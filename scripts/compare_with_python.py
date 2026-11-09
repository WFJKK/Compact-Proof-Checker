#!/usr/bin/env python3
"""Compare the Lean checker with the Python pipeline on every development network of a model.

For each network (held-out networks are skipped: their weights are for the
final evaluation only):

1. Logits: Lean's exact logits on random inputs must equal the Python
   checker's exact logits (core.check.evaluate), fraction for fraction, and
   agree with PyTorch's float forward pass to float precision.
2. Brute force: Lean's count of correctly answered inputs and its per-input
   mask must equal the zoo's (manifest real_correct and <id>.correct.npy).
3. Proofs: proof files with single, skip and interval leaves must certify
   the same number in Lean as in the Python checker: brute force, a proof
   that skips half the inputs, interval leaves grouped by the larger token
   (two positions only), and random split trees.
4. Contract: if the network has a chain of linear maps (max2 has three),
   the same proofs with the whole chain contracted, in one step and in two,
   and a list of malformed contractions that both checkers must reject.
5. The model's baselines (`models/<name>/baselines/*.md`), the proofs the
   pipeline's runs start from, at two knob values; with and without the
   symmetry rule; and, for a baseline with a contraction and interval
   leaves, its interval leaves with approximations of the contracted map in
   all three forms (dense, low rank, row segments), and malformed
   approximations both checkers must reject.

Usage, from the Lean project folder, after `lake build compactcheck`:

    python3 scripts/compare_with_python.py <repo> <model folder> [--inputs N] [--random N] [--only ID]

Exits with status 1 if anything disagrees.
"""

from __future__ import annotations

import argparse
import copy
import json
import random
import re
import subprocess
import sys
import tempfile
from fractions import Fraction
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import export_network  # noqa: E402

LEAN = HERE.parent / ".lake" / "build" / "bin" / "compactcheck"


def lean(*args: str) -> dict | list:
    out = subprocess.run([str(LEAN), *args], capture_output=True, text=True, check=True).stdout
    return json.loads(out.strip().splitlines()[-1])


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("repo", type=Path)
    ap.add_argument("model")
    ap.add_argument("--inputs", type=int, default=200, help="random inputs for the logit comparison")
    ap.add_argument("--random", type=int, default=4, help="random split trees per network")
    ap.add_argument("--only", default="", help="only networks whose id contains this")
    args = ap.parse_args()
    repo = args.repo.resolve()
    sys.path.insert(0, str(repo))
    sys.path.insert(0, str(repo / "core"))  # the baseline recipes import helpers

    import torch
    from core.check.checker import check_proof
    from core.check.cost import Counter
    from core.check.evaluate import Program
    from core.check.proof import full_tree
    from core.check.trace import build_graph
    from core.model_folder import load_model_folder
    from core.zoo import load_weights, read_manifest

    folder = load_model_folder(repo / args.model)
    rng = np.random.default_rng(0)
    failures = 0
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        for entry in read_manifest(folder)["networks"]:
            if entry["split"] != "dev" or args.only not in entry["id"]:
                continue
            nid, setting = entry["id"], entry["setting"]
            space = folder.input_space(setting)
            exported = export_network.export(repo, args.model, nid)
            net = tmp / f"{nid}.json"
            net.write_text(json.dumps(exported))
            problems = []

            # 1. logits
            tokens = np.stack([rng.integers(0, v, size=args.inputs) for v in space], axis=1)
            (tmp / "inputs.json").write_text(json.dumps(tokens.tolist()))
            lean_logits = [[Fraction(s) for s in row] for row in lean("logits", str(net), str(tmp / "inputs.json"))]
            weights = load_weights(folder, nid)
            module = folder.build(setting)
            graph = build_graph(module)
            prog = Program(graph, weights, Counter())
            exact = prog._run_concrete(tokens, Counter()).to_fractions()
            if [list(r) for r in exact] != lean_logits:
                problems.append("exact logits differ from the Python checker's")
            module.load_state_dict({k: torch.tensor(v) for k, v in weights.items()})
            with torch.no_grad():
                ref = module(torch.as_tensor(folder.encode(tokens, setting)).float()).double().numpy()
            lean_float = np.array([[float(f) for f in row] for row in lean_logits])
            err = float(np.abs(lean_float - ref).max() / max(1.0, np.abs(ref).max()))
            if err > 1e-5:
                problems.append(f"logits differ from PyTorch's by {err:.1e}")

            # 2. brute force
            brute = lean("brute", str(net))
            mask = np.array([c == "1" for c in brute["mask"]])
            ref_mask = np.load(folder.zoo_dir() / entry["correct"]).reshape(-1)
            if brute["correct"] != entry["real_correct"] or not np.array_equal(mask, ref_mask):
                problems.append(f"brute force: Lean {brute['correct']}, zoo {entry['real_correct']}")

            # 3. proofs, checked by both checkers
            trees = proof_trees(space, random.Random(sum(map(ord, nid))), args.random)
            trees["brute force"] = full_tree(space)
            half = space[0] // 2
            trees["skip half"] = {"split": {"position": 0, "cuts": [half]},
                                  "children": [{"leaf": "skip"}, _full_tree_from(space, 0, half)]}
            certified = {}
            for name, tree in trees.items():
                proof = {"schema": "split-tree-v1", "network": nid, "tree": tree}
                py = check_proof(proof, folder, nid)
                (tmp / "proof.json").write_text(json.dumps(proof))
                ln = lean(str(net), str(tmp / "proof.json"))
                certified[name] = ln.get("certified")
                if py["status"] != "ok" or py["certified"] != ln.get("certified"):
                    problems.append(f"{name}: Python {py['status']} {py['certified']}, Lean {ln}")

            # 4. the same proofs with contractions, and malformed contractions
            chain = linear_chain(graph)
            contracted = {}
            if chain:
                variants = {"contracted": [{"name": "contracted", "chain": chain}]}
                if len(chain) >= 3:
                    variants["contracted in two steps"] = [
                        {"name": "first", "chain": chain[:2]},
                        {"name": "contracted", "chain": ["first"] + chain[2:]}]
                for vname, contract in variants.items():
                    for name, tree in trees.items():
                        if name == "brute force":
                            continue
                        proof = {"schema": "split-tree-v1", "network": nid, "contract": contract, "tree": tree}
                        py, ln = check_both(check_proof, folder, nid, net, tmp, proof)
                        contracted[f"{name}, {vname}"] = ln.get("certified")
                        if py["status"] != "ok" or py["certified"] != ln.get("certified"):
                            problems.append(f"{name}, {vname}: Python {py['status']} {py['certified']}, Lean {ln}")
                for bname, contract in malformed_contractions(chain).items():
                    proof = {"schema": "split-tree-v1", "network": nid, "contract": contract,
                             "tree": {"leaf": "skip"}}
                    py, ln = check_both(check_proof, folder, nid, net, tmp, proof)
                    if py["status"] != "rejected" or ln.get("status") != "rejected":
                        problems.append(f"malformed contraction ({bname}): Python {py['status']}, Lean {ln}")

            # 5. the baselines, symmetry and approximations
            n_baseline = 0
            for rname, make_proof in baselines(repo / args.model).items():
                seen = []
                for knob in (1.0, 0.5):
                    proof = make_proof(weights, {"input_space": space}, knob)
                    if proof in seen:
                        continue
                    seen.append(proof)
                    cases = {f"{rname}, knob {knob}": (proof, None)}
                    if knob == 1.0 and proof.get("symmetry"):
                        cases[f"{rname} without symmetry"] = ({**proof, "symmetry": False}, None)
                    name = (proof.get("contract") or [{}])[-1].get("name")
                    if knob == 1.0 and name and has_interval(proof["tree"]):
                        p0 = Program(graph, weights, Counter())
                        for c in proof["contract"]:
                            p0.contract(c["name"], c["chain"], Counter())
                        W = p0.linear(name).W.to_fractions()
                        for aname, form in approximations(W).items():
                            cases[f"{rname}, approximation {aname}"] = (
                                {**proof, "approximate": [{"name": "P", "of": name, **form}],
                                 "tree": with_approx(proof["tree"], "P")}, None)
                        for bname, spec in malformed_approximations(W, name).items():
                            cases[f"{rname}, malformed approximation ({bname})"] = (
                                {**proof, "approximate": spec, "tree": with_approx(proof["tree"], "P")},
                                "rejected")
                    for cname, (body, expect) in cases.items():
                        body = {k: v for k, v in body.items() if k != "notes"}
                        body = {**body, "schema": "split-tree-v1", "network": nid}
                        py, ln = check_both(check_proof, folder, nid, net, tmp, body)
                        n_baseline += 1
                        if (py["status"] != ln.get("status", "ok") or py["certified"] != ln.get("certified")
                                or (expect and py["status"] != expect)):
                            problems.append(f"{cname}: Python {py['status']} {py['certified']}, Lean {ln}")

            if COST_MISMATCHES:
                problems.append(f"{len(COST_MISMATCHES)} bills differ from the Python length: " + "; ".join(COST_MISMATCHES[:3]))
                COST_MISMATCHES.clear()
            status = "ok" if not problems else "DIFFERS: " + "; ".join(problems)
            by_larger = certified.get("intervals by larger token")
            by_larger_c = contracted.get("intervals by larger token, contracted")
            print(f"{nid}: logits max rel. diff to PyTorch {err:.1e}, brute force {brute['correct']}/{entry['n_inputs']}, "
                  f"{len(trees)} proofs" + (f" and {len(contracted)} contracted" if contracted else "")
                  + (f" and {n_baseline} from the baselines" if n_baseline else "")
                  + (f" (intervals by larger token: {by_larger}" if by_larger is not None else "")
                  + (f", contracted {by_larger_c})" if by_larger_c is not None else (")" if by_larger is not None else ""))
                  + f", {status}", flush=True)
            failures += bool(problems)
    print(f"bills compared with the Python length: {COST_COMPARED}", flush=True)
    sys.exit(1 if failures else 0)


COST_MISMATCHES: list[str] = []
COST_COMPARED = 0


def check_both(check_proof, folder, nid: str, net: Path, tmp: Path, proof: dict) -> tuple[dict, dict]:
    """The Python checker's result and the Lean checker's last line, for one proof. When both accept the
    proof, `compactcheck cost` is run too and its bill compared with the Python length, category by category
    (the reproduction of cost-v4, CountedCheck.lean); a difference is recorded in COST_MISMATCHES."""
    global COST_COMPARED
    py = check_proof(proof, folder, nid)
    (tmp / "proof.json").write_text(json.dumps(proof))
    ln = lean(str(net), str(tmp / "proof.json"))
    if py["status"] == "ok" and ln.get("status", "ok") == "ok":
        cost = lean("cost", str(net), str(tmp / "proof.json"))
        COST_COMPARED += 1
        by_py = {k: v for k, v in (py.get("length_by_rule") or {}).items() if v}
        by_lean = {k: v for k, v in (cost.get("by_category") or {}).items() if v}
        if cost.get("status", "ok") != "ok" or cost.get("length") != py["length"] or by_py != by_lean:
            COST_MISMATCHES.append(f"{nid}: Python {py['length']} {by_py}, Lean {cost}")
    return py, ln


# Proof trees -----------------------------------------------------------------


def _split(position: int, cuts: list[int], children: list[dict]) -> dict:
    return {"split": {"position": position, "cuts": cuts}, "children": children}


def _full_tree_from(space: list[int], position: int, lo: int) -> dict:
    """Split every position into single tokens, where `position` starts at lo instead of 0."""

    def build(k: int) -> dict:
        if k == len(space):
            return {"leaf": "single"}
        start = lo if k == position else 0
        cuts = list(range(start + 1, space[k]))
        children = [build(k + 1) for _ in range(space[k] - start)]
        if not cuts:
            return children[0]
        return _split(k, cuts, children)

    return build(0)


def _singles(ranges: list[tuple[int, int]], k: int) -> dict:
    """Split positions k, k + 1, ... of the box into single tokens, with single leaves."""
    if k == len(ranges):
        return {"leaf": "single"}
    lo, hi = ranges[k]
    if lo == hi:
        return _singles(ranges, k + 1)
    children = []
    for t in range(lo, hi + 1):
        r = list(ranges)
        r[k] = (t, t)
        children.append(_singles(r, k + 1))
    return _split(k, list(range(lo + 1, hi + 1)), children)


def by_larger_token(space: list[int], chunk: int | None = None) -> dict:
    """Two positions. For each first token t: the second token in [0, t] as
    interval leaves (label t), in pieces of `chunk` tokens if given, and the
    second token above t as single leaves."""
    V = space[1]
    rows = []
    for t in range(space[0]):
        if chunk is None or t + 1 <= chunk:
            low = {"leaf": "interval"}
        else:
            cuts = list(range(chunk, t + 1, chunk))
            low = _split(1, cuts, [{"leaf": "interval"} for _ in range(len(cuts) + 1)])
        if t == V - 1:
            rows.append(low)
        else:
            rows.append(_split(1, [t + 1], [low, _singles([(t, t), (t + 1, V - 1)], 1)]))
    return _split(0, list(range(1, space[0])), rows)


def random_tree(space: list[int], rng: random.Random, max_depth: int, p_leaf: float = 0.3) -> dict:
    """A random valid split tree. Leaves are mostly interval leaves (some
    with a constant label, some not), single leaves on single inputs, and
    skip leaves."""

    def build(ranges: list[tuple[int, int]], depth: int) -> dict:
        splittable = [k for k, (lo, hi) in enumerate(ranges) if hi > lo]
        if not splittable or depth >= max_depth or rng.random() < p_leaf:
            if all(lo == hi for lo, hi in ranges):
                return {"leaf": rng.choice(["single", "single", "interval", "skip"])}
            return {"leaf": rng.choice(["interval", "interval", "interval", "skip"])}
        k = rng.choice(splittable)
        lo, hi = ranges[k]
        cuts = sorted(rng.sample(range(lo + 1, hi + 1), rng.randint(1, min(3, hi - lo))))
        bounds = [lo] + cuts + [hi + 1]
        children = []
        for a, b in zip(bounds, bounds[1:]):
            r = list(ranges)
            r[k] = (a, b - 1)
            children.append(build(r, depth + 1))
        return _split(k, cuts, children)

    return build([(0, v - 1) for v in space], 0)


def proof_trees(space: list[int], rng: random.Random, n_random: int) -> dict[str, dict]:
    trees = {}
    if len(space) == 2:
        trees["intervals by larger token"] = by_larger_token(space)
        trees["intervals in pieces of 4"] = by_larger_token(space, chunk=4)
    for i in range(n_random):
        trees[f"random tree {i}"] = random_tree(space, rng, max_depth=rng.choice([2, 4, 6]))
    return trees


# Contraction -------------------------------------------------------------------


def linear_chain(graph) -> list[str] | None:
    """The names of the linear maps, if the network is the input, a sum over
    the positions, and then a chain of linear maps ending at the output."""
    nodes = graph.nodes
    if len(nodes) < 4 or [n.op for n in nodes[:2]] != ["input", "sum"] or nodes[1].dim not in (1, -2):
        return None
    lins = nodes[2:]
    for prev, n in zip(nodes[1:], lins):
        if n.op != "linear" or list(n.args) != [prev.name]:
            return None
    if graph.output != lins[-1].name:
        return None
    return [n.name for n in lins]


def malformed_contractions(chain: list[str]) -> dict[str, list]:
    """Contractions both checkers must reject."""
    a, b = chain[0], chain[1]
    bad = {"not consecutive": [{"name": "M", "chain": [a, chain[-1]]}]} if len(chain) >= 3 else {}
    return {
        **bad,
        "one map": [{"name": "M", "chain": [a]}],
        "wrong order": [{"name": "M", "chain": [b, a]}],
        "repeated map": [{"name": "M", "chain": [a, a]}],
        "name taken": [{"name": b, "chain": [a, b]}],
        "unknown map": [{"name": "M", "chain": [a, "no such map"]}],
        "map contracted away": [{"name": "M", "chain": [a, b]}, {"name": "N", "chain": [b] + chain[2:3]}],
        "extra key": [{"name": "M", "chain": [a, b], "x": 1}],
    }


# Baselines, symmetry and approximations ---------------------------------------------


def baselines(model: Path) -> dict:
    """The model's baseline recipes: `make_proof(weights, info, knob)` from the Python block of
    each baselines/*.md file. The recipes import the pipeline's `helpers`."""
    out = {}
    for path in sorted((model / "baselines").glob("*.md")):
        found = re.search(r"```python\n(.*?)```", path.read_text(), re.S)
        if found:
            ns: dict = {}
            exec(found.group(1), ns)
            if "make_proof" in ns:
                out[path.stem] = ns["make_proof"]
    return out


def has_interval(tree: dict) -> bool:
    if "leaf" in tree:
        return tree["leaf"] == "interval"
    return any(has_interval(c) for c in tree["children"])


def with_approx(tree: dict, name: str) -> dict:
    """The tree with `"approx": name` on every interval leaf."""
    tree = copy.deepcopy(tree)

    def go(node):
        if "leaf" in node:
            if node["leaf"] == "interval":
                node["approx"] = name
            return
        for c in node["children"]:
            go(c)

    go(tree)
    return tree


def frac(f: Fraction) -> str:
    return f"{f.numerator}/{f.denominator}"


def dec(f: Fraction) -> str:
    """The exact decimal of a dyadic rational."""
    k = f.denominator.bit_length() - 1
    digits = str(abs(f.numerator) * 5**k).rjust(k + 1, "0")
    return ("-" if f < 0 else "") + digits[: len(digits) - k] + ("." + digits[len(digits) - k :] if k else "")


def rounded(x, bits: int) -> Fraction:
    return Fraction(round(Fraction(x) * 2**bits), 2**bits)


def mixed(f: Fraction, i: int):
    """The value in one of the formats a proof file may use, by position."""
    k = i % 5
    if k == 0 and f.denominator == 1:
        return int(f)
    if k <= 1:
        return float(f)  # exact: small dyadic values
    if k == 2:
        return dec(f)
    if k == 3:
        return " " + frac(f) + "\t"
    return ("+" if f >= 0 else "") + dec(f)


def approximations(W: np.ndarray) -> dict[str, dict]:
    """Approximations of an exact matrix (of Fractions) in the three forms."""
    n_out, n_in = W.shape
    out = {"dense, exact": {"form": "dense", "values": [[frac(x) for x in row] for row in W]}}
    for bits in (12, 6):
        out[f"dense, to 2^-{bits}"] = {"form": "dense", "values": [[float(rounded(x, bits)) for x in row] for row in W]}
    out["dense, mixed formats"] = {"form": "dense", "values": [[mixed(rounded(x, 12), i * n_in + j) for j, x in enumerate(row)]
                                                                for i, row in enumerate(W)]}
    U, S, Vt = np.linalg.svd(W.astype(float))
    for r in (1, 4, 16):
        if r <= min(n_out, n_in):
            out[f"low rank {r}"] = {"form": "low_rank",
                                    "left": [[float(rounded(x, 30)) for x in row] for row in U[:, :r] * S[:r]],
                                    "right": [[float(rounded(x, 30)) for x in row] for row in Vt[:r]]}
    for size in (1, 4, 16):
        rows = [[[a, min(n_in, a + size) - 1, dec(rounded((max(W[i, a:a + size]) + min(W[i, a:a + size])) / 2, 20))]
                 for a in range(0, n_in, size)] for i in range(n_out)]
        out[f"row segments of {size}"] = {"form": "row_segments", "rows": rows}
    return out


def malformed_approximations(W: np.ndarray, of: str) -> dict[str, list]:
    """Approximations both checkers must reject."""
    n_out, n_in = W.shape
    vals = [[frac(x) for x in row] for row in W]
    dense = lambda values: [{"name": "P", "of": of, "form": "dense", "values": values}]  # noqa: E731
    seg = lambda rows: [{"name": "P", "of": of, "form": "row_segments", "rows": rows}]  # noqa: E731
    one = [[[0, n_in - 1, "0"]] for _ in range(n_out)]
    return {
        "unknown form": [{"name": "P", "of": of, "form": "sparse", "values": vals}],
        "a row too few": dense(vals[:-1]),
        "a column too few": dense([r[:-1] for r in vals]),
        "a number not dyadic": dense([["1/3"] + vals[0][1:]] + vals[1:]),
        "an exponent in a string": dense([["1e-3"] + vals[0][1:]] + vals[1:]),
        "a boolean": dense([[True] + vals[0][1:]] + vals[1:]),
        "low rank 0": [{"name": "P", "of": of, "form": "low_rank", "left": [[] for _ in range(n_out)], "right": []}],
        "segments with a gap": seg([[[0, 0, 0], [2, n_in - 1, 0]]] + one[1:]),
        "segments past the end": seg([[[0, n_in, 0]]] + one[1:]),
        "of an unknown map": [{"name": "P", "of": "no such map", "form": "dense", "values": vals}],
        "defined twice": dense(vals) * 2,
    }


if __name__ == "__main__":
    main()
