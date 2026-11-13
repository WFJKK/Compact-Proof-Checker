#!/usr/bin/env python3
"""Write the protected target of the open lane: a Lean module with one network's graph, exact weights and
task as constants, and the statement a candidate has to prove.

    python3 scripts/make_protected.py <network.json> <claimed count> <out dir> [<certificate.json> [<plan.json>]]

reads a network file written by scripts/export_network.py and writes <out dir>/Protected/<module>.lean, the module named after the network and the claimed count:

    namespace Protected.<module>
    def graph : Graph := ...          -- the exported graph, operation by operation
    def weights : Weights ℚ := ...    -- every weight, as dyadic rationals
    def task : Task := maxTask 2 8    -- the task named in the file, as parseNetwork builds it
    def cert : Cert := #[...]         -- the certificate of a scored submission (empty otherwise)
    def plan : List Nat := [...]      -- the plan of a planned checker (only when the submission has one)
    def claimedCount : Nat := <claimed count>
    def Target : Prop := claimedCount ≤ numCorrect graph weights task

A certificate is a JSON list of numbers: integers, or [p, q] for p/q (q > 0), or floats, which the
service turns into exact [p, q] pairs. Its canonical form (integers and pairs only) is hashed into the
module name, so a candidate with a certificate gets a module of its own. A plan is a JSON list of natural
numbers for a planned checker (`D : List Nat → Checker`); a submission with a plan, even an empty one, gets the
constant `plan` and `_p<16 hex digits>` of the plan in its module name, and one without keeps the module it has
always had.

The module is part of the trusted base of an open-lane result, as scripts/export_network.py is: a candidate
proves `Target`, and `Target` means what it should only if these constants are the network. The acceptance
service checks that they are: `acceptcheck protected <network.json> <module>` parses the file with the
checker's own reader (parseNetwork in Json.lean) and compares graph and weights with the constants. The module
name is derived from the network id and the claimed count, so a different network or claim always gets a
different module.

Prints the module name.
"""

from __future__ import annotations

import hashlib
import json
import math
import re
import sys
from pathlib import Path


class ProtectedError(ValueError):
    pass


def module_name(network_id: str, claimed: int, cert: list | None = None, plan: list | None = None) -> str:
    """`max2-v64-s0` with claimed count 63 becomes `N_max2_v64_s0_c63`: a Lean identifier that starts with a
    letter, different for every network and claimed count. A nonempty certificate adds `_h<16 hex digits>`
    of its canonical form, a plan (even an empty one) `_p<16 hex digits>` of its own."""
    name = "N_" + re.sub(r"[^A-Za-z0-9]", "_", network_id) + f"_c{claimed}"
    if cert:
        name += "_h" + cert_digest(cert)
    if plan is not None:
        name += "_p" + plan_digest(plan)
    return name


def canonical_plan(plan) -> list:
    """A list of natural numbers, as it is; anything else is an error. Its size is the service's to bound."""
    if not isinstance(plan, list):
        raise ProtectedError("the plan must be a JSON list of natural numbers")
    for i, v in enumerate(plan):
        if isinstance(v, bool) or not isinstance(v, int) or v < 0:
            raise ProtectedError(f"plan entry {i} must be a natural number, not {v!r}")
    return list(plan)


def plan_digest(plan: list) -> str:
    return hashlib.sha256(json.dumps(canonical_plan(plan), separators=(",", ":")).encode()).hexdigest()[:16]


def canonical_cert(cert) -> list:
    """Integers stay; floats become exact [p, q] pairs; [p, q] pairs are reduced; anything else is an error."""
    if not isinstance(cert, list):
        raise ProtectedError("the certificate must be a JSON list of numbers")
    out = []
    for i, v in enumerate(cert):
        if isinstance(v, bool):
            raise ProtectedError(f"certificate entry {i} is a boolean")
        if isinstance(v, int):
            out.append(v)
        elif isinstance(v, float):
            if v != v or v in (float("inf"), float("-inf")):
                raise ProtectedError(f"certificate entry {i} is not finite")
            p, q = v.as_integer_ratio()
            out.append(p if q == 1 else [p, q])
        elif isinstance(v, list) and len(v) == 2 and all(isinstance(x, int) and not isinstance(x, bool) for x in v):
            p, q = v
            if q <= 0:
                raise ProtectedError(f"certificate entry {i} has a denominator that is not positive")
            g = math.gcd(p, q)
            p, q = p // g, q // g
            out.append(p if q == 1 else [p, q])
        else:
            raise ProtectedError(f"certificate entry {i} must be an integer, a float or a pair [p, q]")
    return out


def cert_digest(cert: list) -> str:
    return hashlib.sha256(json.dumps(canonical_cert(cert), separators=(",", ":")).encode()).hexdigest()[:16]


def lean_rat(v) -> str:
    if isinstance(v, int):
        return f"({v} : Rat)"
    p, q = v
    return f"(mkRat {lean_int(p)} {q})"


def lean_int(v: int) -> str:
    return f"({v} : Int)" if v < 0 else f"{v}"


def lean_str(s: str) -> str:
    return json.dumps(s)  # Lean string literals read the JSON escapes used here


def lean_op(node: dict) -> str:
    op = node["op"]
    if op == "input":
        return "Op.input"
    if op == "linear":
        bias = "none" if node.get("bias") is None else f"(some {lean_str(node['bias'])})"
        return f"Op.linear {node['arg']} {lean_str(node['weight'])} {bias}"
    if op == "sum":
        return f"Op.sum {node['arg']} {lean_int(node['dim'])}"
    if op == "add":
        return f"Op.add {node['left']} {node['right']}"
    if op == "param":
        return f"Op.param {lean_str(node['weight'])}"
    if op == "binary":
        return f"Op.binary BinOp.{node['fn']} {node['left']} {node['right']}"
    if op == "neg":
        return f"Op.neg {node['arg']}"
    if op == "matmul":
        return f"Op.matmul {node['left']} {node['right']}"
    if op == "index":
        items = []
        for it in node["items"]:
            if it == "all":
                items.append("IndexItem.all")
            elif "one" in it:
                items.append(f"IndexItem.one {it['one']}")
            else:
                a, b = it["range"]
                items.append(f"IndexItem.range {a} {b}")
        return f"Op.index {node['arg']} [{', '.join(items)}]"
    if op == "transpose":
        return f"Op.transpose {node['arg']}"
    if op == "unsqueeze":
        return f"Op.unsqueeze {node['arg']} {lean_int(node['dim'])}"
    if op == "expand":
        return f"Op.expand {node['arg']} [{', '.join(lean_int(d) for d in node['shape'])}]"
    if op == "cat":
        return f"Op.cat [{', '.join(str(a) for a in node['args'])}] {lean_int(node['dim'])}"
    if op == "stack":
        return f"Op.stack [{', '.join(str(a) for a in node['args'])}] {lean_int(node['dim'])}"
    if op == "exp":
        return f"Op.exp {node['arg']}"
    if op == "softmax":
        return f"Op.softmax {node['arg']} {lean_int(node['dim'])}"
    if op == "zeros_like":
        return f"Op.zerosLike {node['arg']}"
    raise ProtectedError(f"operation {op} is not supported by the Lean checker")


def lean_task(name: str, positions: int, values: int) -> str:
    """As `taskByName` in Task.lean builds the task."""
    if name == "max":
        return f"maxTask {positions} {values}"
    if name == "min":
        return f"minTask {positions} {values}"
    if name == "majority":
        if values != 2:
            raise ProtectedError("majority needs two token values")
        return f"majorityTask {positions}"
    raise ProtectedError(f"unknown task {name}")


def render(net: dict, claimed: int, cert: list | None = None, plan: list | None = None) -> tuple[str, str]:
    """(module name, Lean source)."""
    if net.get("format") != "compactcheck-network-v1":
        raise ProtectedError(f"not a network file: format {net.get('format')!r}")
    cert = canonical_cert(cert or [])
    plan = None if plan is None else canonical_plan(plan)
    g = net["graph"]
    space = [g["values"]] * g["positions"]
    domain = 1
    for v in space:
        domain *= v
    if not isinstance(claimed, int) or isinstance(claimed, bool) or claimed < 0 or claimed > domain:
        raise ProtectedError(f"the claimed count must be an integer from 0 to {domain}, not {claimed!r}")
    name = module_name(net["network"], claimed, cert, plan)
    # a list literal elaborates as nested applications, one level per entry: a long plan needs more than the
    # default recursion depth (512), as a long weight tensor does
    depth = "" if plan is None or len(plan) < 400 else f"set_option maxRecDepth {4 * len(plan) + 4096} in\n"
    plan_src = "" if plan is None else (
        "\n{}/-- The plan of a planned checker, as the manifest gives it ({} numbers). Only the instance runs the\n"
        "    checker on it: the soundness theorem holds for every plan. -/\n"
        "def plan : List Nat := [{}]\n").format(depth, len(plan), ", ".join(str(v) for v in plan))
    ops = ",\n    ".join(lean_op(n) for n in g["nodes"])
    cert_src = "#[" + ", ".join(lean_rat(v) for v in cert) + "]"
    weights = []
    for w in net["weights"]:
        ints = w["ints"]
        if len(ints) == 0:
            data = "#[]"
        else:
            data = "#[" + ", ".join(f"dyadic {lean_int(m)} {lean_int(w['exp'])}" for m in ints) + "]"
        shape = "[" + ", ".join(str(d) for d in w["shape"]) + "]"
        weights.append(f"({lean_str(w['name'])}, ({{ shape := {shape}, data := {data} }} : Tensor ℚ))")
    weights_src = ",\n    ".join(weights) if weights else ""
    src = f"""import CompactCheck.Json
import CompactCheck.Spec
import CompactCheck.Counted

/-!
# Protected target: network `{net["network"]}`, claimed count {claimed}{", certificate of " + str(len(cert)) + " numbers" if cert else ""}{"" if plan is None else ", plan of " + str(len(plan)) + " numbers"}

Written by scripts/make_protected.py from a network file of scripts/export_network.py. Not to be edited:
the acceptance service generates it, and checks its constants against the file with the checker's reader.
-/

namespace Protected.{name}

open CompactCheck

/-- The network's graph, operation by operation, as the file gives it. -/
def graph : Graph := {{
  positions := {g["positions"]}
  values := {g["values"]}
  nodes := [
    {ops}]
  output := {g["output"]} }}

/-- The network's weights, every entry an exact dyadic rational. -/
def weights : Weights ℚ := [
    {weights_src}]

/-- The task, as `taskByName` builds it for this input shape. -/
def task : Task := {lean_task(net["task"], g["positions"], g["values"])}

/-- The certificate of a scored submission, as the manifest gives it ({len(cert)} numbers); a checker reads
    it through `CostM.cert`. -/
def cert : Cert := {cert_src}
{plan_src}
/-- The number of inputs the candidate claims the network answers correctly. -/
def claimedCount : Nat := {claimed}

/-- What a candidate has to prove: the network answers at least `claimedCount` of its
    {domain} inputs correctly, in the sense of `Spec.lean`. -/
def Target : Prop := claimedCount ≤ numCorrect graph weights task

end Protected.{name}
"""
    return name, src


def main() -> None:
    if len(sys.argv) not in (4, 5, 6):
        sys.exit(__doc__)
    net = json.loads(Path(sys.argv[1]).read_text())
    cert = json.loads(Path(sys.argv[4]).read_text()) if len(sys.argv) >= 5 else []
    plan = json.loads(Path(sys.argv[5]).read_text()) if len(sys.argv) == 6 else None
    name, src = render(net, int(sys.argv[2]), cert, plan)
    out = Path(sys.argv[3]) / "Protected"
    out.mkdir(parents=True, exist_ok=True)
    (out / f"{name}.lean").write_text(src)
    print(name)


if __name__ == "__main__":
    main()
