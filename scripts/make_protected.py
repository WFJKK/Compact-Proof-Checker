#!/usr/bin/env python3
"""Write the protected target of the open lane: Lean modules with one network's graph, exact weights and
task as constants, and the statement a candidate has to prove.

    python3 scripts/make_protected.py <network.json> <claimed count> <out dir> [<certificate.json> [<plan.json>]]

reads a network file written by scripts/export_network.py and writes into <out dir>/Protected/:

    Protected.N_<network>_c<claimed>[_h...][_p...]   -- the claim: what a candidate proves
        def graph : Graph := ...                the exported graph, operation by operation
        def weights : Weights ℚ := ...          every weight, as dyadic rationals
        def task : Task := maxTask 2 8          the task named in the file, as parseNetwork builds it
        def cert : Cert := #[...]               the certificate of a scored submission (empty otherwise)
        def plan : List Nat := [...]            the plan of a planned checker (only with a plan)
        def claimedCount : Nat := <claimed count>
        def Target : Prop := claimedCount ≤ numCorrect graph weights task

and, since 17 November 2026, the same constants once more in modules that do not change with the claim:

    Protected.N_<network>                    -- the network: graph, weights, task, written as above
    Protected.N_<network>_h<16 hex digits>   -- a nonempty certificate, named by its content: cert
    Protected.N_<network>_p<16 hex digits>   -- the plan of a planned checker, named by its content: plan

The claim's module is the one protected module there was before, with the same text, so a candidate written
against it compiles and is checked as it was. The others are for a candidate's modules that do not depend on
the claim: a checker, its soundness proof and the kernel's facts about the weights can import the network's
module alone, and then raising the claimed count, or changing the certificate or the plan, renames the claim's
module and nothing they import, so they are neither edited nor compiled again. (In run attn-min2-ptl-3 raising
the claim meant editing and recompiling every module, about 20 compiles.) `Protected.N_<network>.weights` and
the claim's `weights` are two constants with the same definition, term for term, so a fact about one is a fact
about the other: Lean and the kernel see it by unfolding both (`exact`, `rfl`, `show`).

A certificate is a JSON list of numbers: integers, or [p, q] for p/q (q > 0), or floats, which the
service turns into exact [p, q] pairs. Its canonical form (integers and pairs only) is hashed into the
names, so a candidate with a certificate gets modules of its own. A plan is a JSON list of natural
numbers for a planned checker (`D : List Nat → Checker`); a submission with a plan, even an empty one, gets the
constant `plan` and `_p<16 hex digits>` of the plan in its claim module's name, and one without keeps the
name it has always had.

The claim's module is part of the trusted base of an open-lane result, as scripts/export_network.py is: a
candidate proves `Target`, and `Target` means what it should only if the module's constants are the network.
The acceptance service checks that they are: `acceptcheck protected <network.json> <claim module>` parses the
file with the checker's own reader (parseNetwork in Json.lean) and compares graph, weights and task with the
claim module's constants. The other modules are not trusted and need not be: every statement the service
checks is written with the claim module's constants, and a fact about another module's constant counts only
where the kernel finds the two equal. The names are derived from the network id, the claimed count and the
contents, so a different network, claim, certificate or plan always gets a different module.

Prints the claim module's name.
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


def network_module_name(network_id: str) -> str:
    """`max2-v64-s0` becomes `N_max2_v64_s0`: the module of the network alone (graph, weights, task)."""
    return "N_" + re.sub(r"[^A-Za-z0-9]", "_", network_id)


def cert_module_name(network_id: str, cert: list) -> str | None:
    """The module of a nonempty certificate, named by its content; None for an empty one (no module)."""
    return network_module_name(network_id) + "_h" + cert_digest(cert) if cert else None


def plan_module_name(network_id: str, plan: list | None) -> str | None:
    """The module of a plan (even an empty one), named by its content; None without a plan."""
    return None if plan is None else network_module_name(network_id) + "_p" + plan_digest(plan)


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


def render_all(net: dict, claimed: int, cert: list | None = None, plan: list | None = None) -> list[tuple[str, str]]:
    """[(module name, Lean source)]: the network's module, the certificate's (when nonempty), the plan's (with a
    plan), and last the claim's. Each is self-contained; the claim's module defines its constants with the very
    text the others define theirs with, so the terms are the same."""
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
    nid = net["network"]
    name = module_name(nid, claimed, cert, plan)
    net_name, cert_name, plan_name = network_module_name(nid), cert_module_name(nid, cert), plan_module_name(nid, plan)
    note = "Written by scripts/make_protected.py. Not to be edited: the acceptance service generates it."

    # the definitions, each written once and used in the claim's module and in the module of its own. A long
    # weight tensor or plan needs more than Lean's default recursion depth (512): without the option below the
    # protected module of a network of width 32 (tensors of 2,048 entries) did not compile, so such a network
    # could not be proved about at all
    ops = ",\n    ".join(lean_op(n) for n in g["nodes"])
    weights, longest = [], 0
    for w in net["weights"]:
        ints = w["ints"]
        longest = max(longest, len(ints))
        if len(ints) == 0:
            data = "#[]"
        else:
            data = "#[" + ", ".join(f"dyadic {lean_int(m)} {lean_int(w['exp'])}" for m in ints) + "]"
        shape = "[" + ", ".join(str(d) for d in w["shape"]) + "]"
        weights.append(f"({lean_str(w['name'])}, ({{ shape := {shape}, data := {data} }} : Tensor ℚ))")
    weights_src = ",\n    ".join(weights) if weights else ""
    # measured on attn-min2-v64-s0 (tensors of 2,048 entries), compiled as the service compiles, with
    # -DElab.async=false: 36,864 is too little, 50,000 enough
    # and with tensors of 4,096 entries (attn-min2-v128-s0) Lean's compiler ran out of its default heartbeats on
    # the definition; the service limits a compile's time itself
    wdepth = "" if longest < 400 else f"set_option maxRecDepth {64 * longest + 4096} in\nset_option maxHeartbeats 0 in\n"
    network_src = f"""/-- The network's graph, operation by operation, as the file gives it. -/
def graph : Graph := {{
  positions := {g["positions"]}
  values := {g["values"]}
  nodes := [
    {ops}]
  output := {g["output"]} }}

{wdepth}/-- The network's weights, every entry an exact dyadic rational. -/
def weights : Weights ℚ := [
    {weights_src}]

/-- The task, as `taskByName` builds it for this input shape. -/
def task : Task := {lean_task(net["task"], g["positions"], g["values"])}
"""
    cert_src = f"""/-- The certificate of a scored submission, as the manifest gives it ({len(cert)} numbers); a checker reads
    it through `CostM.cert`. -/
def cert : Cert := #[{", ".join(lean_rat(v) for v in cert)}]
"""
    pdepth = "" if plan is None or len(plan) < 400 else f"set_option maxRecDepth {4 * len(plan) + 4096} in\n"
    plan_src = "" if plan is None else (
        "{}/-- The plan of a planned checker, as the manifest gives it ({} numbers). Only the instance runs the\n"
        "    checker on it: the soundness theorem holds for every plan. -/\n"
        "def plan : List Nat := [{}]\n").format(pdepth, len(plan), ", ".join(str(v) for v in plan))
    imports = "import CompactCheck.Json\nimport CompactCheck.Spec\nimport CompactCheck.Counted\n"
    out = [(net_name, f"""{imports}
/-!
# Protected network `{nid}`

{note}
The graph, the weights and the task as the module of a claim on this network defines them, in a module that
does not change with the claimed count, the certificate or the plan: facts about the weights import it alone.
-/

namespace Protected.{net_name}

open CompactCheck

{network_src}
end Protected.{net_name}
""")]
    if cert_name:
        out.append((cert_name, f"""{imports}
/-! # Protected certificate of {len(cert)} numbers, for network `{nid}`

{note} The certificate as the module of a claim with it defines it. -/

namespace Protected.{cert_name}

open CompactCheck

{cert_src}
end Protected.{cert_name}
"""))
    if plan_name:
        out.append((plan_name, f"""/-! # Protected plan of {len(plan)} numbers, for network `{nid}`

{note} The plan as the module of a claim with it defines it. -/

namespace Protected.{plan_name}

{plan_src}
end Protected.{plan_name}
"""))
    out.append((name, f"""{imports}
/-!
# Protected target: network `{nid}`, claimed count {claimed}{", certificate of " + str(len(cert)) + " numbers" if cert else ""}{"" if plan is None else ", plan of " + str(len(plan)) + " numbers"}

Written by scripts/make_protected.py from a network file of scripts/export_network.py. Not to be edited:
the acceptance service generates it, and checks its constants against the file with the checker's reader.
-/

namespace Protected.{name}

open CompactCheck

{network_src}
{cert_src}{"" if plan is None else chr(10) + plan_src}
/-- The number of inputs the candidate claims the network answers correctly. -/
def claimedCount : Nat := {claimed}

/-- What a candidate has to prove: the network answers at least `claimedCount` of its
    {domain} inputs correctly, in the sense of `Spec.lean`. -/
def Target : Prop := claimedCount ≤ numCorrect graph weights task

end Protected.{name}
"""))
    return out


def render(net: dict, claimed: int, cert: list | None = None, plan: list | None = None) -> tuple[str, str]:
    """(module name, Lean source) of the claim's module (render_all)."""
    return render_all(net, claimed, cert, plan)[-1]


def main() -> None:
    if len(sys.argv) not in (4, 5, 6):
        sys.exit(__doc__)
    net = json.loads(Path(sys.argv[1]).read_text())
    cert = json.loads(Path(sys.argv[4]).read_text()) if len(sys.argv) >= 5 else []
    plan = json.loads(Path(sys.argv[5]).read_text()) if len(sys.argv) == 6 else None
    out = Path(sys.argv[3]) / "Protected"
    out.mkdir(parents=True, exist_ok=True)
    for name, src in render_all(net, int(sys.argv[2]), cert, plan):
        (out / f"{name}.lean").write_text(src)
    print(name)


if __name__ == "__main__":
    main()
