#!/usr/bin/env python3
"""The open lane's acceptance service: takes a candidate's Lean modules, builds them in a box, and asks the
kernel whether they prove the protected target. Writes a receipt.

    python3 scripts/accept.py submit <candidate dir> --repo <pipeline repo> --work <work dir> [--mode M]

The candidate dir holds manifest.json and the modules it names:

    {"schema": "open-lane-candidate-v1", "candidate_id": "...",
     "model": "models/max2", "network": "max2-v64-s0", "claimed_count": 4095,
     "theorem": "Candidate.Cubic.performance", "modules": ["Candidate/Cubic.lean"]}

What happens, in order (every step's outcome is in the receipt):

1. The manifest is checked: types, a claimed count that is a natural number, module paths under Candidate/
   with identifier names, no symbolic links. Module files may import only Candidate.* (among the submitted
   modules), the protected module, CompactCheck.* and Mathlib.*.
2. The network is exported from the pipeline's zoo with scripts/export_network.py (cached by network), and
   the protected module Protected.N_<network>_c<claimed> is written by scripts/make_protected.py and compiled;
   `acceptcheck protected` checks its constants against the network file with the checker's own reader.
3. Each candidate module is compiled with `lean` in a box (Landlock on Linux: no network, reads only the
   toolchain, the Lean project, the workspace and system files, writes only the workspace's out/ and tmp/;
   on macOS with --mode seatbelt, a sandbox-exec profile with the same reads inside the home folder, the
   same writes, no network and no other programs; `process` mode elsewhere, which is weak and is recorded
   as such), under time and memory limits.
4. `acceptcheck check` imports the trusted modules only, replays every constant of the candidate's .olean
   files through the kernel, and asks the kernel to accept `Challenge.proof : Target := <theorem>`.
5. The axioms of the challenge must be among propext, Classical.choice and Quot.sound.

Receipt statuses: accepted, rejected (the candidate is at fault: manifest, compile error, kernel rejection,
axioms), unsupported (the network has an operation the Lean checker does not know), timeout, error
(infrastructure). A certified count is given only with status accepted. Receipts go to <work>/receipts/,
which the box cannot write. The service never trusts a candidate's own build output.

A scored submission (docs/COUNTED.md) adds to its manifest

    "scored": {"checker": "Candidate.X.D", "sound": "Candidate.X.D_sound", "instance": "Candidate.X.D_instance",
               "certificate": [...numbers...], "claimed_bill": 12345}

and, once verified as above, goes through the scored path: the certificate becomes the protected module's
`cert`; `acceptcheck closure` checks that the checker touches numbers only through the counted primitives
(accept/allowlist.txt); `acceptcheck score` has the kernel accept the soundness theorem at the fixed shape and
the instance `CostM.billed D ⟨weights, cert⟩ = some (claimed_count, claimed_bill)`, and measures the general
layer (the checker's description size, kernel time), which the policy budgets below bound. The receipt's `scoring` block says
whether the submission is scored and gives the length in cost-v3 units: the bill, plus `extract` (one per
weight entry) and `read` (one per certificate number). A submission refused scoring stays verified.

A manifest with "kind": "auxiliary" submits a lemma instead of a proof of Target: `theorem` may have any
statement; it is compiled, replayed and axiom-checked the same way (`acceptcheck lemma`), and accepted with
no count and no score (claim_kind auxiliary in the receipt). The receipt's `claim_kind`, `score_eligible`
and `execution_assurance` say what a result is: a scored result's count and bill are both kernel-checked
(`kernel_checked_instance`); nothing of a candidate is ever executed.

    python3 scripts/accept.py protected <network.json> <claimed> --work <work dir> [--certificate c.json]

builds and checks a protected module alone (for tests, and for a candidate's own development).

    python3 scripts/accept.py identity

prints what the service is (the project's commit, the digests every receipt carries: toolchain, trusted
sources, policy; the acceptcheck binary), for a run to record when it starts and check when it resumes.

    python3 scripts/accept.py compile <workspace> Candidate/<Name>.lean --repo R --work W --model M --network N
                              --claimed C [--certificate c.json]

compiles a module of a candidate's workspace in the box against that protected module, for development: the
pipeline's `lean_check` tool is this call. Its output is never evidence.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN_PROJECT = HERE.parent
SCHEMA = "open-lane-candidate-v1"
RECEIPT_SCHEMA = "open-lane-receipt-v1"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
TRUSTED_PREFIXES = ("CompactCheck.", "Mathlib.")
KINDS = ("performance", "auxiliary")  # a proof of Target, or a lemma: accepted with no count and no score
COST_MODEL = "cost-v3"  # the prices (CountedCheck.lean, core/check/cost.py of the pipeline): unchanged since the open lane began
# the open lane's policy around those prices, versioned: what a checker may use for free and the budgets.
# v8 (13 November 2026): List.instDecidableEqNil and List.instDecidableNilEq on the allowlist, the instances Lean
# elaborates `a = []` and `[] = a` to; they match on the list without looking at its elements, as List.isEmpty
# (already allowed) does. Run attn-min2-ptl-1's round-3 checker was refused scoring for the first alone.
# v7 (23 October 2026, evening): the maximum condition adds the fixed rules lane's token_interval rule for general
# networks, `Interp.gtokenIntervals` (a list of leaves per call; the rows that depend on their token alone are
# charged once per call, as cost-v3 charges them once per proof).
# v6 (23 October 2026, afternoon): knowledge conditions, minimal (the base allowlist) and maximum (plus the fixed
# rules lane's interval rule for general networks, `Interp.ginterval`, from allowlist-maximum.txt), chosen by --knowledge
# and part of the policy digest; the closure check counts a primitive projection of a trusted structure as its
# projection function; gsingle charges every operation (the review of the afternoon).
# v5 (23 October 2026): the single rule for general networks (attention), `Interp.gsingle`, on the
# allowlist, priced as cost-v3 prices a single leaf of such a network; extract for a general network is its
# weight count without the exporter's scalar constants, and a general network with charged operations that
# do not depend on the input is refused scoring (cost-v3 charges them once; the open lane does not yet).
# v4 (22 October, after pilot 2 and review round 7): a free weightSize read, graph constructors of the
# linear family and two audited match-compiler constants on the allowlist. v3 (21 October): language
# version 4 and the description-size budget. Recorded in every receipt and in the policy digest.
POLICY_VERSION = "open-lane-policy-v8"
ASSURANCE = "kernel_checked_instance"  # a scored result's count and bill are both kernel-checked, never executed
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
IMPORT_LINE = re.compile(r"^\s*import\s+([A-Za-z_][A-Za-z0-9_.]*)\s*$")
COMPILE_TIMEOUT_S = 3600
CHECK_TIMEOUT_S = 3600
MEMORY_MB = 12288  # virtual: Mathlib's .olean files are mapped into memory
ALLOWLIST = LEAN_PROJECT / "accept" / "allowlist.txt"
# The knowledge conditions (docs/COUNTED.md, "Knowledge conditions"): minimal is the base language; maximum adds
# the fixed rules lane's rules for groups of inputs as operations (allowlist-maximum.txt). Set by --knowledge; part of
# the policy digest and recorded in every receipt, so a run's frontier never mixes the two.
ALLOWLIST_MAXIMUM = LEAN_PROJECT / "accept" / "allowlist-maximum.txt"
KNOWLEDGE_CONDITIONS = ("minimal", "maximum")
KNOWLEDGE = "minimal"
# the scoring policy (docs/COUNTED.md): the checker's description size and the general layer's kernel work
# are bounded. The size budget is base + per_param * E in acceptcheck's units (a node 1, a numeral or a
# string 1 per bit), calibrated so that an honest checker fits (the pilot's column checker is under 8,000)
# and a copy of the weights does not: an exported weight has 23 to 35 bits (its mantissa, shifted to the
# tensor's common exponent), so a copy costs at least about 24 E however it is written, against 4 E plus
# the base, on every network of the zoo with E above about 400 (max2 v64 has 1,088; scripts/test_accept.py
# checks the arithmetic on every exported network). On a tiny network (E = 80) the whole set of weights is
# smaller than any checker, and the budget cannot separate them. The environment variables are hooks for
# tests; whatever is in force is in the policy digest and the receipt.
SIZE_BUDGET_BASE = int(os.environ.get("ACCEPT_SIZE_BUDGET_BASE", 8192))
SIZE_BUDGET_PER_PARAM = int(os.environ.get("ACCEPT_SIZE_BUDGET_PER_PARAM", 4))
GENERAL_KERNEL_BUDGET_MS = 120_000  # kernel time to replay the general layer


def size_budget(extract: int) -> int:
    return SIZE_BUDGET_BASE + SIZE_BUDGET_PER_PARAM * extract


class Reject(Exception):
    """The candidate is at fault."""


class Unsupported(Exception):
    pass


class Infra(Exception):
    pass


def sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def sha256_text(s: str) -> str:
    return hashlib.sha256(s.encode()).hexdigest()


# ---- the toolchain and the project ---------------------------------------------------------------
def lean_binary() -> Path:
    for candidate in (shutil.which("lean"), str(Path.home() / ".elan" / "bin" / "lean")):
        if candidate and Path(candidate).exists():
            p = Path(candidate).resolve()
            # elan's bin/lean is a proxy; ask it where the real toolchain is
            try:
                out = subprocess.run([str(p), "--print-prefix"], capture_output=True, text=True, timeout=60,
                                     cwd=str(LEAN_PROJECT))
                if out.returncode == 0 and out.stdout.strip():
                    return Path(out.stdout.strip()) / "bin" / "lean"
            except (OSError, subprocess.TimeoutExpired):
                pass
            return p
    raise Infra("no lean binary found (install elan)")


def toolchain_root(lean: Path) -> Path:
    return lean.parent.parent


def lean_path() -> list[str]:
    """The LEAN_PATH of the Lean project: its build and its packages' builds."""
    r = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], capture_output=True, text=True,
                       cwd=str(LEAN_PROJECT), timeout=300, env={**os.environ, "PATH": _path_with_elan()})
    if r.returncode != 0 or not r.stdout.strip():
        raise Infra(f"lake env failed in {LEAN_PROJECT}: {r.stderr[-500:]}")
    return [p for p in r.stdout.strip().split(":") if p]


def _path_with_elan() -> str:
    return str(Path.home() / ".elan" / "bin") + ":" + os.environ.get("PATH", "/usr/bin:/bin")


def acceptcheck_binary() -> Path:
    p = LEAN_PROJECT / ".lake" / "build" / "bin" / "acceptcheck"
    if not p.exists():
        raise Infra(f"{p} is missing: run `lake build acceptcheck` in {LEAN_PROJECT}")
    return p


# ---- the box -----------------------------------------------------------------------------------------
BOX_MODES = ("hardened", "landlock", "seatbelt", "process")
SEATBELT = "/usr/bin/sandbox-exec"


def seatbelt_available() -> bool:
    return sys.platform == "darwin" and os.path.exists(SEATBELT)


def box_mode(want: str) -> str:
    """The box: Landlock where the kernel has it (hardened or landlock), macOS's sandbox-exec when asked for by
    name (seatbelt; not chosen by hardened until it has passed its test on a Mac), else the process box, which
    only limits time and memory and is recorded as weak."""
    if want == "process":
        return "process"
    if want == "seatbelt":
        if not seatbelt_available():
            raise Infra("seatbelt mode needs macOS with /usr/bin/sandbox-exec")
        return "seatbelt"
    try:
        sys.path.insert(0, str(_repo))
        from core.sandbox import landlock_available
    finally:
        sys.path.pop(0)
    if landlock_available():
        return "landlock"
    if want == "landlock":
        raise Infra("Landlock is not available on this machine")
    return "process"


_repo: Path = Path(".")
_work: Path | None = None  # the service's work folder (other candidates' workspaces, receipts): seatbelt refuses it


def _sb(path) -> str:
    return '"' + str(path).replace("\\", "\\\\").replace('"', '\\"') + '"'


def _both(paths) -> list[str]:
    """Each path as given and with its links resolved: a profile is matched against real paths."""
    out = set()
    for p in paths:
        out.add(os.path.abspath(str(p)))
        out.add(os.path.realpath(str(p)))
    return sorted(out)


def python_executables() -> list[str]:
    """The programs that starting this Python runs: on a macOS framework build (python.org, Homebrew),
    bin/python3.x replaces itself with the interpreter inside the framework's Python.app."""
    import sysconfig
    paths = [sys.executable]
    framework = sysconfig.get_config_var("PYTHONFRAMEWORK")
    if sys.platform == "darwin" and framework:
        app = os.path.join(sys.base_prefix, "Resources", "Python.app", "Contents", "MacOS", framework)
        if os.path.exists(app):
            paths.append(app)
    return _both(paths)


def seatbelt_profile(ws: Path, read: list[str], deny_read: list[str], execs: list[str], read_write: list[str]) -> str:
    """The sandbox-exec profile of one boxed command. Everything not named stays as macOS allows it (allow
    default), and the rules after it take that away; in a profile a later rule wins over an earlier one, so
    reading deny_read (the home folder, the work folder, the pipeline) is refused and then the paths the
    Landlock box may read (read) are allowed again. Writing: ws/out, ws/tmp and the devices only. Programs:
    Python (which runs _boxrun.py) and the command only. No network, no other process, no signal to another."""
    rules = [
        "(version 1)",
        "(allow default)",
        "(deny network*)",
        "(deny process-fork)",
        "(deny process-exec)",
        "(allow process-exec " + " ".join(f"(literal {_sb(p)})" for p in _both(execs)) + ")",
        "(deny signal)",
        "(allow signal (target self))",
        "(deny file-write*)",
        "(allow file-write* " + " ".join(f"(subpath {_sb(p)})" for p in _both([ws / "out", ws / "tmp"]))
        + "".join(f" (literal {_sb(p)})" for p in read_write) + ")",
        "(deny file-read* " + " ".join(f"(subpath {_sb(p)})" for p in _both(deny_read)) + ")",
        "(allow file-read* " + " ".join(f"(subpath {_sb(p)})" for p in _both(read)) + ")",
        "(allow file-read-metadata)",  # finding one's way along a path; no contents, no listings
    ]
    return "\n".join(rules) + "\n"


def run_boxed(ws: Path, cmd: list[str], env: dict, mode: str, timeout_s: float, read_extra: list[str]) -> dict:
    """Run cmd in the box rooted at ws (out/ and tmp/ writable). Returns rc, stdout, stderr, timed_out."""
    sys.path.insert(0, str(_repo))
    try:
        from core.sandbox import SYSTEM_READ, DEVICE_READ, DEVICE_READ_WRITE, PROC_READ, python_paths
        import core.harness as harness
    finally:
        sys.path.pop(0)
    (ws / "out").mkdir(exist_ok=True)
    (ws / "tmp").mkdir(exist_ok=True)
    shutil.copy(harness.__file__, ws / "_harness.py")
    shutil.copy(HERE / "_boxrun.py", ws / "_boxrun.py")
    policy = None
    if mode == "landlock":
        read = [p for p in SYSTEM_READ + DEVICE_READ + PROC_READ if os.path.exists(p)] + [str(ws)] + read_extra
        policy = {"read": read, "read_write": [str(ws / "out"), str(ws / "tmp")] + list(DEVICE_READ_WRITE),
                  "own_proc": True}
    job = {"policy": policy, "limits": {"RLIMIT_AS": MEMORY_MB << 20, "RLIMIT_CPU": int(timeout_s) + 60},
           "cwd": str(ws), "env": env, "cmd": cmd}
    (ws / "job.json").write_text(json.dumps(job))
    argv = [sys.executable, "-I", "-B", str(ws / "_boxrun.py"), str(ws / "job.json")]
    if mode == "seatbelt":
        # the profile holds from the start, so Python's own folders must be readable too (in landlock mode
        # _boxrun.py locks itself in after Python has started)
        read = python_paths() + [p for p in SYSTEM_READ + DEVICE_READ if os.path.exists(p)] + [str(ws)] + read_extra
        deny = [str(Path.home()), str(_repo)] + ([str(_work)] if _work else [])
        profile = seatbelt_profile(ws, read, deny, python_executables() + [cmd[0]], list(DEVICE_READ_WRITE))
        argv = [SEATBELT, "-p", profile] + argv
    t0 = time.time()
    try:
        p = subprocess.run(argv, capture_output=True, text=True, timeout=timeout_s, cwd=str(ws))
    except subprocess.TimeoutExpired as exc:
        return {"rc": -9, "stdout": exc.stdout or "", "stderr": "timed out", "timed_out": True,
                "seconds": round(time.time() - t0, 1)}
    return {"rc": p.returncode, "stdout": p.stdout, "stderr": p.stderr, "timed_out": False,
            "seconds": round(time.time() - t0, 1)}


# ---- the pieces ---------------------------------------------------------------------------------------
def export_network(repo: Path, model: str, network: str, work: Path) -> Path:
    out = work / "networks" / f"{network}.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    if out.exists():
        return out
    r = subprocess.run([sys.executable, "-B", str(HERE / "export_network.py"), str(repo), model, network, str(out)],
                       capture_output=True, text=True, timeout=1800)
    if r.returncode != 0:
        msg = (r.stderr or r.stdout)[-800:]
        if "not supported" in msg or "ExportError" in msg:
            raise Unsupported(f"the network cannot be exported for the Lean checker: {msg}")
        raise Infra(f"export failed: {msg}")
    return out


def excerpt(text: str, head: int = 1500, tail: int = 500) -> str:
    """The first errors and the last lines of a compiler's output: the first error is the one that matters,
    and a later one (a `decide` that cannot reduce) can be thousands of lines on its own."""
    if len(text) <= head + tail:
        return text
    return text[:head] + "\n[...]\n" + text[-tail:]


def box_env(ws: Path, lean: Path, lp: list[str]) -> dict:
    """The environment of a boxed lean or acceptcheck: the search path, the toolchain, a home in tmp/."""
    root = toolchain_root(lean)
    return {"LEAN_PATH": ":".join(lp + [str(ws / "out")]), "LEAN_SYSROOT": str(root),
            "PATH": f"{root / 'bin'}:/usr/bin:/bin", "HOME": str(ws / "tmp"), "TMPDIR": str(ws / "tmp"),
            "LANG": "C.UTF-8"}


def compile_module(ws: Path, root: Path, module: str, src: Path, lean: Path, lp: list[str], mode: str,
                   timeout_s: float = COMPILE_TIMEOUT_S) -> dict:
    """Compile one module whose source is src (module name relative to root) into ws/out."""
    out = ws / "out" / (module.replace(".", "/") + ".olean")
    out.parent.mkdir(parents=True, exist_ok=True)
    env = box_env(ws, lean, lp)
    # Elaboration in one thread: with asynchronous elaboration (Lean's default) every theorem of a module is a
    # task, and a module of many theorems (an instance split into one decided fact per input) makes Lean start
    # threads whose stacks reserve more address space than any limit the box can set (64 GB was not enough for
    # 64 facts; the process reserved about 77 GB unlimited). Sequential elaboration builds the same constants.
    cmd = [str(lean), "-DElab.async=false", "-R", str(root), "-o", str(out), str(src)]
    res = run_boxed(ws, cmd, env, mode, timeout_s, [str(toolchain_root(lean)), str(LEAN_PROJECT)] + lp)
    res["module"] = module
    res["olean"] = str(out)
    return res


def check_imports(text: str, module: str, modules: set[str], protected: str) -> list[str]:
    """The module's imports, each checked against the allowlist. Imports must come first, as in Lean."""
    imports = []
    for line in text.splitlines():
        s = line.strip()
        if not s or s.startswith("--"):
            continue
        m = IMPORT_LINE.match(line)
        if not m:
            break
        name = m.group(1)
        if name.startswith("Candidate."):
            if name not in modules:
                raise Reject(f"{module} imports {name}, which is not a submitted module")
            if name == module:
                raise Reject(f"{module} imports itself")
        elif name == protected or name.startswith(TRUSTED_PREFIXES):
            pass
        else:
            raise Reject(f"{module} imports {name}; allowed: the submitted Candidate modules, {protected}, "
                         "CompactCheck.* and Mathlib.*")
        imports.append(name)
    return imports


def order_modules(deps: dict[str, list[str]]) -> list[str]:
    """Candidate modules in an order where every import comes first."""
    out, state = [], {}

    def visit(m, trail):
        if state.get(m) == 2:
            return
        if state.get(m) == 1:
            raise Reject("the candidate modules import each other in a cycle: " + " -> ".join(trail + [m]))
        state[m] = 1
        for d in deps[m]:
            if d.startswith("Candidate."):
                visit(d, trail + [m])
        state[m] = 2
        out.append(m)

    for m in sorted(deps):
        visit(m, [])
    return out


def read_manifest(cdir: Path) -> dict:
    p = cdir / "manifest.json"
    if not p.is_file():
        raise Reject("manifest.json is missing")
    try:
        m = json.loads(p.read_text())
    except ValueError as exc:
        raise Reject(f"manifest.json is not JSON: {exc}")
    if not isinstance(m, dict) or m.get("schema") != SCHEMA:
        raise Reject(f"manifest schema must be {SCHEMA}")
    for key, typ in (("candidate_id", str), ("model", str), ("network", str), ("theorem", str), ("modules", list)):
        if not isinstance(m.get(key), typ):
            raise Reject(f"manifest field {key} must be a {typ.__name__}")
    m["kind"] = m.get("kind", "performance")
    if m["kind"] not in KINDS:
        raise Reject(f"kind must be one of {KINDS}")
    if m["kind"] == "auxiliary":
        m.setdefault("claimed_count", 0)  # names the protected module the lemma may import; no claim is made
        if "scored" in m:
            raise Reject("an auxiliary submission cannot be scored")
    c = m.get("claimed_count")
    if not isinstance(c, int) or isinstance(c, bool) or c < 0:
        raise Reject("claimed_count must be a natural number")
    if not re.match(r"^[A-Za-z0-9_.-]{1,80}$", m["candidate_id"]):
        raise Reject("candidate_id must be 1 to 80 letters, digits, dots, dashes or underscores")
    if not m["modules"]:
        raise Reject("modules is empty")
    for rel in m["modules"]:
        if not isinstance(rel, str) or not rel.startswith("Candidate/") or not rel.endswith(".lean"):
            raise Reject(f"module path {rel!r} must be Candidate/<Name>.lean")
        parts = rel[len("Candidate/"):-len(".lean")].split("/")
        if not all(IDENT.match(x) for x in parts):
            raise Reject(f"module path {rel!r} is not made of identifiers")
        f = cdir / rel
        if f.is_symlink() or not f.is_file():
            raise Reject(f"module {rel} is missing or is a symbolic link")
    parts = m["theorem"].split(".")
    if len(parts) < 2 or parts[0] != "Candidate" or not all(IDENT.match(x) for x in parts):
        raise Reject("theorem must be a name under Candidate., made of identifiers")
    if not re.match(r"^[A-Za-z0-9_./-]+$", m["model"]) or ".." in m["model"]:
        raise Reject("model must be a relative path in the pipeline repository")
    if not re.match(r"^[A-Za-z0-9_-]+$", m["network"]):
        raise Reject("network must be a network id")
    if "scored" in m:
        s = m["scored"]
        if not isinstance(s, dict):
            raise Reject("scored must be an object")
        for key in ("checker", "sound", "instance"):
            v = s.get(key)
            if not isinstance(v, str):
                raise Reject(f"scored.{key} must be a constant name")
            ps = v.split(".")
            if len(ps) < 2 or ps[0] != "Candidate" or not all(IDENT.match(x) for x in ps):
                raise Reject(f"scored.{key} must be a name under Candidate., made of identifiers")
        b = s.get("claimed_bill")
        if not isinstance(b, int) or isinstance(b, bool) or b < 0:
            raise Reject("scored.claimed_bill must be a natural number")
        sys.path.insert(0, str(HERE))
        try:
            import make_protected
        finally:
            sys.path.pop(0)
        try:
            s["certificate"] = make_protected.canonical_cert(s.get("certificate", []))
        except make_protected.ProtectedError as exc:
            raise Reject(f"scored.certificate: {exc}")
    return m


# ---- the protected module ---------------------------------------------------------------------------
def build_protected(net_json: Path, claimed: int, work: Path, lean: Path, lp: list[str], mode: str,
                    cert: list | None = None) -> dict:
    """Write, compile and verify the protected module; returns {module, olean, ...}. Cached by content."""
    sys.path.insert(0, str(HERE))
    try:
        import make_protected
    finally:
        sys.path.pop(0)
    net = json.loads(net_json.read_text())
    try:
        name, src = make_protected.render(net, claimed, cert)
    except make_protected.ProtectedError as exc:
        if "not supported" in str(exc):
            raise Unsupported(str(exc))
        raise Reject(str(exc))
    module = f"Protected.{name}"
    pdir = work / "protected"
    ws = pdir / name
    olean = ws / "out" / "Protected" / f"{name}.olean"
    stamp = ws / "verified.json"
    if olean.exists() and stamp.exists() and json.loads(stamp.read_text()).get("source_sha256") == sha256_text(src):
        return {"module": module, "olean": str(olean), "lean_path_dir": str(ws / "out"), "cached": True,
                "domain": json.loads(stamp.read_text())["domain"]}
    shutil.rmtree(ws, ignore_errors=True)
    (ws / "Protected").mkdir(parents=True)
    srcp = ws / "Protected" / f"{name}.lean"
    srcp.write_text(src)
    (ws / "cert.json").write_text(json.dumps(cert or []))
    res = compile_module(ws, ws, module, srcp, lean, lp, mode)
    if res["timed_out"]:
        raise Infra("compiling the protected module timed out")
    if res["rc"] != 0:
        raise Infra(f"the protected module does not compile: {res['stdout'][-1500:]}{res['stderr'][-500:]}")
    env = box_env(ws, lean, lp)
    chk = run_boxed(ws, [str(acceptcheck_binary()), "protected", str(net_json), module, str(olean)], env, mode,
                    CHECK_TIMEOUT_S, [str(toolchain_root(lean)), str(LEAN_PROJECT), str(net_json)])
    last = last_json(chk["stdout"])
    if chk["rc"] != 0 or not last or last.get("status") != "ok":
        raise Infra(f"the protected module does not match the network file: {last or chk['stderr'][-800:]}")
    stamp.write_text(json.dumps({"source_sha256": sha256_text(src), "domain": last["domain"],
                                 "network": last["network"]}))
    return {"module": module, "olean": str(olean), "lean_path_dir": str(ws / "out"), "cached": False,
            "domain": last["domain"]}


def last_json(text: str) -> dict | None:
    for line in reversed(text.strip().splitlines()):
        line = line.strip()
        if line.startswith("{"):
            try:
                return json.loads(line)
            except ValueError:
                return None
    return None


# ---- a submission -------------------------------------------------------------------------------------
def submit(cdir: Path, repo: Path, work: Path, want_mode: str) -> dict:
    global _repo, _work
    _repo, _work = repo, work
    t0 = time.time()
    receipt = {"schema": RECEIPT_SCHEMA, "candidate_id": None, "status": None, "reason": None,
               "claim_kind": None, "certified_count": None, "domain_size": None, "claimed_count": None, "network": None,
               "theorem": None, "statement": None, "axioms": None, "isolation": None, "steps": [], "digests": {},
               "score_eligible": False, "execution_assurance": None, "cost_model": COST_MODEL, "policy_version": POLICY_VERSION,
               "knowledge": KNOWLEDGE,
               "scoring": {"status": "not_requested"},
               "seconds": None, "time": time.strftime("%Y-%m-%dT%H:%M:%S%z")}
    ws = None
    try:
        manifest = read_manifest(cdir)
        receipt.update(candidate_id=manifest["candidate_id"], claimed_count=manifest["claimed_count"] if manifest["kind"] == "performance" else None,
                       network=manifest["network"], theorem=manifest["theorem"], claim_kind=manifest["kind"])
        mode = box_mode(want_mode)
        receipt["isolation"] = mode if mode in ("landlock", "seatbelt") else "process (weak: no Landlock here)"
        lean = lean_binary()
        lp = lean_path()
        # the service's identity, as `accept.py identity` reports it: a run checks every receipt against the
        # identity it recorded when it started
        receipt["digests"].update({k: v for k, v in identity().items() if k != "dirty"})
        # the modules and their imports
        modules = {}
        for rel in manifest["modules"]:
            name = "Candidate." + rel[len("Candidate/"):-len(".lean")].replace("/", ".")
            if name in modules:
                raise Reject(f"module {name} is listed twice")
            modules[name] = cdir / rel
        receipt["digests"]["modules"] = {m: sha256_file(p) for m, p in modules.items()}
        # the network and the protected target
        net_json = export_network(repo, manifest["model"], manifest["network"], work)
        receipt["digests"]["network_file"] = sha256_file(net_json)
        scored = manifest.get("scored")
        prot = build_protected(net_json, manifest["claimed_count"], work, lean, lp, mode,
                               scored["certificate"] if scored else None)
        receipt["domain_size"] = prot["domain"]
        receipt["steps"].append({"step": "protected", "module": prot["module"], "cached": prot["cached"]})
        deps = {m: check_imports(p.read_text(), m, set(modules), prot["module"]) for m, p in modules.items()}
        order = order_modules(deps)
        # the workspace
        ws = work / "submissions" / f"{manifest['candidate_id']}-{int(t0)}"
        if ws.exists():
            raise Infra(f"{ws} exists")
        (ws / "Candidate").mkdir(parents=True)
        for m, p in modules.items():
            dst = ws / (m.replace(".", "/") + ".lean")
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(p, dst)
        lp_all = lp + [prot["lean_path_dir"]]
        oleans = []
        for m in order:
            res = compile_module(ws, ws, m, ws / (m.replace(".", "/") + ".lean"), lean, lp_all, mode)
            receipt["steps"].append({"step": "compile", "module": m, "rc": res["rc"], "seconds": res["seconds"],
                                     "timed_out": res["timed_out"]})
            if res["timed_out"]:
                receipt.update(status="timeout", reason=f"compiling {m} exceeded {COMPILE_TIMEOUT_S} s")
                return finish(receipt, work, t0)
            if res["rc"] != 0:
                raise Reject(f"{m} does not compile: {excerpt(res['stdout'] + res['stderr'])}")
            oleans.append(res["olean"])
        # the kernel
        trusted = [prot["module"]] + sorted({d for ds in deps.values() for d in ds if not d.startswith("Candidate.")})
        env = box_env(ws, lean, lp_all)
        if manifest["kind"] == "auxiliary":
            cmd = [str(acceptcheck_binary()), "lemma", manifest["theorem"]] + trusted + ["--"] + oleans
        else:
            cmd = [str(acceptcheck_binary()), "check", prot["module"] + ".Target", manifest["theorem"]] + trusted + ["--"] + oleans
        chk = run_boxed(ws, cmd, env, mode, CHECK_TIMEOUT_S, [str(toolchain_root(lean)), str(LEAN_PROJECT)] + lp_all)
        receipt["steps"].append({"step": "kernel", "rc": chk["rc"], "seconds": chk["seconds"], "timed_out": chk["timed_out"]})
        if chk["timed_out"]:
            receipt.update(status="timeout", reason=f"the kernel check exceeded {CHECK_TIMEOUT_S} s")
            return finish(receipt, work, t0)
        last = last_json(chk["stdout"])
        if chk["rc"] != 0 or last is None:
            raise Infra(f"acceptcheck failed: {(chk['stdout'] + chk['stderr'])[-1500:]}")
        if last.get("status") != "accepted":
            raise Reject(last.get("reason") or "the kernel rejected the candidate")
        axioms = list(last.get("axioms") or [])
        receipt["axioms"] = axioms
        bad = sorted(set(axioms) - ALLOWED_AXIOMS)
        if bad:
            raise Reject(f"the proof depends on axioms that are not allowed: {', '.join(bad)}")
        if manifest["kind"] == "auxiliary":
            receipt.update(status="accepted", statement=last.get("statement"), replayed_constants=last.get("replayed"))
            return finish(receipt, work, t0)
        receipt.update(status="accepted", certified_count=manifest["claimed_count"],
                       replayed_constants=last.get("replayed"))
        if scored:
            receipt["scoring"] = score(scored, manifest, prot, net_json, trusted, oleans, ws, env, mode, lean, lp_all, receipt)
            if receipt["scoring"]["status"] == "scored":
                receipt.update(score_eligible=True, execution_assurance=ASSURANCE)
    except Reject as exc:
        receipt.update(status="rejected", reason=str(exc))
    except Unsupported as exc:
        receipt.update(status="unsupported", reason=str(exc))
    except Infra as exc:
        receipt.update(status="error", reason=str(exc))
    return finish(receipt, work, t0)


def score(scored: dict, manifest: dict, prot: dict, net_json: Path, trusted: list[str], oleans: list[str], ws: Path,
          env: dict, mode: str, lean: Path, lp_all: list[str], receipt: dict) -> dict:
    """The scored path, after verification: the closure check, the kernel's two challenges, the budgets, the
    length. Returns the receipt's `scoring` block; never raises for the candidate's faults."""
    net = json.loads(net_json.read_text())
    extract = extraction_cost(net)
    read = len(scored["certificate"])
    out = {"status": None, "reason": None, "assurance": ASSURANCE, "cost_model": COST_MODEL,
           "bill": None, "extract": extract, "read": read, "length": None,
           "description_size": None, "size_budget": None if extract is None else size_budget(extract),
           "general_kernel_ms": None, "general_kernel_budget_ms": GENERAL_KERNEL_BUDGET_MS, "rest_kernel_ms": None,
           "axioms": None}
    if extract is None:
        # a property of the network, not of the candidate: refused before any check of the candidate's checker
        out.update(status="refused", reason="the network has operations that do not depend on the input and cost "
                   "something; cost-v3 charges them to extract once, which the open lane does not compute yet")
        return out
    read_extra = [str(toolchain_root(lean)), str(LEAN_PROJECT)] + lp_all
    # the checker touches numbers only through the counted primitives
    allowlist = ws / "allowlist.txt"  # the list in force, written where the box can read it
    allowlist.write_text(allowlist_text())
    cmd = [str(acceptcheck_binary()), "closure", scored["checker"], str(allowlist), prot["module"]] + trusted + ["--"] + oleans
    chk = run_boxed(ws, cmd, env, mode, CHECK_TIMEOUT_S, read_extra)
    receipt["steps"].append({"step": "closure", "rc": chk["rc"], "seconds": chk["seconds"], "timed_out": chk["timed_out"]})
    last = last_json(chk["stdout"])
    if chk["timed_out"] or chk["rc"] != 0 or last is None:
        raise Infra(f"acceptcheck closure failed: {(chk['stdout'] + chk['stderr'])[-1500:]}")
    if last.get("status") != "ok":
        out.update(status="refused", reason="the checker uses constants outside the counted language: "
                   + ", ".join(last.get("offending") or []) + (f" ({last['reason']})" if last.get("reason") else ""))
        return out
    out["closure_visited"] = last.get("visited")
    # the kernel: the soundness shape and the instance
    cmd = [str(acceptcheck_binary()), "score", prot["module"], scored["checker"], scored["sound"], scored["instance"],
           str(manifest["claimed_count"]), str(scored["claimed_bill"])] + trusted + ["--"] + oleans
    chk = run_boxed(ws, cmd, env, mode, CHECK_TIMEOUT_S, read_extra)
    receipt["steps"].append({"step": "score", "rc": chk["rc"], "seconds": chk["seconds"], "timed_out": chk["timed_out"]})
    if chk["timed_out"]:
        out.update(status="timeout", reason=f"the scored kernel check exceeded {CHECK_TIMEOUT_S} s")
        return out
    last = last_json(chk["stdout"])
    if chk["rc"] != 0 or last is None:
        raise Infra(f"acceptcheck score failed: {(chk['stdout'] + chk['stderr'])[-1500:]}")
    if last.get("status") != "accepted":
        out.update(status="refused", reason=last.get("reason") or "the kernel rejected the scored submission")
        return out
    axioms = list(last.get("axioms") or [])
    out["axioms"] = axioms
    bad = sorted(set(axioms) - ALLOWED_AXIOMS)
    if bad:
        out.update(status="refused", reason=f"the scored proofs depend on axioms that are not allowed: {', '.join(bad)}")
        return out
    general, rest = last.get("general") or {}, last.get("rest") or {}
    out.update(description_size=general.get("description_size"), general_kernel_ms=general.get("kernel_ms"),
               rest_kernel_ms=rest.get("kernel_ms"), general_constants=general.get("constants"),
               checker_constants=general.get("checker_constants"))
    if out["description_size"] is None or out["description_size"] > out["size_budget"]:
        out.update(status="refused", reason=f"the checker's description size {out['description_size']} exceeds the budget {out['size_budget']}")
        return out
    if out["general_kernel_ms"] is None or out["general_kernel_ms"] > GENERAL_KERNEL_BUDGET_MS:
        out.update(status="refused", reason=f"replaying the general layer took {out['general_kernel_ms']} ms, over the budget {GENERAL_KERNEL_BUDGET_MS} ms")
        return out
    # the length, in cost-v3 units
    out.update(status="scored", bill=scored["claimed_bill"], length=scored["claimed_bill"] + extract + read)
    return out


FREE_OPS = ("input", "param", "index", "transpose", "unsqueeze", "expand", "cat", "stack", "zerosLike")


def extraction_cost(net: dict) -> int | None:
    """cost-v3's E for a network file: one per parameter of the model. Constants the exporter turns into
    weights (`#const...`, such as an attention scale) are literals of the model's code, not parameters,
    and cost-v3 does not count them. On a general network, cost-v3 also charges to E the operations that
    do not depend on the input, computed once per proof; `None` if there is one that costs something
    (none of the zoo's attention networks has one), so that the length is never understated."""
    E = sum(len(w["ints"]) for w in net["weights"] if not w["name"].startswith("#const"))
    if net.get("general"):
        nodes = net["graph"]["nodes"]
        deps = []
        for op in nodes:
            args = [op[k] for k in ("arg", "left", "right") if k in op] + list(op.get("args") or [])
            deps.append(op["op"] == "input" or any(deps[a] for a in args if isinstance(a, int) and a < len(deps)))
        if any(not d and op["op"] not in FREE_OPS for d, op in zip(deps, nodes)):
            return None
    return E


def allowlist_text() -> str:
    """The allowlist in force: the base list, and in the maximum-knowledge condition its additions."""
    text = ALLOWLIST.read_text() if ALLOWLIST.exists() else ""
    if KNOWLEDGE == "maximum":
        text += "\n" + (ALLOWLIST_MAXIMUM.read_text() if ALLOWLIST_MAXIMUM.exists() else "")
    return text


def policy_digest() -> str:
    """A digest of the scoring policy: the allowlist in force (with the knowledge condition) and the budgets."""
    h = hashlib.sha256()
    h.update(allowlist_text().encode())
    h.update(json.dumps({"policy_version": POLICY_VERSION, "knowledge": KNOWLEDGE,
                         "size_budget": [SIZE_BUDGET_BASE, SIZE_BUDGET_PER_PARAM],
                         "general_kernel_budget_ms": GENERAL_KERNEL_BUDGET_MS,
                         "allowed_axioms": sorted(ALLOWED_AXIOMS), "trusted_prefixes": TRUSTED_PREFIXES}).encode())
    return h.hexdigest()[:16]


def finish(receipt: dict, work: Path, t0: float) -> dict:
    receipt["seconds"] = round(time.time() - t0, 1)
    if receipt["status"] != "accepted":
        receipt["certified_count"] = None
        receipt["score_eligible"] = False
    rdir = work / "receipts"
    rdir.mkdir(parents=True, exist_ok=True)
    name = f"{receipt['candidate_id'] or 'invalid'}-{int(t0)}.json"
    (rdir / name).write_text(json.dumps(receipt, indent=1))
    receipt["receipt_path"] = str(rdir / name)
    return receipt


def compile_for_development(ws: Path, rel: str, repo: Path, model: str, network: str, claimed: int, work: Path,
                            want_mode: str, cert: list | None = None) -> dict:
    """Compile <ws>/<rel> against the protected module of (network, claimed, certificate), in the box, with the
    workspace's own out/ on the path for its other modules. For a candidate's development, never for acceptance:
    returns {"ok", "timed_out", "module", "protected_module", "messages", "seconds"} or {"ok": False, "error"}."""
    global _repo, _work
    _repo, _work = repo, work
    if not re.match(r"^Candidate/([A-Za-z_][A-Za-z0-9_]*/)*[A-Za-z_][A-Za-z0-9_]*\.lean$", rel):
        return {"ok": False, "error": "the module path must be Candidate/<Name>.lean"}
    src = ws / rel
    if src.is_symlink() or not src.is_file():
        return {"ok": False, "error": f"{rel} is not a file of the workspace"}
    try:
        mode = box_mode(want_mode)
        lean, lp = lean_binary(), lean_path()
        net_json = export_network(repo, model, network, work)
        prot = build_protected(net_json, claimed, work, lean, lp, mode, cert)
    except (Reject, Unsupported, Infra) as exc:
        return {"ok": False, "error": str(exc)}
    module = "Candidate." + rel[len("Candidate/"):-len(".lean")].replace("/", ".")
    (ws / "out").mkdir(exist_ok=True)
    res = compile_module(ws, ws, module, src, lean, lp + [prot["lean_path_dir"], str(ws / "out")], mode)
    text = (res["stdout"] + res["stderr"]).strip()
    return {"ok": res["rc"] == 0 and not res["timed_out"], "timed_out": res["timed_out"], "module": module,
            "protected_module": prot["module"], "messages": text, "seconds": round(res["seconds"], 1)}


IDENTITY_KEYS = ("commit", "toolchain", "lean_project", "policy", "acceptcheck")


def identity() -> dict:
    """What the service is, for a run to record when it starts and to check when it resumes: the Lean
    project's commit and whether tracked files are modified, the toolchain, the project's trusted sources,
    the policy as it is in force (environment hooks included) and the acceptcheck binary. Every receipt
    carries these five digests (IDENTITY_KEYS) under `digests`; a receipt whose digests differ from the
    identity a run recorded was made by a different service."""
    lean = lean_binary()
    try:
        head = subprocess.run(["git", "-C", str(LEAN_PROJECT), "rev-parse", "HEAD"], capture_output=True, text=True,
                              timeout=60).stdout.strip() or None
        dirty = bool(subprocess.run(["git", "-C", str(LEAN_PROJECT), "status", "--porcelain", "--untracked-files=no"],
                                    capture_output=True, text=True, timeout=60).stdout.strip())
    except (OSError, subprocess.TimeoutExpired):
        head, dirty = None, True
    return {"commit": head, "dirty": dirty,
            "toolchain": (toolchain_root(lean) / "bin" / "lean").name + ":" + sha256_file(lean)[:16],
            "lean_project": project_digest(), "policy": policy_digest(),
            "acceptcheck": sha256_file(acceptcheck_binary())[:16]}


def project_digest() -> str:
    """A digest of the Lean project's source: the trusted base of every receipt."""
    h = hashlib.sha256()
    files = sorted(list(LEAN_PROJECT.glob("CompactCheck/*.lean")) + [LEAN_PROJECT / "AcceptMain.lean",
                   LEAN_PROJECT / "lakefile.toml", LEAN_PROJECT / "lake-manifest.json", LEAN_PROJECT / "lean-toolchain",
                   HERE / "make_protected.py", HERE / "export_network.py", HERE / "accept.py", HERE / "_boxrun.py"])
    for f in files:
        if f.exists():
            h.update(f.name.encode() + b"\0" + f.read_bytes() + b"\0")
    return h.hexdigest()[:16]


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("submit")
    s.add_argument("candidate", type=Path)
    s.add_argument("--repo", type=Path, required=True, help="the pipeline repository")
    s.add_argument("--work", type=Path, required=True, help="networks, protected modules, workspaces and receipts")
    s.add_argument("--mode", default="hardened", choices=BOX_MODES)
    s.add_argument("--knowledge", default="minimal", choices=KNOWLEDGE_CONDITIONS)
    c = sub.add_parser("compile", help="compile a candidate module in a workspace, for development")
    c.add_argument("workspace", type=Path)
    c.add_argument("module", help="Candidate/<Name>.lean, relative to the workspace")
    c.add_argument("--repo", type=Path, required=True)
    c.add_argument("--work", type=Path, required=True)
    c.add_argument("--model", required=True)
    c.add_argument("--network", required=True)
    c.add_argument("--claimed", type=int, required=True)
    c.add_argument("--certificate", type=Path)
    c.add_argument("--mode", default="hardened", choices=BOX_MODES)
    c.add_argument("--knowledge", default="minimal", choices=KNOWLEDGE_CONDITIONS)
    p = sub.add_parser("protected")
    p.add_argument("network", type=Path)
    p.add_argument("claimed", type=int)
    p.add_argument("--repo", type=Path, required=True)
    p.add_argument("--work", type=Path, required=True)
    p.add_argument("--mode", default="hardened", choices=BOX_MODES)
    p.add_argument("--certificate", type=Path, help="a JSON list of numbers, for a scored submission's module")
    i = sub.add_parser("identity", help="the service's identity: commit, toolchain, project, policy and binary digests")
    i.add_argument("--knowledge", default="minimal", choices=KNOWLEDGE_CONDITIONS)
    args = ap.parse_args(argv)
    global KNOWLEDGE
    KNOWLEDGE = getattr(args, "knowledge", "minimal")
    if args.cmd == "identity":
        print(json.dumps(identity(), indent=1))
        return 0
    global _repo, _work
    _repo, _work = args.repo.resolve(), args.work.resolve()
    if args.cmd == "submit":
        r = submit(args.candidate.resolve(), _repo, args.work.resolve(), args.mode)
        print(json.dumps(r, indent=1))
        return 0 if r["status"] == "accepted" else 1
    if args.cmd == "compile":
        cert = json.loads(args.certificate.read_text()) if args.certificate else None
        r = compile_for_development(args.workspace.resolve(), args.module, _repo, args.model, args.network, args.claimed,
                                    args.work.resolve(), args.mode, cert)
        print(json.dumps(r, indent=1))
        return 0 if r.get("ok") else 1
    mode = box_mode(args.mode)
    cert = json.loads(args.certificate.read_text()) if args.certificate else None
    r = build_protected(args.network.resolve(), args.claimed, args.work.resolve(), lean_binary(), lean_path(), mode, cert)
    print(json.dumps(r, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
