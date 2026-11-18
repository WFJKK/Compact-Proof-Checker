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
   modules), the submission's protected modules, CompactCheck.* and Mathlib.*.
2. The network is exported from the pipeline's zoo with scripts/export_network.py (cached by network), and
   the protected modules are written by scripts/make_protected.py and compiled: the claim's,
   Protected.N_<network>_c<claimed>..., with the graph, the weights, the task and the target, and beside it
   the same definitions in modules whose names no claim changes: the network's, Protected.N_<network> (one
   per network, compiled once), and the certificate's and the plan's when there are any (named by their
   content). `acceptcheck protected` checks the claim module's constants against the network file with the
   checker's own reader. A candidate's facts about the weights can import the network's module alone.
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

and goes through the scored path: the certificate becomes the protected module's `cert`; before the kernel,
`acceptcheck closure` checks that the checker touches numbers only through the counted primitives
(accept/allowlist.txt); then `acceptcheck check-score`, in the one replay that verifies the candidate, has the
kernel accept the soundness theorem at the fixed shape and the instance `CostM.billed D ⟨weights, cert⟩ =
some (claimed_count, claimed_bill)`, and measures the general layer (the checker's description size, kernel
time), which the policy budgets below bound. The receipt's `scoring` block says whether the submission is
scored and gives the length in cost-v3 units: the bill, plus `extract` (one per weight entry) and `read` (one
per certificate number). A submission refused scoring stays verified.

A submission's modules are compiled without the kernel's check of each declaration (`debug.skipKernelTC`):
acceptcheck replays every constant of the candidate through the kernel, and that replay is the check that
counts; checking at the compile as well only did the same work twice (three times for a scored proof, before
check-score). A development compile (`compile`) keeps the kernel's check, so its errors show where they are.

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
import math
import os
import random
import re
import shutil
import subprocess
import sys
import time
from fractions import Fraction
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
# v12 (17 November 2026): a plan is bounded in information too: its length in a prefix code (plan_bits) is at
# most a quarter of weight_bits, so a plan cannot carry a copy of the weights for the checker to compute on for
# free (the honest plan of attn-min2 v64d8's windowed proof measures 775; a copy holds at least 31,127). And a
# proof refused scoring by a budget of the general layer (description size, kernel time) keeps what the kernel
# verified: `measured_bill` and `measured_length`, which no frontier uses. Measured the same day: the size
# measure does not hold a table to one unit per bit (variables are an alphabet: 32,768 random bits measure
# 11,536), so on a network of this size the budget stops a plain copy and no more; docs/COUNTED.md.
# v11 (16 November 2026): the description-size budget follows the network's information: 8192 + 4 E (the budget
# up to v10), raised where it is lower to half of weight_bits (the bits a copy of the weights must hold: each
# weight's sign and significant bits), the share raising it to at most 16,384. attn-min2 v64d8-s1: 13,376
# becomes 15,563; max2 v64-s0: 12,544 becomes 13,010. No budget goes down, and none changes from E = 2,048 on.
# v10 (16 November 2026): `CostM.weight` and `CostM.cert` read through a balanced tree (`ReadTree`, Counted.lean)
# instead of `a[i]!`, which the kernel evaluates by walking `i` cells per read: the same numbers and charges,
# about log2 n kernel steps per read instead of i. A proof that unfolded the old definitions migrates with
# `rw [CostM.weight_run_eq_ite]` / `rw [CostM.cert_run_eq_ite]`; the allowlist and budgets are unchanged.
# v9 (13 November 2026): planned checkers. A scored manifest may give a plan (natural numbers); the checker is
# then `D : List Nat → Checker`, its soundness theorem holds for every plan and its instance runs on the protected
# module's `plan`, which the general layer may not mention. The plan is free, as the fixed rules lane's plan is
# (cost-v4), and bounded as that lane bounds its tree (PLAN_PER_INPUT, PLAN_BASE, PLAN_ENTRY_BITS). Unplanned
# submissions are checked exactly as in v8.
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
# v13 (17 November 2026): the network has a protected module of its own. The claim's module is what it was,
# text for text, and every statement the service writes is the one it wrote before. Beside it the service now
# builds Protected.N_<network> (graph, weights, task) and, for a certificate and a plan, modules named by
# their content, with the same definitions. A candidate's modules that import only those are compiled once
# for a network, not once for every claimed count, certificate and plan (run attn-min2-ptl-3 spent about 20
# compiles of a round on the renames); a fact about the network module's weights is a fact about the claim
# module's, since the kernel unfolds both to the same term. The general layer may use `graph` and `task` of
# either module and no other protected constant, as before. And a theorem that two candidate modules each
# hold with one statement (Lean derives a definition's equation lemmas in every module that first unfolds it)
# is one theorem, no longer "declared twice"; a definition, or one name with two statements, is refused as
# before.
# v14 (17 November 2026): two things against a checker that holds the network's own numbers and computes on
# them for free (the cheat the size budget is for, which it cannot keep out of a small network: there a real
# checker measures about what a copy of the weights does).
#   The size budget is capped (SIZE_BUDGET_CAP). It grew with the network, 4 units per weight, which leaves
# room for a rounded copy of the weights at any size; a checker's code does not grow with the weights, so
# from the cap on a copy has less room the larger the network is. The cap is well above every real checker
# measured (the largest 14,043) and above every budget of a network that has a proof.
#   The last-bits test (last_bits). A scored proof's checker is run again, compiled, with the proof's own
# certificate and plan, on copies of the network whose weights differ in their last bits. A checker that
# computes on the weights it is given certifies what it certified; one whose count rests on comparing the
# weights with numbers it holds certifies nothing, and is refused scoring. It needs nothing about the
# architecture: the copies are made from the network file. It sees an exact copy, not a rounded one compared
# with a tolerance. The runs are of compiled code, so the first is on the network itself and must give what the
# kernel established, and a checker that cannot be run as the kernel ran it is refused scoring too: a module
# that gives a definition other compiled code (implemented_by, extern, export, csimp) or runs code when loaded,
# a noncomputable checker, a run that does not come to an end. The development compile's preview makes the
# same runs (scoring_preview), so that the test's answer costs a compile to see and not a submission.
# v15 (18 November 2026): the checker's run on the network may be the compiled checker's (scored.run:
# "compiled"). A scored result is two statements: the checker never counts more than the network gets right,
# for every weight (soundness: mathematics), and on this network it counts n at a bill of L (the run:
# arithmetic). Until now the kernel made the run too, as the instance theorem; that is where the time and
# the memory went (the run of attn-min2-ptl-3's proof: about 400 s in the kernel, about 1 s compiled), and most
# of a proof's modules existed to cut the run into pieces the kernel can hold. With run "compiled" the
# candidate proves soundness alone, the kernel checks it (acceptcheck sound), and the service runs the compiled
# checker for the count and the bill (acceptcheck probe, the run the last-bits test already makes). What is
# trusted beyond the kernel is then Lean's compiler and runtime, for this one evaluation; the receipt says
# which it was (run, execution_assurance). Everything else is as before: the counted language, the budgets,
# the last-bits test on the same runs. Run "kernel", the default, is unchanged.
POLICY_VERSION = "open-lane-policy-v15"
ASSURANCE = "kernel_checked_instance"  # a scored result's count and bill are both kernel-checked, never executed
ASSURANCE_RUN = "compiled_instance"  # soundness is kernel-checked; the count and the bill are the compiled checker's run
RUNS = ("kernel", "compiled")  # scored.run: who runs the checker on the network
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
# are bounded. The size budget, in acceptcheck's units (a node 1, a numeral or a string 1 per bit), is
# base + per_param * E, or SHARE of weight_bits when that is larger, the share's part at most SHARE_CAP
# (policy v11). weight_bits is the least a copy of the weights holds however it is written: each weight's sign
# and significant bits, which do not compress. A checker that verified a copy against the weights and then
# computed on it in free arithmetic is the cheat the budget blocks. Where the share decides the budget, a
# checker holds at most half of weight_bits, so a copy measures at least twice the budget, and a quantity
# that needs tensors holding more than half the bits stays out of reach: in the zoo's attention networks the
# embedding and unembedding, which every logit needs, hold 47 to 79% of the bits, and where the share decides
# the budget (v24, v64d8) a copy of both leaves under 700 units for the checker's code, or none. The base
# decides it on small networks (attention at v16, E = 544), where an honest checker is about as large as the
# weights: there it stays 8192 + 4 E, as up to v10 (on the tiny network, E = 80, the weights are smaller than
# any checker and the budget separates nothing). The cap keeps the share from raising the budget of a large
# network, where the base already exceeds every honest checker so far (the largest measured 14,043) and half a
# copy would mostly be room for a partial copy. scripts/test_accept.py checks the arithmetic on every exported
# network of the zoo. The environment variables are hooks for tests; whatever is in force is in the policy
# digest and the receipt.
# A planned checker's plan is free and untrusted (the soundness theorem holds for every plan), and bounded as the
# fixed rules lane bounds its plan, the proof file's tree (core/check/checker.py: 4 nodes per input plus 10,000):
# at most PLAN_PER_INPUT entries per input of the domain plus PLAN_BASE, each below 2^PLAN_ENTRY_BITS, so that it
# holds indices and counts, as a plan does. Turning an entry into a number for arithmetic goes through `I.lit`,
# charged 1, as reading a certificate number is. A plan's entries are plain numbers that the checker may compute
# on for free, so the plan is bounded in information as well (policy v12): plan_bits, its length in a prefix
# code, is at most PLAN_BITS_SHARE of weight_bits. A plan that carried a copy of the weights (checked against
# them at about one charged operation per weight, then computed on for free) would hold at least weight_bits.
PLAN_PER_INPUT = 4
PLAN_BASE = 10_000
PLAN_ENTRY_BITS = 32
PLAN_BITS_SHARE = Fraction(os.environ.get("ACCEPT_PLAN_BITS_SHARE", "1/4"))  # of weight_bits
SIZE_BUDGET_BASE = int(os.environ.get("ACCEPT_SIZE_BUDGET_BASE", 8192))
SIZE_BUDGET_PER_PARAM = int(os.environ.get("ACCEPT_SIZE_BUDGET_PER_PARAM", 4))
SIZE_BUDGET_SHARE = Fraction(os.environ.get("ACCEPT_SIZE_BUDGET_SHARE", "1/2"))  # of weight_bits
SIZE_BUDGET_SHARE_CAP = int(os.environ.get("ACCEPT_SIZE_BUDGET_SHARE_CAP", 16384))
# No budget is above this (policy v14): 1.75 times the largest real checker measured (14,043, run
# attn-min2-ptl-1) and above the budget of every network that has a proof (the largest 15,563). It decides from
# 4,097 parameters on; before, a network of 8,256 parameters had 41,216 and one of 12,352 had 57,600.
SIZE_BUDGET_CAP = int(os.environ.get("ACCEPT_SIZE_BUDGET_CAP", 24576))
# The last-bits test (policy v14). Each copy moves every nonzero parameter by about 2^-level of itself (at least
# one unit of its tensor's last place), up or down; float32 weights have 24 significant bits, so levels 20 and 16
# change their last 4 and 8. LEVELS decide: on every copy at these levels the checker must certify at least KEEP
# of what it certifies on the network. RECORDED are run for the record only (how far the count holds), since a
# real checker's certificate and plan were made for the network and stop fitting at some distance from it.
# Measured on run attn-min2-ptl-3's proof (1,889 inputs): 1,889 on every copy down to level 12, then 0 and 1,763
# at level 8. On examples/open_lane/max2_tiny_stored_weight: 0 on every copy.
LAST_BITS_LEVELS = (20, 16)
LAST_BITS_RECORDED = (12, 8)
LAST_BITS_COPIES = 2
LAST_BITS_KEEP = Fraction(os.environ.get("ACCEPT_LAST_BITS_KEEP", "9/10"))
PREVIEW_LAST_BITS_S = int(os.environ.get("ACCEPT_PREVIEW_LAST_BITS_S", 120))  # the most a development preview gives the runs
GENERAL_KERNEL_BUDGET_MS = 120_000  # kernel time to replay the general layer


def weight_bits(net: dict) -> int:
    """The least a copy of the network's parameters holds however it is written: for each weight its sign and
    its significant bits, from its highest to its lowest nonzero bit (the exporter's integer over the tensor's
    common exponent, whose trailing zeros carry nothing); 1 for a zero weight. Not counted, so that this stays
    below any copy: where each weight's bits sit (its exponent), which a copy needs too. On the zoo the
    significant bits do not compress (lzma, bz2 and zlib save under 1%) and the signs are balanced (16
    November 2026). The `#const` weights are left out, as extraction_cost leaves them out."""
    def bits(v: int) -> int:
        v = abs(v)
        return 1 + (v >> ((v & -v).bit_length() - 1)).bit_length() if v else 1
    return sum(bits(v) for w in net["weights"] if not w["name"].startswith("#const") for v in w["ints"])


def size_budget(extract: int, bits: int) -> int:
    """The description-size budget of a network with `extract` parameters and `bits` = weight_bits."""
    return min(SIZE_BUDGET_CAP, max(SIZE_BUDGET_BASE + SIZE_BUDGET_PER_PARAM * extract,
                                    min(math.floor(SIZE_BUDGET_SHARE * bits), SIZE_BUDGET_SHARE_CAP)))


def plan_bits(plan: list) -> int:
    """The length of a plan in a prefix code (Elias gamma of each entry plus one: 2 * bitlength - 1 bits, so 0
    costs 1, 1 and 2 cost 3, 63 costs 13). The entries can be read back from the code, so a plan that holds b
    bits of information measures at least b."""
    return sum(2 * (v + 1).bit_length() - 1 for v in plan)


def plan_bits_budget(bits: int) -> int:
    """The most a plan may measure on a network with `bits` = weight_bits."""
    return math.floor(PLAN_BITS_SHARE * bits)


def plan_problem(plan: list, domain: int, bits: int) -> str | None:
    """Why a plan is over its bounds on a network with `bits` = weight_bits, or None."""
    cap = PLAN_PER_INPUT * domain + PLAN_BASE
    if len(plan) > cap:
        return f"the plan has {len(plan)} entries, more than {cap} ({PLAN_PER_INPUT} per input plus {PLAN_BASE})"
    big = next((i for i, v in enumerate(plan) if v >= 1 << PLAN_ENTRY_BITS), None)
    if big is not None:
        return f"plan entry {big} is {plan[big]}, not below 2^{PLAN_ENTRY_BITS}"
    held, most = plan_bits(plan), plan_bits_budget(bits)
    if held > most:
        return (f"the plan holds {held} bits (its length in a prefix code), more than {most}: "
                f"{PLAN_BITS_SHARE} of the {bits} bits a copy of the weights holds at least")
    return None


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
        out = exc.stdout or ""
        return {"rc": -9, "stdout": out.decode(errors="replace") if isinstance(out, bytes) else out,
                "stderr": "timed out", "timed_out": True, "seconds": round(time.time() - t0, 1)}
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
                   timeout_s: float = COMPILE_TIMEOUT_S, kernel: bool = True) -> dict:
    """Compile one module whose source is src (module name relative to root) into ws/out. kernel=False skips
    the kernel's check of each declaration as Lean adds it (debug.skipKernelTC): only for a submission, whose
    every constant acceptcheck replays through the kernel afterwards, the check that counts."""
    out = ws / "out" / (module.replace(".", "/") + ".olean")
    out.parent.mkdir(parents=True, exist_ok=True)
    env = box_env(ws, lean, lp)
    # Elaboration in one thread: with asynchronous elaboration (Lean's default) every theorem of a module is a
    # task, and a module of many theorems (an instance split into one decided fact per input) makes Lean start
    # threads whose stacks reserve more address space than any limit the box can set (64 GB was not enough for
    # 64 facts; the process reserved about 77 GB unlimited). Sequential elaboration builds the same constants.
    cmd = [str(lean), "-DElab.async=false"] + ([] if kernel else ["-Ddebug.skipKernelTC=true"]) + \
        ["-R", str(root), "-o", str(out), str(src)]
    res = run_boxed(ws, cmd, env, mode, timeout_s, [str(toolchain_root(lean)), str(LEAN_PROJECT)] + lp)
    res["module"] = module
    res["olean"] = str(out)
    return res


def check_imports(text: str, module: str, modules: set[str], protected: list[str]) -> list[str]:
    """The module's imports, each checked against the allowlist (`protected`: the submission's protected
    modules, the network's and the claim's among them). Imports must come first, as in Lean."""
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
        elif name in protected or name.startswith(TRUSTED_PREFIXES):
            pass
        else:
            raise Reject(f"{module} imports {name}; allowed: the submitted Candidate modules, {', '.join(protected)}, "
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
    run = None
    if isinstance(m.get("scored"), dict):
        run = m["scored"].setdefault("run", "kernel")
        if run not in RUNS:
            raise Reject(f"scored.run must be one of {RUNS}")
    if run == "compiled":
        # the candidate proves soundness and claims no count: the service runs the checker (policy v15). The
        # theorem the kernel is asked for is the soundness theorem.
        if not isinstance(m["scored"].get("sound"), str):
            raise Reject("scored.sound must be a constant name")
        if m.get("theorem", m["scored"]["sound"]) != m["scored"]["sound"]:
            raise Reject("with scored.run compiled the theorem is scored.sound, or is left out")
        for key in ("instance", "claimed_bill"):
            if key in m["scored"]:
                raise Reject(f"with scored.run compiled there is no scored.{key}: the service runs the checker itself")
        # claimed_count then claims nothing: as for a lemma, it names the claim's protected module, which modules
        # written for a kernel instance import (0 when left out; a module can import the network's own instead)
        m.update(theorem=m["scored"]["sound"], claimed_count=m.get("claimed_count", 0))
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
        if m["kind"] != "performance":
            raise Reject("only a performance submission can be scored")
        for key in ("checker", "sound") + (("instance",) if s["run"] == "kernel" else ()):
            v = s.get(key)
            if not isinstance(v, str):
                raise Reject(f"scored.{key} must be a constant name")
            ps = v.split(".")
            if len(ps) < 2 or ps[0] != "Candidate" or not all(IDENT.match(x) for x in ps):
                raise Reject(f"scored.{key} must be a name under Candidate., made of identifiers")
        b = s.get("claimed_bill")
        if s["run"] == "kernel" and (not isinstance(b, int) or isinstance(b, bool) or b < 0):
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
        if "plan" in s:  # a planned checker; its size is checked when scoring (plan_problem)
            try:
                s["plan"] = make_protected.canonical_plan(s["plan"])
            except make_protected.ProtectedError as exc:
                raise Reject(f"scored.plan: {exc}")
    return m


# ---- the protected module ---------------------------------------------------------------------------
def build_protected(net_json: Path, claimed: int, work: Path, lean: Path, lp: list[str], mode: str,
                    cert: list | None = None, plan: list | None = None) -> dict:
    """Write, compile and verify the protected modules (scripts/make_protected.py): the claim's, which is the
    trusted one and is checked against the network file, and beside it the network's, the certificate's and the
    plan's when there are any, which hold the same definitions under names that do not change with the claim.
    Each of those three is compiled once, in a folder of its own, and cached by content; the claim's folder gets
    a copy of their object files beside its own, because Lean looks for every module of `Protected` in the first
    folder of its search path that has that package. So one folder (lean_path_dir) holds all a candidate may
    import, and a candidate's module that imports the network's module alone stays compiled when the claim
    changes. Returns {module, olean, lean_path_dir: the claim module's; modules: every module's name;
    network_module; cached; domain}. With a plan (a planned checker's), the claim's module also has `plan`."""
    sys.path.insert(0, str(HERE))
    try:
        import make_protected
    finally:
        sys.path.pop(0)
    net = json.loads(net_json.read_text())
    try:
        parts = make_protected.render_all(net, claimed, cert, plan)
    except make_protected.ProtectedError as exc:
        if "not supported" in str(exc):
            raise Unsupported(str(exc))
        raise Reject(str(exc))
    pdir = work / "protected"
    names = [f"Protected.{name}" for name, _ in parts]
    name, src = parts[-1]
    ws = pdir / name
    olean = ws / "out" / "Protected" / f"{name}.olean"
    stamp = ws / "verified.json"
    out = {"module": names[-1], "olean": str(olean), "lean_path_dir": str(ws / "out"), "lean_path_dirs": [str(ws / "out")],
           "modules": names, "network_module": names[0]}
    # the stamp is of every module's source: the folder is rebuilt when any of them changes
    key = sha256_text("\n".join(text for _, text in parts))
    if olean.exists() and stamp.exists() and json.loads(stamp.read_text()).get("source_sha256") == key:
        return {**out, "cached": True, "domain": json.loads(stamp.read_text())["domain"]}

    def compiled(dws: Path, dname: str, dsrc: str) -> None:
        srcp = dws / "Protected" / f"{dname}.lean"
        srcp.parent.mkdir(parents=True, exist_ok=True)
        srcp.write_text(dsrc)
        res = compile_module(dws, dws, f"Protected.{dname}", srcp, lean, lp, mode)
        if res["timed_out"]:
            raise Infra(f"compiling the protected module Protected.{dname} timed out")
        if res["rc"] != 0:
            raise Infra(f"the protected module Protected.{dname} does not compile: {res['stdout'][-1500:]}{res['stderr'][-500:]}")

    parts_dir = pdir / "parts"  # the modules that do not change with the claim, each compiled once
    ready = []
    for dname, dsrc in parts[:-1]:
        dws = parts_dir / dname
        dolean = dws / "out" / "Protected" / f"{dname}.olean"
        dstamp = dws / "compiled.json"
        if not (dolean.exists() and dstamp.exists() and json.loads(dstamp.read_text()).get("source_sha256") == sha256_text(dsrc)):
            shutil.rmtree(dws, ignore_errors=True)
            compiled(dws, dname, dsrc)
            dstamp.write_text(json.dumps({"source_sha256": sha256_text(dsrc)}))
        ready.append((dname, dolean))
    shutil.rmtree(ws, ignore_errors=True)
    (ws / "out" / "Protected").mkdir(parents=True)
    for dname, dolean in ready:
        shutil.copyfile(dolean, ws / "out" / "Protected" / f"{dname}.olean")
        (ws / "Protected").mkdir(exist_ok=True)
        shutil.copyfile(dolean.parents[2] / "Protected" / f"{dname}.lean", ws / "Protected" / f"{dname}.lean")
    (ws / "cert.json").write_text(json.dumps(cert or []))
    if plan is not None:
        (ws / "plan.json").write_text(json.dumps(plan))
    compiled(ws, name, src)
    env = box_env(ws, lean, lp)
    chk = run_boxed(ws, [str(acceptcheck_binary()), "protected", str(net_json), names[-1], str(olean)], env, mode,
                    CHECK_TIMEOUT_S, [str(toolchain_root(lean)), str(LEAN_PROJECT), str(net_json)])
    last = last_json(chk["stdout"])
    if chk["rc"] != 0 or not last or last.get("status") != "ok":
        raise Infra(f"the protected module does not match the network file: {last or chk['stderr'][-800:]}")
    stamp.write_text(json.dumps({"source_sha256": key, "domain": last["domain"], "network": last["network"]}))
    return {**out, "cached": False, "domain": last["domain"]}


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
               "score_eligible": False, "execution_assurance": None, "run": None, "cost_model": COST_MODEL,
               "policy_version": POLICY_VERSION, "knowledge": KNOWLEDGE,
               "scoring": {"status": "not_requested"},
               "seconds": None, "time": time.strftime("%Y-%m-%dT%H:%M:%S%z")}
    ws = None
    try:
        manifest = read_manifest(cdir)
        run = (manifest.get("scored") or {}).get("run")  # "kernel", "compiled", or None for a proof that is not scored
        receipt.update(candidate_id=manifest["candidate_id"], network=manifest["network"], theorem=manifest["theorem"],
                       claim_kind=manifest["kind"], run=run,
                       claimed_count=manifest["claimed_count"] if manifest["kind"] == "performance" and run != "compiled" else None)
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
                               scored["certificate"] if scored else None, scored.get("plan") if scored else None)
        receipt["domain_size"] = prot["domain"]
        receipt["steps"].append({"step": "protected", "module": prot["module"], "network_module": prot["network_module"],
                                 "cached": prot["cached"]})
        deps = {m: check_imports(p.read_text(), m, set(modules), prot["modules"]) for m, p in modules.items()}
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
        lp_all = lp + prot["lean_path_dirs"]
        oleans = []
        for m in order:
            # without the kernel's check here: acceptcheck replays every constant through the kernel below, and an
            # instance of many decided facts was checked three times before (compile, check, score)
            res = compile_module(ws, ws, m, ws / (m.replace(".", "/") + ".lean"), lean, lp_all, mode, kernel=False)
            receipt["steps"].append({"step": "compile", "module": m, "rc": res["rc"], "seconds": res["seconds"],
                                     "timed_out": res["timed_out"], "kernel": False})
            if res["timed_out"]:
                receipt.update(status="timeout", reason=f"compiling {m} exceeded {COMPILE_TIMEOUT_S} s")
                return finish(receipt, work, t0)
            if res["rc"] != 0:
                raise Reject(f"{m} does not compile: {excerpt(res['stdout'] + res['stderr'])}")
            oleans.append(res["olean"])
        # the kernel: one replay of every constant, which verifies and, for a scored proof, scores
        trusted = [prot["module"]] + sorted({d for ds in deps.values() for d in ds if not d.startswith("Candidate.")})
        env = box_env(ws, lean, lp_all)
        scoring = None  # a scored proof: what scoring finds before the kernel (score_before_kernel)
        if manifest["kind"] == "auxiliary":
            cmd = [str(acceptcheck_binary()), "lemma", manifest["theorem"]] + trusted + ["--"] + oleans
        elif run == "compiled":
            # soundness alone goes to the kernel; the run on the network is made below, compiled
            scoring = score_before_kernel(scored, prot, net_json, trusted, oleans, ws, env, mode, lean, lp_all, receipt)
            cmd = [str(acceptcheck_binary()), "sound" if scored.get("plan") is None else "sound-planned", prot["module"],
                   scored["checker"], scored["sound"]] + trusted + ["--"] + oleans
        else:
            if scored:
                scoring = score_before_kernel(scored, prot, net_json, trusted, oleans, ws, env, mode, lean, lp_all, receipt)
            if scoring is not None and scoring["status"] is None:  # verified and scored in one replay
                cmd = [str(acceptcheck_binary()), "check-score" if scored.get("plan") is None else "check-score-planned",
                       prot["module"] + ".Target", manifest["theorem"], prot["module"], scored["checker"], scored["sound"],
                       scored["instance"], str(manifest["claimed_count"]), str(scored["claimed_bill"])] + trusted + ["--"] + oleans
            else:
                cmd = [str(acceptcheck_binary()), "check", prot["module"] + ".Target", manifest["theorem"]] + trusted + ["--"] + oleans
        chk = run_boxed(ws, cmd, env, mode, CHECK_TIMEOUT_S, [str(toolchain_root(lean)), str(LEAN_PROJECT)] + lp_all)
        receipt["steps"].append({"step": "kernel", "rc": chk["rc"], "seconds": chk["seconds"], "timed_out": chk["timed_out"],
                                 "scores": cmd[1].startswith(("check-score", "sound"))})
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
        if run == "compiled":
            # the run: the compiled checker on the network, and on the last-bits copies in the same process
            res = last_bits_runs(scored["checker"], scored.get("plan") is not None, prot, net_json, list(zip(order, oleans)),
                                 ws, env, mode, lean, lp_all, work)
            receipt["steps"].append({"step": "run", "rc": res["rc"], "seconds": res["seconds"],
                                     "timed_out": res["timed_out"], "status": res["status"]})
            if res["status"] == "error":
                raise Infra(f"acceptcheck probe failed: {res['reason']}")
            base = res.get("base") or {}  # the run on the network: known also when a later run, on a copy, was stopped
            why = run_problem(res, "The service")
            if why is None and base.get("count") is None:
                why = "the checker returns nothing on the network (its run fails), so it certifies no count"
            if why and base.get("count") is None:
                raise Reject(why)  # soundness is proved and nothing was run: there is no count to accept
            count, bill = base["count"], base["bill"]  # with `why`: a count, and no score (last_bits_verdict says why)
            receipt.update(status="accepted", certified_count=count, replayed_constants=last.get("replayed"))
            ran = {**scored, "claimed_bill": bill}
            out = score_after_kernel(ran, scoring, last) if scoring["status"] is None else dict(scoring)
            if out.get("measured_bill") is None and out.get("extract") is not None:  # refused before the kernel
                out.update(measured_bill=bill, measured_length=bill + out["extract"] + out["read"])
            if out["status"] == "scored":
                out = last_bits_verdict(ran, out, count, res)
            receipt["scoring"] = out
            if out["status"] == "scored":
                receipt.update(score_eligible=True, execution_assurance=ASSURANCE_RUN)
            return finish(receipt, work, t0)
        receipt.update(status="accepted", certified_count=manifest["claimed_count"],
                       replayed_constants=last.get("replayed"))
        if scored:
            receipt["scoring"] = scoring if scoring["status"] is not None else score_after_kernel(scored, scoring, last.get("scoring"))
            if receipt["scoring"]["status"] == "scored":
                receipt["scoring"] = last_bits(scored, receipt["scoring"], manifest["claimed_count"], prot, net_json,
                                               list(zip(order, oleans)), ws, env, mode, lean, lp_all, work, receipt)
            if receipt["scoring"]["status"] == "scored":
                receipt.update(score_eligible=True, execution_assurance=ASSURANCE)
    except Reject as exc:
        receipt.update(status="rejected", reason=str(exc))
    except Unsupported as exc:
        receipt.update(status="unsupported", reason=str(exc))
    except Infra as exc:
        receipt.update(status="error", reason=str(exc))
    return finish(receipt, work, t0)


def score_before_kernel(scored: dict, prot: dict, net_json: Path, trusted: list[str], oleans: list[str], ws: Path,
                        env: dict, mode: str, lean: Path, lp_all: list[str], receipt: dict) -> dict:
    """The scored path's checks that need no kernel: the network's extraction cost, the plan's bounds and the
    closure check (the checker touches numbers only through the counted primitives). Returns the receipt's
    `scoring` block, refused, or with status None when the kernel's part (score_after_kernel) is to follow.
    Never raises for the candidate's faults."""
    net = json.loads(net_json.read_text())
    extract = extraction_cost(net)
    bits = weight_bits(net)
    read = len(scored["certificate"])
    plan = scored.get("plan")
    out = {"status": None, "reason": None, "cost_model": COST_MODEL, "run": scored.get("run", "kernel"),
           "assurance": ASSURANCE_RUN if scored.get("run") == "compiled" else ASSURANCE,
           "bill": None, "extract": extract, "read": read, "length": None,
           "plan_entries": None if plan is None else len(plan),
           "plan_bits": None if plan is None else plan_bits(plan), "plan_bits_budget": plan_bits_budget(bits),
           "measured_bill": None, "measured_length": None,
           "description_size": None, "weight_bits": bits,
           "size_budget": None if extract is None else size_budget(extract, bits),
           "general_kernel_ms": None, "general_kernel_budget_ms": GENERAL_KERNEL_BUDGET_MS, "rest_kernel_ms": None,
           "last_bits": None, "axioms": None}
    if extract is None:
        # a property of the network, not of the candidate: refused before any check of the candidate's checker
        out.update(status="refused", reason="the network has operations that do not depend on the input and cost "
                   "something; cost-v3 charges them to extract once, which the open lane does not compute yet")
        return out
    if plan is not None:
        why = plan_problem(plan, prot["domain"], bits)
        if why:
            out.update(status="refused", reason=why)
            return out
    read_extra = [str(toolchain_root(lean)), str(LEAN_PROJECT)] + lp_all
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
    return out


def score_after_kernel(scored: dict, out: dict, last: dict | None) -> dict:
    """The scored path's kernel part, from the `scoring` that `acceptcheck check-score` reported with the one
    replay that verified the candidate: the soundness shape and the instance, their axioms, the description
    size and the general layer's kernel time against their budgets, and the length."""
    out = dict(out)
    if not isinstance(last, dict):
        raise Infra("acceptcheck check-score reported no scoring")
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
    # what the kernel verified, whatever the budgets below decide: the bill the instance proves and the length it
    # gives. A proof refused scoring keeps them (no frontier uses them), so its measurement is not lost.
    out.update(measured_bill=scored["claimed_bill"], measured_length=scored["claimed_bill"] + out["extract"] + out["read"])
    if out["description_size"] is None or out["description_size"] > out["size_budget"]:
        out.update(status="refused", reason=f"the checker's description size {out['description_size']} exceeds the budget {out['size_budget']}")
        return out
    if out["general_kernel_ms"] is None or out["general_kernel_ms"] > GENERAL_KERNEL_BUDGET_MS:
        out.update(status="refused", reason=f"replaying the general layer took {out['general_kernel_ms']} ms, over the budget {GENERAL_KERNEL_BUDGET_MS} ms")
        return out
    # the length, in cost-v3 units
    out.update(status="scored", bill=scored["claimed_bill"], length=scored["claimed_bill"] + out["extract"] + out["read"])
    return out


def last_bits_copy(net: dict, level: int, i: int) -> dict:
    """Copy `i` of a network file at a level: every nonzero parameter moved by about 2^-level of itself, at least
    one unit of its tensor's last place, up or down (by a generator seeded with the network, the level and i, so
    the copies of a network are the same on every machine). Zeros stay zeros, and the exporter's `#const`
    tensors stay: they are constants of the model's code, not parameters. Nothing here knows the architecture."""
    out = json.loads(json.dumps(net))
    rng = random.Random(int(hashlib.sha256(f"last-bits|{net['network']}|{level}|{i}".encode()).hexdigest(), 16))
    for w in out["weights"]:
        if not w["name"].startswith("#const"):
            w["ints"] = [m if m == 0 else m + rng.choice((-1, 1)) * max(1, abs(m) >> level) for m in w["ints"]]
    return out


def last_bits_files(net_json: Path, work: Path) -> list[tuple[int, Path]]:
    """The copies of a network for the last-bits test, written once under <work>/last_bits: (level, file), the
    deciding levels first."""
    net = json.loads(net_json.read_text())
    folder = work / "last_bits" / net_json.stem
    folder.mkdir(parents=True, exist_ok=True)
    files = []
    for k in LAST_BITS_LEVELS + LAST_BITS_RECORDED:
        for i in range(LAST_BITS_COPIES):
            f = folder / f"k{k}-{i}.json"
            text = json.dumps(last_bits_copy(net, k, i))
            if not f.exists() or f.read_text() != text:
                tmp = folder / f".k{k}-{i}.{os.getpid()}.tmp"  # whole or not there, for a probe reading it meanwhile
                tmp.write_text(text)
                os.replace(tmp, f)
            files.append((k, f))
    return files


def last_bits_runs(checker: str, planned: bool, prot: dict, net_json: Path, modules: list[tuple[str, str]], ws: Path,
                   env: dict, mode: str, lean: Path, lp_all: list[str], work: Path,
                   timeout_s: float = CHECK_TIMEOUT_S) -> dict:
    """Run a compiled checker on the network and on its last-bits copies (`acceptcheck probe`), with the
    certificate and plan of the protected module. Returns a dict with "status", "seconds", "rc", "timed_out" and
      ok          "base": {count, bill}, "counts": [(level, count)]; a run in which the checker fails counts 0
      replaced    "module", "by": a module of the candidate replaces compiled code or runs code when loaded
      uncompiled  "reason": the checker has no compiled code (noncomputable)
      untyped     "reason": the name is not a checker's (its type is not Checker, or List Nat → Checker with a plan)
      stopped     "reason", "done": the checker's own code did not run to the end (a crash, memory, timeout_s),
                  after `done` of the runs; with "base" when the run on the network was among them
      error       "reason": the probe itself could not be run; the service's fault, not the candidate's."""
    files = last_bits_files(net_json, work)
    cmd = [str(acceptcheck_binary()), "probe-planned" if planned else "probe", prot["module"], checker, str(net_json)] + \
        [str(f) for _, f in files] + ["--"] + [f"{m}={o}" for m, o in modules]
    chk = run_boxed(ws, cmd, env, mode, timeout_s,
                    [str(toolchain_root(lean)), str(LEAN_PROJECT), str(net_json), str(files[0][1].parent)] + lp_all)
    out = {"seconds": chk["seconds"], "rc": chk["rc"], "timed_out": chk["timed_out"]}
    lines = []
    for line in chk["stdout"].splitlines():  # one JSON object per line; the last decides (AcceptMain.lean, runProbe)
        if line.startswith("{"):
            try:
                lines.append(json.loads(line))
            except ValueError:
                pass
    last = lines[-1] if lines else {}
    if not chk["timed_out"] and chk["rc"] == 0 and last.get("status") in ("replaced", "uncompiled", "untyped"):
        return {**out, "status": last["status"], "module": last.get("module"), "by": last.get("by"),
                "reason": last.get("reason")}
    runs = last.get("runs") or []
    if not chk["timed_out"] and chk["rc"] == 0 and last.get("status") == "ok" and len(runs) == 1 + len(files):
        return {**out, "status": "ok", "base": runs[0],
                "counts": [(k, int(r.get("count") or 0)) for (k, _), r in zip(files, runs[1:])]}
    if any(d.get("status") == "loaded" for d in lines) and last.get("status") in ("loaded", "run"):
        # everything of the service's was done; the process ended in the candidate's code
        ran = [d for d in lines if d.get("status") == "run"]
        done = max([int(d.get("done") or 0) for d in ran], default=0)
        first = [d for d in ran if d.get("done") == 1 and "count" in d]  # the run on the network, when it was made
        if first:
            out["base"] = {"count": first[0].get("count"), "bill": first[0].get("bill")}
        where = "on the network" if done == 0 else f"on copy {done} of {len(files)}"
        if chk["timed_out"]:
            why = f"did not finish within {timeout_s:.0f} s"
        else:
            said = [l.strip() for l in chk["stderr"].splitlines() if l.strip()]  # Lean's first line says what happened
            why = f"ended without a result (exit code {chk['rc']}" + \
                  (f": {said[0].split(' (potential solution')[0][:300]}" if said else "") + ")"
        return {**out, "status": "stopped", "done": done, "reason": f"its run {where} {why}"}
    if chk["timed_out"]:
        return {**out, "status": "error", "reason": f"the probe did not start its runs within {timeout_s:.0f} s"}
    if not lines:  # not a word of the probe's: a binary built before the probe existed prints its usage here
        return {**out, "status": "error",
                "reason": "acceptcheck gave no answer to `probe` (is it built from this commit? `lake build acceptcheck`): "
                          + (chk["stdout"] + chk["stderr"])[-1200:]}
    return {**out, "status": "error",
            "reason": (last.get("reason") if last.get("status") == "error" else None) or
                      (f"acceptcheck probe answered {str(last)[:600]}" if chk["rc"] == 0 else
                       (chk["stdout"] + chk["stderr"])[-1500:])}


def last_bits_block(count: int, counts: list[tuple[int, int]]) -> tuple[dict, int, int]:
    """The receipt's `last_bits` for a checker that certifies `count` on the network and `counts` on the copies,
    and the deciding copy on which it certifies least: its level and its count."""
    keeps = lambda n: n * LAST_BITS_KEEP.denominator >= count * LAST_BITS_KEEP.numerator
    block = {"levels": list(LAST_BITS_LEVELS), "recorded": list(LAST_BITS_RECORDED), "copies": LAST_BITS_COPIES,
             "keep": str(LAST_BITS_KEEP), "runs": [{"level": k, "count": n} for k, n in counts],
             "least_share": None, "holds_to": None, "passed": None}
    worst_k, worst = min(((k, n) for k, n in counts if k in LAST_BITS_LEVELS), key=lambda kn: kn[1])
    block["least_share"] = round(worst / count, 4) if count else None
    for k in LAST_BITS_LEVELS + LAST_BITS_RECORDED:  # from the finest level: how far every copy keeps the count
        if not all(keeps(n) for kk, n in counts if kk == k):
            break
        block["holds_to"] = k
    block["passed"] = keeps(worst)
    return block, worst_k, worst


REPLACED = ("the module {module} uses `{by}`: it gives a definition other compiled code than its body, or runs code when "
            "it is loaded. {who} runs the checker compiled, and takes it for the checker the kernel knows only where the "
            "two are the same code")
UNCOMPILED = ("the checker has no compiled code to run ({reason}). {who} runs the checker compiled: neither the checker "
              "nor anything it uses may be `noncomputable`")
STOPPED = ("the compiled checker did not run to the end: {reason}. {who} runs the checker compiled, on the network and on "
           "copies of it, each in one run from start to end")


def run_problem(res: dict, who: str) -> str | None:
    """Why the compiled checker gave no runs to go by, in the candidate's terms; None when it ran (status ok).
    `who` runs it: "The last-bits test", or "The service" when the run is the result (scored.run compiled)."""
    if res["status"] == "replaced":
        return REPLACED.format(module=res["module"], by=res["by"], who=who)
    if res["status"] == "uncompiled":
        return UNCOMPILED.format(reason=res["reason"], who=who)
    if res["status"] == "untyped":
        return f"{who} cannot run the checker: {res['reason']}"
    if res["status"] == "stopped":
        return STOPPED.format(reason=res["reason"], who=who)
    return None


def last_bits_verdict(scored: dict, out: dict, count: int, res: dict) -> dict:
    """The last-bits test's answer to the runs of a scored proof's compiled checker (`res`, of last_bits_runs,
    status not error): the scoring block with `last_bits`, refused when the checker could not be run as the
    kernel knows it, when its run on the network is not the count and bill it is scored with, or when a
    deciding copy keeps less than LAST_BITS_KEEP of the count. The measured bill and length are kept."""
    out = dict(out)
    block = {"levels": list(LAST_BITS_LEVELS), "recorded": list(LAST_BITS_RECORDED), "copies": LAST_BITS_COPIES,
             "keep": str(LAST_BITS_KEEP), "runs": None, "least_share": None, "holds_to": None, "passed": False}
    out["last_bits"] = block

    def refuse(reason: str) -> dict:
        out.update(status="refused", reason=reason, bill=None, length=None)
        return out

    why = run_problem(res, "The last-bits test")
    if why:
        return refuse(why)
    base = res["base"]
    if base.get("count") != count or base.get("bill") != scored["claimed_bill"]:
        return refuse(f"the compiled checker gives count {base.get('count')} and bill {base.get('bill')} on the network, "
                      f"where the kernel established {count} and {scored['claimed_bill']}: the last-bits test cannot take it "
                      "for the checker the kernel ran")
    block, worst_k, worst = last_bits_block(count, res["counts"])
    out["last_bits"] = block
    if not block["passed"]:
        return refuse(f"the last-bits test: on a copy of the network whose weights differ by about 2^-{worst_k} of themselves "
                      f"(their last bits) the checker certifies {worst} inputs, where it certifies {count} on the network; at "
                      f"least {LAST_BITS_KEEP} of them are asked for. A count that goes with the last bits of the weights rests "
                      "on comparing the weights with numbers the checker holds, not on what it computes from them. Numbers "
                      "that belong to this network reach a checker through the certificate, and a check on them needs room "
                      "for the weights' last bits")
    return out


def last_bits(scored: dict, out: dict, count: int, prot: dict, net_json: Path, modules: list[tuple[str, str]], ws: Path,
              env: dict, mode: str, lean: Path, lp_all: list[str], work: Path, receipt: dict) -> dict:
    """The last-bits test of a proof the kernel has scored (header, policy v14): the checker, compiled, with the
    proof's certificate and plan, on the network and on copies of it whose weights differ in their last bits.
    Returns the scoring block with `last_bits` added (last_bits_verdict). A probe that could not be run for a
    reason that is not the candidate's is the service's fault and raises Infra, with the receipt's scoring left
    unsettled (status None)."""
    res = last_bits_runs(scored["checker"], scored.get("plan") is not None, prot, net_json, modules, ws, env, mode,
                         lean, lp_all, work)
    receipt["steps"].append({"step": "last_bits", "rc": res["rc"], "seconds": res["seconds"],
                             "timed_out": res["timed_out"], "status": res["status"]})
    if res["status"] == "error":
        # the proof is verified and its scoring is not settled: the receipt must not read as scored
        receipt["scoring"] = {**out, "status": None, "reason": "the last-bits test could not be run", "bill": None,
                              "length": None,
                              "last_bits": {"levels": list(LAST_BITS_LEVELS), "recorded": list(LAST_BITS_RECORDED),
                                            "copies": LAST_BITS_COPIES, "keep": str(LAST_BITS_KEEP), "runs": None,
                                            "least_share": None, "holds_to": None, "passed": None}}
        raise Infra(f"acceptcheck probe failed: {res['reason']}")
    return last_bits_verdict(scored, out, count, res)


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
                         "size_budget": [SIZE_BUDGET_BASE, SIZE_BUDGET_PER_PARAM, str(SIZE_BUDGET_SHARE),
                                         SIZE_BUDGET_SHARE_CAP, SIZE_BUDGET_CAP],
                         "last_bits": [list(LAST_BITS_LEVELS), list(LAST_BITS_RECORDED), LAST_BITS_COPIES, str(LAST_BITS_KEEP)],
                         "runs": list(RUNS),
                         "plan_bounds": [PLAN_PER_INPUT, PLAN_BASE, PLAN_ENTRY_BITS, str(PLAN_BITS_SHARE)],
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


def candidate_imports(ws: Path, module: str) -> tuple[list[str], list[str]]:
    """The workspace modules `module` imports, itself included, transitively (in no particular order), and the
    other modules they import, from the sources' `import` lines."""
    seen, others, stack = [], set(), [module]
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.append(m)
        p = ws / (m.replace(".", "/") + ".lean")
        if not p.is_file():
            continue
        for line in p.read_text().splitlines():
            g = re.match(r"^\s*import\s+(.+)$", line)
            if not g:
                continue
            for name in g.group(1).split():
                if name.startswith("Candidate."):
                    stack.append(name)
                else:
                    others.add(name)
    return seen, sorted(others)


def scoring_preview(ws: Path, module: str, checker: str, prot: dict, net_json: Path, lean: Path, lp: list[str],
                    mode: str, plan: list | None = None, left_s: float | None = None, read: int = 0) -> dict:
    """The scoring checks that need no kernel work, run on a development compile as the score step runs them:
    the counted-language closure of `checker` against the allowlist in force, its description size against
    the budget, with a plan the plan's bits against theirs, and the last-bits test (`last_bits`: what the
    compiled checker certifies on the network, with its bill, and on the copies; given PREVIEW_LAST_BITS_S at
    most, and no more than the call has left when the caller says so with left_s). A preview, not a verdict:
    the submission's score step also has the kernel check the soundness and instance theorems and times the
    general layer. `run`, when the compiled checker gave a count: its count and bill on the network and the
    length they make with a certificate of `read` numbers, which is what a submission with scored.run compiled
    is given (policy v15)."""
    ps = checker.split(".")
    if len(ps) < 2 or ps[0] != "Candidate" or not all(IDENT.match(x) for x in ps):
        return {"error": "the checker must be a constant of the candidate, such as Candidate.MyChecker.D"}
    mods, others = candidate_imports(ws, module)
    oleans = [str(ws / "out" / (m.replace(".", "/") + ".olean")) for m in mods]
    oleans = [o for o in oleans if os.path.isfile(o)]
    trusted = [prot["module"]] + [m for m in others if m != prot["module"]]
    (ws / "tmp").mkdir(exist_ok=True)
    allowlist = ws / "tmp" / "allowlist.txt"
    allowlist.write_text(allowlist_text())
    lp_all = lp + prot["lean_path_dirs"] + [str(ws / "out")]
    cmd = [str(acceptcheck_binary()), "closure", checker, str(allowlist), prot["module"]] + trusted + ["--"] + oleans
    chk = run_boxed(ws, cmd, box_env(ws, lean, lp_all), mode, CHECK_TIMEOUT_S,
                    [str(toolchain_root(lean)), str(LEAN_PROJECT)] + lp_all)
    last = last_json(chk["stdout"])
    if chk["timed_out"] or chk["rc"] != 0 or last is None:
        return {"error": "the closure check failed: " + excerpt(chk["stdout"] + chk["stderr"])}
    net = json.loads(net_json.read_text())
    extract = extraction_cost(net)
    budget = None if extract is None else size_budget(extract, weight_bits(net))
    size = last.get("description_size")
    by = sorted((last.get("size_by") or {}).items(), key=lambda kv: -kv[1])
    out = {"checker": checker,
           "counted_language": last.get("status"), "offending": last.get("offending") or [],
           "description_size": size, "size_budget": budget,
           "within_budget": None if size is None or budget is None else size <= budget,
           "largest_definitions": [{"name": k, "size": v} for k, v in by[:8]]}
    if plan is not None:
        most = plan_bits_budget(weight_bits(net))
        out.update(plan_bits=plan_bits(plan), plan_bits_budget=most, plan_within_budget=plan_bits(plan) <= most)
    if last.get("reason"):
        out["reason"] = last["reason"]
    if last.get("status") == "ok" and _work is not None:
        lb = last_bits_preview(ws, mods, checker, prot, net_json, lean, lp_all, mode, plan is not None, left_s)
        out["last_bits"] = lb
        if lb.get("count") is not None and extract is not None:
            # the compiled checker's run on the network: with scored.run compiled this is the count and the bill a
            # submission is given (policy v15), and the length they make with the certificate as it is now
            out["run"] = {"count": lb["count"], "bill": lb["bill"], "extract": extract, "read": read,
                          "length": lb["bill"] + extract + read}
    return out


def last_bits_preview(ws: Path, mods: list[str], checker: str, prot: dict, net_json: Path, lean: Path, lp_all: list[str],
                      mode: str, planned: bool, left_s: float | None) -> dict:
    """The last-bits test on a development compile, as the score step runs it (policy v14) but for the kernel:
    what the compiled checker certifies on the network (`count`, with its `bill`) and on the copies (`runs`),
    and whether that passes. `passes` is None where nothing can be said: the runs did not fit the time, or the
    checker fails on the network."""
    limit = PREVIEW_LAST_BITS_S if left_s is None else min(PREVIEW_LAST_BITS_S, left_s - 10)
    if limit < 5:
        return {"passes": None, "reason": "not run: this call had no time left for it. The submission's score step runs it"}
    pairs = [(m, str(ws / "out" / (m.replace(".", "/") + ".olean"))) for m in mods]
    res = last_bits_runs(checker, planned, prot, net_json, [(m, o) for m, o in pairs if os.path.isfile(o)], ws,
                         box_env(ws, lean, lp_all), mode, lean, lp_all, _work, timeout_s=limit)
    if res["status"] == "untyped":
        return {"passes": None, "reason": res["reason"]}
    if res["status"] in ("replaced", "uncompiled") or (res["status"] == "stopped" and not res["timed_out"]):
        return {"passes": False, "reason": run_problem(res, "The service")}
    if res["status"] == "stopped":
        base = res.get("base") or {}  # the run on the network, when the time ran out on a copy
        return {"passes": None, **({"count": base.get("count"), "bill": base.get("bill")} if base else {}),
                "reason": f"not run to the end: {res['reason']}, which is what a preview gives the runs on the "
                          f"network and on {len(LAST_BITS_LEVELS + LAST_BITS_RECORDED) * LAST_BITS_COPIES} copies. "
                          "The submission's score step runs them in full"}
    if res["status"] == "error":
        return {"passes": None, "reason": "the test could not be run here: " + excerpt(res["reason"], 600, 300)}
    count = res["base"].get("count")
    if count is None:
        return {"passes": None, "count": None, "bill": None,
                "reason": "the checker fails on the network (it returns nothing), so there is nothing to compare"}
    block, worst_k, worst = last_bits_block(count, res["counts"])
    return {"count": count, "bill": res["base"].get("bill"), "runs": block["runs"], "keep": block["keep"],
            "least_count_on_copies": worst, "holds_to": block["holds_to"], "passes": block["passed"],
            "seconds": res["seconds"]}


def compile_for_development(ws: Path, rel: str, repo: Path, model: str, network: str, claimed: int, work: Path,
                            want_mode: str, cert: list | None = None, checker: str | None = None,
                            plan: list | None = None, limit_s: float | None = None) -> dict:
    """Compile <ws>/<rel> against the protected module of (network, claimed, certificate), in the box, with the
    workspace's own out/ on the path for its other modules. For a candidate's development, never for acceptance:
    returns {"ok", "timed_out", "module", "protected_module", "messages", "seconds"} or {"ok": False, "error"}.
    With `checker` (a constant of the compiled module or the workspace modules it imports) and a successful
    compile, also "scoring_preview" (scoring_preview). limit_s: the seconds the caller gives the whole call, when
    it stops the call from outside; the preview's last-bits runs then take no more than what is left of them."""
    global _repo, _work
    _repo, _work = repo, work
    t0 = time.time()
    if not re.match(r"^Candidate/([A-Za-z_][A-Za-z0-9_]*/)*[A-Za-z_][A-Za-z0-9_]*\.lean$", rel):
        return {"ok": False, "error": "the module path must be Candidate/<Name>.lean"}
    src = ws / rel
    if src.is_symlink() or not src.is_file():
        return {"ok": False, "error": f"{rel} is not a file of the workspace"}
    try:
        mode = box_mode(want_mode)
        lean, lp = lean_binary(), lean_path()
        net_json = export_network(repo, model, network, work)
        prot = build_protected(net_json, claimed, work, lean, lp, mode, cert, plan)
    except (Reject, Unsupported, Infra) as exc:
        return {"ok": False, "error": str(exc)}
    module = "Candidate." + rel[len("Candidate/"):-len(".lean")].replace("/", ".")
    (ws / "out").mkdir(exist_ok=True)
    res = compile_module(ws, ws, module, src, lean, lp + prot["lean_path_dirs"] + [str(ws / "out")], mode)
    text = (res["stdout"] + res["stderr"]).strip()
    ok = res["rc"] == 0 and not res["timed_out"]
    out = {"ok": ok, "timed_out": res["timed_out"], "module": module,
           "protected_module": prot["module"], "network_module": prot["network_module"],
           "protected_modules": prot["modules"], "messages": text, "seconds": round(res["seconds"], 1)}
    if checker and ok:
        try:
            out["scoring_preview"] = scoring_preview(ws, module, checker, prot, net_json, lean, lp, mode, plan,
                                                     None if limit_s is None else limit_s - (time.time() - t0),
                                                     read=len(cert or []))
        except (Reject, Unsupported, Infra) as exc:
            out["scoring_preview"] = {"error": str(exc)}
    return out


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
    c.add_argument("--claimed", type=int, default=0, help="the count a kernel instance will claim (it names the claim's "
                                                          "protected module); 0 when the service runs the checker")
    c.add_argument("--certificate", type=Path)
    c.add_argument("--mode", default="hardened", choices=BOX_MODES)
    c.add_argument("--knowledge", default="minimal", choices=KNOWLEDGE_CONDITIONS)
    c.add_argument("--checker", help="a checker constant: also report the counted-language closure, the "
                                     "description size against the budget and the last-bits test, as scoring would")
    c.add_argument("--limit-s", type=float, help="the seconds the caller gives this whole call, when it stops the call "
                                                 "from outside: the preview's last-bits runs take no more than is left")
    c.add_argument("--plan", type=Path, help="a JSON list of natural numbers: the plan of a planned checker, given to "
                                             "the protected module as `plan`")
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
        plan = None
        if args.plan:
            sys.path.insert(0, str(HERE))
            try:
                import make_protected
            finally:
                sys.path.pop(0)
            try:
                plan = make_protected.canonical_plan(json.loads(args.plan.read_text()))
            except (ValueError, make_protected.ProtectedError) as exc:
                print(json.dumps({"ok": False, "error": f"the plan: {exc}"}, indent=1))
                return 1
        r = compile_for_development(args.workspace.resolve(), args.module, _repo, args.model, args.network, args.claimed,
                                    args.work.resolve(), args.mode, cert, args.checker, plan, args.limit_s)
        print(json.dumps(r, indent=1))
        return 0 if r.get("ok") else 1
    mode = box_mode(args.mode)
    cert = json.loads(args.certificate.read_text()) if args.certificate else None
    r = build_protected(args.network.resolve(), args.claimed, args.work.resolve(), lean_binary(), lean_path(), mode, cert)
    print(json.dumps(r, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
