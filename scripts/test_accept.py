"""Tests of the open lane's acceptance service (scripts/accept.py): the hand-built example is accepted, and
every way a candidate can be wrong is rejected with the right status.

    python3 -m pytest scripts/test_accept.py -v

Needs the Lean project built (`lake build` of the library and `lake build acceptcheck`), the pipeline
repository (REPO below, or the environment variable COMPACT_PROOF_REPO), and its Python environment. Each test
compiles Lean against Mathlib, so the file takes a few minutes. The work folder is kept between tests
(the exported network and the protected module are cached) and deleted at the end.
"""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent
EXAMPLE = PROJECT / "examples" / "open_lane" / "max2_tiny_brute"
SCORED = PROJECT / "examples" / "open_lane" / "max2_tiny_scored"
AGENT = PROJECT / "examples" / "open_lane" / "max2_tiny_agent_cols23"
PORT = PROJECT / "examples" / "open_lane" / "max2_tiny_cols23_v3"
TREE = PROJECT / "examples" / "open_lane" / "max2_tiny_decision_tree"
ATTN = PROJECT / "examples" / "open_lane" / "attn_max2_tiny_scored"
ATTN_TOKENS = PROJECT / "examples" / "open_lane" / "attn_max2_tiny_tokens"
def _agent_repo() -> Path:
    """The agent repository next to this one: Compact-Proof-Agent, or a clone made under its old name."""
    for name in ("Compact-Proof-Agent", "auto-research-compact-proof", "Auto-Research-Compact-Proof"):
        if (PROJECT.parent / name / "core").is_dir():
            return PROJECT.parent / name
    return PROJECT.parent / "Compact-Proof-Agent"


REPO = Path(os.environ.get("COMPACT_PROOF_REPO") or _agent_repo())

pytestmark = pytest.mark.skipif(not (REPO / "core").is_dir(), reason="the pipeline repository is not next to this one")


@pytest.fixture(scope="module")
def work(tmp_path_factory):
    return tmp_path_factory.mktemp("accept-work")


SMALL_BUDGET = {"ACCEPT_SIZE_BUDGET_BASE": "512", "ACCEPT_SIZE_BUDGET_PER_PARAM": "1",
                "ACCEPT_SIZE_BUDGET_SHARE": "0"}  # 592 on the tiny network


def copy_bound(nums: list[int]) -> int:
    """The least any encoding of these numbers can measure: one unit per bit (a numeral or a string; a list
    of booleans or a Church numeral costs at least twice that)."""
    return sum(max(1, abs(v).bit_length()) for v in nums)


def submit(candidate: Path, work: Path, mode: str = "hardened", env: dict | None = None, knowledge: str = "minimal") -> dict:
    """Submit a candidate. With env SMALL_BUDGET the size budget is 592 on the tiny network: the brute-force
    checker (about 370) fits, a copy of its 80 weights (over 1,700) does not. The default budget is
    calibrated for real networks, where the weights outweigh any checker; on the tiny network they do not
    (test_a_copy_of_the_weights_is_refused_under_the_default_policy_on_a_real_network uses the default)."""
    r = subprocess.run([sys.executable, "-B", str(HERE / "accept.py"), "submit", str(candidate), "--repo", str(REPO),
                        "--work", str(work), "--mode", mode, "--knowledge", knowledge], capture_output=True, text=True, timeout=3600,
                       env={**os.environ, **(env or {})})
    assert r.stdout.strip(), r.stderr
    receipt = json.loads(r.stdout)
    assert (r.returncode == 0) == (receipt["status"] == "accepted")
    return receipt


READ_UNFOLDINGS = {"simp only [CostM.weight] at": "rw [CostM.weight_run_eq_ite] at",
                   "simp only [CostM.cert] at": "rw [CostM.cert_run_eq_ite] at"}


def migrate_reads(example: Path, tmp_path: Path) -> Path:
    """A copy of an example kept from an earlier run, with the one step policy v10 changes: its proofs unfolded
    `CostM.weight` (or `CostM.cert`) and split on the old definition's `if`; since v10 a read goes through a
    `ReadTree`, and the old definition is the equation `CostM.weight_run_eq_ite` (`cert_run_eq_ite`). The
    example's own files are left as the agent wrote them; nothing but these unfoldings changes."""
    d = tmp_path / ("migrated-" + example.name)
    if d.exists():
        shutil.rmtree(d)
    shutil.copytree(example, d)
    for p in d.rglob("*.lean"):
        text = p.read_text()
        new = text
        for old, rep in READ_UNFOLDINGS.items():
            new = new.replace(old, rep)
        if new != text:
            p.write_text(new)
    return d


def variant(tmp_path: Path, name: str, lean: str | None = None, manifest: dict | None = None,
            module_path: str = "Candidate/Max2Tiny.lean", base: Path = EXAMPLE) -> Path:
    """A copy of the example with its Lean source or manifest changed."""
    d = tmp_path / name
    shutil.copytree(base, d)
    m = json.loads((d / "manifest.json").read_text())
    if manifest:
        m.update(manifest)
    m["candidate_id"] = name
    (d / "manifest.json").write_text(json.dumps(m))
    if lean is not None:
        p = d / module_path
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(lean)
    return d


SOURCE = (EXAMPLE / "Candidate" / "Max2Tiny.lean").read_text()
SCORED_SOURCE = (SCORED / "Candidate" / "Max2TinyScored.lean").read_text()
NEW_D = "def D : Checker := fun I => countSingles I graph task (allInputs task.space)"
assert NEW_D in SCORED_SOURCE


def scored_variant(tmp_path: Path, name: str, lean: str) -> Path:
    return variant(tmp_path, name, lean=lean, module_path="Candidate/Max2TinyScored.lean", base=SCORED)


def test_the_hand_built_proof_is_accepted(work):
    r = submit(EXAMPLE, work)
    assert r["status"] == "accepted", r["reason"]
    assert r["certified_count"] == 64 and r["domain_size"] == 64
    assert set(r["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}
    assert r["replayed_constants"] >= 4
    assert Path(r["receipt_path"]).exists()
    if sys.platform == "linux":
        assert r["isolation"] == "landlock"


def test_a_claim_above_the_count_is_rejected(work, tmp_path):
    """The network answers all 64 inputs correctly, so no claim above 64 can be proved; the domain has 64
    inputs, so a claim of 65 is rejected before anything is compiled. A claim of 64 made against the
    protected module of another claim is an import that is not allowed."""
    r = submit(variant(tmp_path, "claim-65", manifest={"claimed_count": 65}), work)
    assert r["status"] == "rejected" and "0 to 64" in r["reason"]
    r = submit(variant(tmp_path, "claim-63-mismatch", manifest={"claimed_count": 63}), work)
    assert r["status"] == "rejected" and "imports" in r["reason"]
    # a proof of a count the kernel finds false is rejected by the kernel's replay (one input is fine; D is 64,
    # not 63): a submission is compiled without the kernel's check, so the replay is where it fails
    src = SOURCE.replace("D weights = 64", "D weights = 63").replace("claimedCount = 64 := rfl", "claimedCount = 63 := rfl")
    src = src.replace("_c64", "_c63")
    r = submit(variant(tmp_path, "claim-63-tried", lean=src, manifest={"claimed_count": 63}), work)
    assert r["status"] == "rejected" and "the kernel rejects the candidate" in r["reason"], r["reason"]


def test_sorry_is_rejected(work, tmp_path):
    src = SOURCE.replace("decide +kernel", "sorry")
    r = submit(variant(tmp_path, "sorry", lean=src), work)
    assert r["status"] == "rejected" and "sorryAx" in r["reason"]


def test_native_decide_is_rejected(work, tmp_path):
    src = SOURCE.replace("decide +kernel", "native_decide")
    r = submit(variant(tmp_path, "native", lean=src), work)
    # this toolchain gives native_decide an axiom of its own; either way it is not a standard axiom
    assert r["status"] == "rejected" and "axioms that are not allowed" in r["reason"] and "native" in r["reason"]


def test_a_theorem_of_another_type_is_rejected(work, tmp_path):
    src = SOURCE.replace("theorem performance : Target := by", "theorem performance : True := by\n  trivial\n\ntheorem performance' : Target := by")
    r = submit(variant(tmp_path, "wrong-type", lean=src), work)
    assert r["status"] == "rejected" and "kernel rejects Challenge.proof" in r["reason"]


def test_a_conditional_claim_is_rejected(work, tmp_path):
    src = SOURCE.replace("theorem performance : Target := by", "theorem performance (h : False) : Target := by\n  exact h.elim\n\ntheorem performance' : Target := by")
    r = submit(variant(tmp_path, "conditional", lean=src), work)
    assert r["status"] == "rejected" and "kernel rejects Challenge.proof" in r["reason"]


def test_another_network_cannot_be_imported(work, tmp_path):
    src = SOURCE.replace("import Protected.N_max2_tiny_v8_s0_c64", "import Protected.N_max2_tiny_v8_s1_c64")
    r = submit(variant(tmp_path, "other-network", lean=src), work)
    assert r["status"] == "rejected" and "imports" in r["reason"]


def test_redeclaring_a_trusted_constant_is_rejected(work, tmp_path):
    src = SOURCE.replace("namespace Candidate.Max2Tiny", "theorem CompactCheck.singleOk_correct' : True := trivial\n\nnamespace Candidate.Max2Tiny")
    # a new name in a trusted namespace is allowed; the same name as a trusted constant is not
    r = submit(variant(tmp_path, "new-name", lean=src), work)
    assert r["status"] == "accepted", r["reason"]
    src2 = SOURCE.replace("namespace Candidate.Max2Tiny", "namespace CompactCheck\ntheorem shapeSize_three' : True := trivial\nend CompactCheck\n\nnamespace Candidate.Max2Tiny")
    r = submit(variant(tmp_path, "new-name-2", lean=src2), work)
    assert r["status"] == "accepted", r["reason"]


def _with_module(tmp_path: Path, name: str, rel: str, text: str) -> Path:
    """A copy of the example with one more module, compiled and replayed but not imported by the proof."""
    d = variant(tmp_path, name)
    (d / rel).write_text(text)
    m = json.loads((d / "manifest.json").read_text())
    m["modules"] = [rel] + m["modules"]
    (d / "manifest.json").write_text(json.dumps(m))
    return d


def test_a_copy_of_a_trusted_equation_lemma_is_accepted(work, tmp_path):
    """Lean generates `Tensor.get.eq_1` in whichever module first unfolds `Tensor.get`; trusted modules already
    have it, and a candidate module that unfolds it without importing one of them has its own, identical copy
    (run attn-min2-ptl-1, 12 November 2026, round 3 was refused for this). The copy is left out of the replay."""
    extra = ("import CompactCheck.Tensor\n\nnamespace Candidate.Extra\nopen CompactCheck\n\n"
             "theorem get_eq (t : Tensor Nat) (i : Nat) : t.get i = t.data.getD i 0 := by\n  simp [Tensor.get]\n\n"
             "end Candidate.Extra\n")
    r = submit(_with_module(tmp_path, "eq-lemma-copy", "Candidate/Extra.lean", extra), work)
    assert r["status"] == "accepted", r["reason"]
    assert r["certified_count"] == 64


def test_a_trusted_name_with_another_statement_is_rejected(work, tmp_path):
    """Only an identical theorem passes: a module that does not import `singleOk_correct` can declare that name
    with any statement, and the service refuses it."""
    fake = ("import CompactCheck.Tensor\n\ntheorem CompactCheck.singleOk_correct : True := trivial\n")
    r = submit(_with_module(tmp_path, "trusted-name", "Candidate/Fake.lean", fake), work)
    assert r["status"] == "rejected" and "redeclares CompactCheck.singleOk_correct" in r["reason"], r["reason"]


def test_a_macro_cannot_change_the_challenge(work, tmp_path):
    hijack = (
        "\nopen Lean Elab Command in\n"
        "macro_rules | `(theorem $n:ident : $t := $p) => `(theorem $n : True := trivial)\n"
    )
    src = SOURCE.replace("theorem performance : Target := by", "theorem performance : Target := by\n  trivial\n  done\n\ntheorem performance' : Target := by")
    r = submit(variant(tmp_path, "macro", lean=src + hijack), work)
    assert r["status"] == "rejected"


def test_bad_manifests_are_rejected(work, tmp_path):
    for name, change, text in (
        ("string-count", {"claimed_count": "63"}, "natural number"),
        ("negative-count", {"claimed_count": -1}, "natural number"),
        ("bool-count", {"claimed_count": True}, "natural number"),
        ("theorem-outside", {"theorem": "Mathlib.performance"}, "under Candidate."),
        ("module-outside", {"modules": ["Other/X.lean"]}, "Candidate/<Name>.lean"),
    ):
        r = submit(variant(tmp_path, name, manifest=change), work)
        assert r["status"] == "rejected" and text in r["reason"], (name, r["reason"])


@pytest.mark.skipif(sys.platform != "linux", reason="Landlock is Linux only")
def test_the_box_blocks_writes_outside_it(work, tmp_path):
    target = work / "receipts" / "forged.json"
    src = SOURCE.replace("namespace Candidate.Max2Tiny",
                         f'#eval IO.FS.writeFile "{target}" "{{}}"\n\nnamespace Candidate.Max2Tiny')
    r = submit(variant(tmp_path, "writer", lean=src), work)
    assert r["status"] == "rejected" and "does not compile" in r["reason"]
    assert not target.exists()


def test_a_tampered_protected_module_is_caught(work, tmp_path):
    """`acceptcheck protected` compares the claim's module with the network file: a changed weight is a mismatch.
    The claim's module is the trusted one, and it holds its constants itself, in the text it always had; the
    network's own module (17 November 2026) holds the same definitions for a candidate's modules to import."""
    sys.path.insert(0, str(HERE))
    import accept
    import make_protected
    sys.path.pop(0)
    accept._repo = REPO
    net_json = accept.export_network(REPO, "tests/max2_tiny", "max2_tiny-v8-s0", work)
    net = json.loads(net_json.read_text())
    name, src = make_protected.render(net, 64)
    (net_name, net_src), (claim_name, claim_src) = make_protected.render_all(net, 64)
    assert net_name == "N_max2_tiny_v8_s0" and (claim_name, claim_src) == (name, src) and "import Protected" not in src
    block = src[src.index("/-- The network's graph"):src.index("/-- The certificate")]
    assert "dyadic 1505767040" in block and block in net_src  # the same definitions, text for text
    bad = src.replace("dyadic 1505767040", "dyadic 1505767041", 1)
    assert bad != src
    ws = tmp_path / "tampered"
    (ws / "Protected").mkdir(parents=True)
    (ws / "Protected" / f"{name}.lean").write_text(bad)
    lean, lp = accept.lean_binary(), accept.lean_path()
    mode = accept.box_mode("hardened")
    res = accept.compile_module(ws, ws, f"Protected.{name}", ws / "Protected" / f"{name}.lean", lean, lp, mode)
    assert res["rc"] == 0, res["stdout"][-500:]
    env = accept.box_env(ws, lean, lp)
    chk = accept.run_boxed(ws, [str(accept.acceptcheck_binary()), "protected", str(net_json), f"Protected.{name}",
                                res["olean"]], env, mode, 600, [str(accept.toolchain_root(lean)), str(PROJECT), str(net_json)])
    last = accept.last_json(chk["stdout"])
    assert last and last["status"] == "mismatch" and "weights" in last["reason"], chk


# ---- the scored path (docs/COUNTED.md) ------------------------------------------------------------------
def test_the_scored_proof_is_verified_and_scored(work):
    r = submit(SCORED, work)
    assert r["status"] == "accepted", r["reason"]
    s = r["scoring"]
    assert s["status"] == "scored", s["reason"]
    assert s["bill"] == 64 * 63 and s["read"] == 0 and s["extract"] == 80
    assert s["length"] == s["bill"] + s["extract"] + s["read"]
    assert s["measured_bill"] == s["bill"] and s["measured_length"] == s["length"]  # what the kernel verified
    assert s["description_size"] <= s["size_budget"] and s["general_kernel_ms"] <= s["general_kernel_budget_ms"]
    assert set(s["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}
    # one replay verifies and scores (check-score), after the closure check, which needs none; the last-bits test
    # follows it, on compiled code (policy v14)
    assert [x["step"] for x in r["steps"]] == ["protected", "compile", "closure", "kernel", "last_bits"]
    assert [x["scores"] for x in r["steps"] if x["step"] == "kernel"] == [True]
    assert all(x["kernel"] is False for x in r["steps"] if x["step"] == "compile")


FALSE_FACT = ("namespace Candidate.False\n\ntheorem five : 2 + 2 = 5 := by decide +kernel\n\n"
              "end Candidate.False\n")


def test_a_submission_compiles_without_the_kernel_and_the_replay_is_the_check(work, tmp_path):
    """A false fact decided by the kernel: a development compile refuses it (the kernel checks there), a
    submission's compile does not check it (debug.skipKernelTC), and the replay rejects the submission. So the
    one check that counts is acceptcheck's, as before; the compile only stopped doing it twice."""
    ws = tmp_path / "ws"
    (ws / "Candidate").mkdir(parents=True)
    (ws / "Candidate" / "False.lean").write_text(FALSE_FACT)
    cmd = [sys.executable, "-B", str(HERE / "accept.py"), "compile", str(ws), "Candidate/False.lean", "--repo", str(REPO),
           "--work", str(work), "--model", "tests/max2_tiny", "--network", "max2_tiny-v8-s0", "--claimed", "64"]
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=1800)
    out = json.loads(r.stdout)
    assert r.returncode == 1 and out["ok"] is False and "error" in out["messages"].lower(), out
    d = _with_module(tmp_path, "false-fact", "Candidate/False.lean", FALSE_FACT)
    m = json.loads((d / "manifest.json").read_text())
    m.update(kind="auxiliary", theorem="Candidate.False.five")
    (d / "manifest.json").write_text(json.dumps(m))
    r = submit(d, work)
    compiled = [x for x in r["steps"] if x["step"] == "compile" and x["module"] == "Candidate.False"]
    assert compiled and compiled[0]["rc"] == 0 and compiled[0]["kernel"] is False
    assert r["status"] == "rejected" and "the kernel rejects the candidate" in r["reason"], r["reason"]


def test_one_replay_scores_as_check_then_score_did(work):
    """check-score's verdicts and measures on the scored example are check's and score's, run apart."""
    r = submit(SCORED, work)
    ws = max((work / "submissions").glob(f"{r['candidate_id']}-*"), key=lambda p: p.stat().st_mtime)
    oleans = sorted(str(p) for p in (ws / "out" / "Candidate").rglob("*.olean"))
    prot = next(x["module"] for x in r["steps"] if x["step"] == "protected")
    m = json.loads((SCORED / "manifest.json").read_text())
    sc = m["scored"]
    accept = _accept_module()
    accept._repo, accept._work = REPO, work
    lean, lp = accept.lean_binary(), accept.lean_path()
    lp_all = lp + [str(work / "protected" / prot.split(".", 1)[1] / "out")]
    env = accept.box_env(ws, lean, lp_all)
    source = (SCORED / "Candidate" / "Max2TinyScored.lean").read_text()
    trusted = [prot] + sorted({line.split()[1] for line in source.splitlines() if line.startswith("import ")
                               and not line.split()[1].startswith(("Candidate.", "Protected."))})

    def run(*args):
        chk = accept.run_boxed(ws, [str(accept.acceptcheck_binary()), *args, *trusted, "--", *oleans], env,
                               accept.box_mode("hardened"), 1800, [str(accept.toolchain_root(lean)), str(PROJECT)] + lp_all)
        return accept.last_json(chk["stdout"])

    check = run("check", f"{prot}.Target", m["theorem"])
    score = run("score", prot, sc["checker"], sc["sound"], sc["instance"], str(m["claimed_count"]), str(sc["claimed_bill"]))
    both = run("check-score", f"{prot}.Target", m["theorem"], prot, sc["checker"], sc["sound"], sc["instance"],
               str(m["claimed_count"]), str(sc["claimed_bill"]))
    assert check["status"] == both["status"] == "accepted" and check["axioms"] == both["axioms"]
    assert check["replayed"] == both["replayed"]
    s = both["scoring"]
    assert s["status"] == score["status"] == "accepted" and s["axioms"] == score["axioms"]
    for part, key in (("general", "description_size"), ("general", "constants"), ("general", "checker_constants"), ("rest", "constants")):
        assert s[part][key] == score[part][key], (part, key)
    # a wrong bill: verified, scoring refused with score's reason
    wrong = run("check-score", f"{prot}.Target", m["theorem"], prot, sc["checker"], sc["sound"], sc["instance"],
                str(m["claimed_count"]), str(sc["claimed_bill"] + 1))
    assert wrong["status"] == "accepted" and wrong["scoring"]["status"] == "rejected"
    assert "Challenge.instance" in wrong["scoring"]["reason"]


def test_a_wrong_bill_is_refused_scoring(work, tmp_path):
    """The instance theorem states the exact bill; the service asks for the manifest's. The kernel's rejection
    of the mismatched statement refuses scoring, and the proof stays verified."""
    d = variant(tmp_path, "wrong-bill", module_path="Candidate/Max2TinyScored.lean", base=SCORED)
    m = json.loads((d / "manifest.json").read_text())
    m["scored"]["claimed_bill"] = 4031
    (d / "manifest.json").write_text(json.dumps(m))
    r = submit(d, work)
    assert r["status"] == "accepted" and r["certified_count"] == 64
    assert r["scoring"]["status"] == "refused" and "Challenge.instance" in r["scoring"]["reason"]


def test_a_checker_that_trusts_the_certificate_is_rejected_with_its_sorry(work, tmp_path):
    """`D` returns the certificate's size as the count: its soundness theorem is false in general, so the
    candidate can only `sorry` it, and the whole submission is rejected (the target's proof uses it)."""
    src = SCORED_SOURCE.replace(NEW_D, "def D : Checker := fun I => do\n  let n ← I.certSize\n  pure (I.nofNat n)")
    src = src.replace("  intro w c n cost h\n  unfold numCorrect\n  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h", "  sorry")
    src = src.replace("some (64, 64 * 63)", "some (0, 0)").replace("exact D_sound weights cert 64 cost h", "sorry")
    r = submit(scored_variant(tmp_path, "trusts-cert", src), work)
    assert r["status"] == "rejected" and "sorryAx" in r["reason"]


def test_the_general_layer_may_not_touch_the_weights_not_proving_anti_hiding(work, tmp_path):
    """A checker that looks at the protected weights directly is outside the counted language, and the
    service says which constant it uses. This checks eligibility, not the anti-hiding property."""
    src = SCORED_SOURCE.replace(NEW_D, "def D : Checker := fun I => countSingles I graph task (if weights.length = 0 then [] else allInputs task.space)")
    src = src.replace("  intro w c n cost h\n  unfold numCorrect\n  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h",
                      "  intro w c n cost h\n  unfold numCorrect\n  simp only [D] at h\n  rw [if_neg (by decide : ¬ weights.length = 0)] at h\n  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h")
    r = submit(scored_variant(tmp_path, "uses-weights", src), work)
    assert r["status"] == "accepted", r["reason"]
    s = r["scoring"]
    assert s["status"] == "refused" and "weights" in s["reason"], s
    # the same for the weights of the network's own module (the same definition under a name no claim changes):
    # only a protected module's graph and task are the general layer's to use
    first = "import Protected.N_max2_tiny_v8_s0_c64\n"
    assert "weights.length" in src and src.startswith(first)
    other = "import Protected.N_max2_tiny_v8_s0\n" + src.replace("weights.length", "Protected.N_max2_tiny_v8_s0.weights.length")
    r = submit(scored_variant(tmp_path, "uses-network-weights", other), work)
    assert r["status"] == "accepted", r["reason"]
    s = r["scoring"]
    assert s["status"] == "refused" and "Protected.N_max2_tiny_v8_s0.weights" in s["reason"], s


def test_a_copy_of_the_weights_as_literals_is_refused_scoring_not_proving_anti_hiding(work, tmp_path):
    """A general-layer definition carrying the network's numbers as literals goes over the size budget."""
    net = json.loads((work / "networks" / "max2_tiny-v8-s0.json").read_text())
    nums = [abs(v) for w in net["weights"] for v in w["ints"]]
    table = "def table : List Nat := [" + ", ".join(str(v) for v in nums) + "]\n\n"
    src = SCORED_SOURCE.replace("/-- The checker: every input of the task's space. -/\n" + NEW_D,
                                table + "/-- The checker: every input of the task's space. -/\ndef D : Checker := fun I => countSingles I graph task (if table.length = 0 then [] else allInputs task.space)")
    src = src.replace("  intro w c n cost h\n  unfold numCorrect\n  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h",
                      "  intro w c n cost h\n  unfold numCorrect\n  simp only [D, table, List.length_cons, Nat.succ_ne_zero, ite_false] at h\n  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h")
    r = submit(scored_variant(tmp_path, "weights-copy", src), work, env=SMALL_BUDGET)
    assert r["status"] == "accepted", r["reason"]
    s = r["scoring"]
    assert s["status"] == "refused" and "description size" in s["reason"], s
    assert s["description_size"] >= copy_bound(nums)
    # refused by a budget, after the kernel verified the instance: no score, and the measurement is kept (v12)
    assert s["bill"] is None and s["length"] is None
    assert s["measured_bill"] == 64 * 63 and s["measured_length"] == 64 * 63 + s["extract"] + s["read"]


def test_a_checker_outside_the_counted_language_is_refused_scoring(work, tmp_path):
    """`Interp.counting` and `CostM` are not on the allowlist: a checker that runs the counting interpreter
    itself (for free, outside the bill) is refused scoring, even when the result is the same."""
    src = SCORED_SOURCE.replace(NEW_D,
                                "def D : Checker := fun I => countSingles I graph task "
                                "(if (CostM.billed (countSingles Interp.counting graph task [[0, 0]]) ⟨[], #[]⟩).isSome then allInputs task.space else allInputs task.space)")
    src = src.replace("  intro w c n cost h\n  unfold numCorrect\n  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h",
                      "  intro w c n cost h\n  unfold numCorrect\n  simp only [D, ite_self] at h\n  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h")
    r = submit(scored_variant(tmp_path, "bare-function", src), work)
    assert r["status"] == "accepted", r["reason"]
    s = r["scoring"]
    assert s["status"] == "refused" and "Interp.counting" in s["reason"] and "CostM.billed" in s["reason"], s


def test_a_checker_may_compare_a_list_with_the_empty_list(work, tmp_path):
    """`a = []` elaborates to `List.instDecidableEqNil`, which decides it by matching on the list without looking at
    its elements (as `List.isEmpty`); allowed from policy v8. Run attn-min2-ptl-1 (12 November 2026): the agent's
    shape check `sC ≠ []` on a 0-d weight was refused scoring for this constant alone."""
    src = SCORED_SOURCE.replace(NEW_D, "def D : Checker := fun I => countSingles I graph task "
                                      "(if task.space ≠ [] ∧ [] ≠ task.space then allInputs task.space else [])")
    src = src.replace("  intro w c n cost h\n  unfold numCorrect\n  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h",
                      "  intro w c n cost h\n  unfold numCorrect\n  simp only [D] at h\n"
                      "  rw [if_pos (by decide : task.space ≠ [] ∧ [] ≠ task.space)] at h\n"
                      "  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h")
    r = submit(scored_variant(tmp_path, "nil-test", src), work)
    assert r["status"] == "accepted", r["reason"]
    s = r["scoring"]
    assert s["status"] == "scored", s
    assert s["bill"] == 64 * 63 and r["policy_version"] == "open-lane-policy-v14"


# ---- the protected modules: the network apart from the claim (17 November 2026) --------------------------------
SPLIT = PROJECT / "examples" / "open_lane" / "max2_tiny_split"


def test_a_proof_split_over_the_network_and_the_claim_is_scored_as_the_one_module_proof_is(work):
    """examples/open_lane/max2_tiny_split: the scored brute-force proof in three modules. The checker, its
    soundness proof and the decided fact import the network's module alone (Protected.N_max2_tiny_v8_s0: graph,
    weights, task); only the last module names the claim's (Protected.N_max2_tiny_v8_s0_c64), whose constants
    have the same definitions. The kernel accepts the soundness and instance statements the service writes with
    the claim module's names, unfolding both: the same count, bill, length and description size as the proof in
    one module."""
    one = submit(SCORED, work)
    r = submit(SPLIT, work)
    assert r["status"] == "accepted" and r["certified_count"] == 64, r["reason"]
    s = r["scoring"]
    assert s["status"] == "scored", s
    assert (s["bill"], s["length"]) == (64 * 63, one["scoring"]["length"]) and s["description_size"] <= one["scoring"]["description_size"]
    step = next(x for x in r["steps"] if x["step"] == "protected")
    assert step["module"] == "Protected.N_max2_tiny_v8_s0_c64" and step["network_module"] == "Protected.N_max2_tiny_v8_s0"


def test_facts_about_the_network_are_not_compiled_again_when_the_claim_changes(work, tmp_path):
    """What the split is for. In run attn-min2-ptl-3 raising the claimed count renamed the protected module, and
    every module of the proof was edited and compiled again (about 20 compiles). Here the general layer and the
    fact are compiled once, against claim 64; then a module for claim 60 is compiled against them as they are:
    the claim's module has another name, the network's the same, and the fact's object file is untouched."""
    ws = tmp_path / "ws"
    shutil.copytree(SPLIT / "Candidate", ws / "Candidate")
    (ws / "Candidate" / "SplitTop.lean").unlink()

    def compile_(rel: str, claimed: int) -> dict:
        r = subprocess.run([sys.executable, "-B", str(HERE / "accept.py"), "compile", str(ws), rel, "--repo", str(REPO),
                            "--work", str(work), "--model", "tests/max2_tiny", "--network", "max2_tiny-v8-s0",
                            "--claimed", str(claimed)], capture_output=True, text=True, timeout=1800)
        out = json.loads(r.stdout)
        assert out["ok"] is True, out
        return out

    a = compile_("Candidate/SplitGeneral.lean", 64)
    b = compile_("Candidate/SplitFacts.lean", 64)
    assert a["protected_module"] == b["protected_module"] == "Protected.N_max2_tiny_v8_s0_c64"
    assert a["network_module"] == "Protected.N_max2_tiny_v8_s0"
    fact = ws / "out" / "Candidate" / "SplitFacts.olean"
    before = (hashlib.sha256(fact.read_bytes()).hexdigest(), fact.stat().st_mtime_ns)
    (ws / "Candidate" / "SplitTop60.lean").write_text(
        "import Protected.N_max2_tiny_v8_s0_c60\nimport Candidate.SplitFacts\n\nnamespace Candidate.SplitTop60\n\n"
        "open CompactCheck Candidate.SplitGeneral\n\n"
        "theorem performance : Protected.N_max2_tiny_v8_s0_c60.Target := by\n"
        "  show 60 ≤ numCorrect Protected.N_max2_tiny_v8_s0.graph Protected.N_max2_tiny_v8_s0.weights Protected.N_max2_tiny_v8_s0.task\n"
        "  obtain ⟨cost, h⟩ := CostM.exec_of_billed Candidate.SplitFacts.D_run\n"
        "  exact Nat.le_trans (by decide) (D_sound _ _ 64 cost h)\n\nend Candidate.SplitTop60\n")
    c = compile_("Candidate/SplitTop60.lean", 60)
    assert c["protected_module"] == "Protected.N_max2_tiny_v8_s0_c60" and c["network_module"] == a["network_module"]
    assert (hashlib.sha256(fact.read_bytes()).hexdigest(), fact.stat().st_mtime_ns) == before
    # the network's module was compiled once for both claims
    assert sorted(p.name for p in (work / "protected" / "parts").iterdir() if p.name.startswith("N_max2_tiny_v8_s0")) == ["N_max2_tiny_v8_s0"]


def split_with(tmp_path: Path, name: str, extra: dict[str, str], imports: list[str]) -> Path:
    """The split example with more modules (`extra`: file name to source), of which `imports` are imported by
    the module that proves the target."""
    d = variant(tmp_path, name, base=SPLIT)
    for rel, src in extra.items():
        (d / "Candidate" / rel).write_text(src)
    top = d / "Candidate" / "SplitTop.lean"
    text = top.read_text()
    assert "import Candidate.SplitFacts\n" in text
    top.write_text(text.replace("import Candidate.SplitFacts\n", "import Candidate.SplitFacts\n" + "".join(f"import Candidate.{m}\n" for m in imports), 1))
    m = json.loads((d / "manifest.json").read_text())
    m["modules"] += [f"Candidate/{rel}" for rel in extra]
    (d / "manifest.json").write_text(json.dumps(m))
    return d


EQ_A = "namespace Candidate.EqA\n\ndef rows : List Nat → Nat\n  | [] => 0\n  | x :: xs => x + rows xs\n\nend Candidate.EqA\n"


def eq_user(name: str, xs: str, total: int) -> str:
    return (f"import Candidate.EqA\n\nnamespace Candidate.{name}\n\ntheorem t : Candidate.EqA.rows {xs} = {total} := by\n"
            f"  simp [Candidate.EqA.rows]\n\nend Candidate.{name}\n")


def test_two_modules_that_each_derive_the_same_equation_lemma_are_one_proof(work, tmp_path):
    """Lean derives a definition's equation lemmas (`rows.eq_1`, `rows.eq_def`) in the module that first unfolds
    it, under the definition's name. Two modules that unfold `rows` and do not import each other each hold a
    copy; Lean imports both (the same theorem). Until policy v13 the service refused such a proof, "the
    candidate declares Candidate.EqA.rows.eq_def twice" (run attn-min2-ptl-3, round 1, `Candidate.Far.rows.eq_2`:
    a false alarm that cost the agent a submission). A second copy with the same statement adds nothing: the
    kernel replays the first."""
    d = split_with(tmp_path, "eq-dup", {"EqA.lean": EQ_A, "EqB.lean": eq_user("EqB", "[1, 2]", 3), "EqC.lean": eq_user("EqC", "[2, 2]", 4)},
                   ["EqB", "EqC"])
    r = submit(d, work)
    assert r["status"] == "accepted", r["reason"]
    assert r["scoring"]["status"] == "scored", r["scoring"]


def test_one_name_with_two_statements_is_still_refused(work, tmp_path):
    """What the rule is for: two modules that declare one name with different statements. Lean refuses to import
    both into one module, so only one is imported by the proof; the other is listed. Which of the two a later
    stage reads under that name would be the candidate's choice, so the proof is refused, as before."""
    one = "namespace Candidate.Shared\n\ntheorem t : 1 + 1 = 2 := rfl\n\nend Candidate.Shared\n"
    two = "namespace Candidate.Shared\n\ntheorem t : 2 + 2 = 4 := rfl\n\nend Candidate.Shared\n"
    d = split_with(tmp_path, "two-statements", {"SharedOne.lean": one, "SharedTwo.lean": two}, ["SharedOne"])
    r = submit(d, work)
    assert r["status"] == "rejected" and "declares Candidate.Shared.t twice" in r["reason"], r["reason"]


def test_a_definition_declared_in_two_modules_is_still_refused(work, tmp_path):
    """Only a second copy of a theorem with the same statement is let through. A definition is not: two
    definitions of one name with one type can differ in what they compute."""
    one = "namespace Candidate.Shared\n\ndef k : Nat := 1\n\nend Candidate.Shared\n"
    two = "namespace Candidate.Shared\n\ndef k : Nat := 2\n\nend Candidate.Shared\n"
    d = split_with(tmp_path, "two-definitions", {"SharedOne.lean": one, "SharedTwo.lean": two}, ["SharedOne"])
    r = submit(d, work)
    assert r["status"] == "rejected" and "declares Candidate.Shared.k twice" in r["reason"], r["reason"]


def test_the_protected_modules_of_a_network_of_width_32_compile(work):
    """attn-min2-v64-s0: 8,257 weights, its embedding and unembedding 2,048 entries each. A literal that long
    needs more than Lean's default recursion depth; until 17 November 2026 the protected module of such a
    network did not compile ("maximum recursion depth has been reached"), so the open lane stopped at width 8.
    The module now sets the depth it needs for its weights (and lifts the compiler's step limit, which tensors
    of 4,096 entries run into: attn-min2-v128-s0 builds too, in about 140 s, not run here). Both modules are
    built and the claim's is checked against the network file."""
    sys.path.insert(0, str(HERE))
    import accept
    sys.path.pop(0)
    accept._repo = REPO
    net_json = accept.export_network(REPO, "models/attn-min2", "attn-min2-v64-s0", work)
    net = json.loads(net_json.read_text())
    assert max(len(w["ints"]) for w in net["weights"]) == 2048
    r = accept.build_protected(net_json, 100, work, accept.lean_binary(), accept.lean_path(), accept.box_mode("hardened"))
    assert r["modules"] == ["Protected.N_attn_min2_v64_s0", "Protected.N_attn_min2_v64_s0_c100"] and r["domain"] == 4096
    assert Path(r["olean"]).is_file() and (Path(r["lean_path_dir"]) / "Protected" / "N_attn_min2_v64_s0.olean").is_file()


# ---- the last-bits test (policy v14) ----------------------------------------------------------------------------
STORED = PROJECT / "examples" / "open_lane" / "max2_tiny_stored_weight"


def test_the_copies_of_the_last_bits_test_change_every_parameter_a_little_and_nothing_else():
    """The copies are made from the network file alone, so for any network: every nonzero parameter moves by
    about 2^-level of itself and at least one unit of its tensor's last place, a zero stays a zero, the
    exporter's constants and everything that is not a weight stay, and a copy is the same on every machine."""
    sys.path.insert(0, str(HERE))
    import accept
    sys.path.pop(0)
    net = {"format": "compactcheck-network-v1", "network": "toy-s0", "graph": {"nodes": []}, "task": "max",
           "weights": [{"name": "E", "shape": [2, 3], "exp": -32, "ints": [1505767040, -3579024640, 0, 5, -1, 2 ** 40]},
                       {"name": "#const0", "shape": [], "exp": -54, "ints": [6369051672525773]}]}
    before = json.dumps(net)
    for level in (20, 16, 12, 8):
        a, b = accept.last_bits_copy(net, level, 0), accept.last_bits_copy(net, level, 1)
        assert json.dumps(net) == before and a == accept.last_bits_copy(net, level, 0)
        assert {k: v for k, v in a.items() if k != "weights"} == {k: v for k, v in net.items() if k != "weights"}
        assert a["weights"][1] == net["weights"][1]  # the constant of the model's code
        for copy in (a, b):
            w = copy["weights"][0]
            assert {k: v for k, v in w.items() if k != "ints"} == {k: v for k, v in net["weights"][0].items() if k != "ints"}
            for m, m2 in zip(net["weights"][0]["ints"], w["ints"]):
                assert (m2 == 0) if m == 0 else (m2 != m and abs(m2 - m) == max(1, abs(m) >> level)), (level, m, m2)
        assert a != b or level == 8  # two copies differ (in the signs of the moves)
    assert accept.last_bits_copy(net, 20, 0) != accept.last_bits_copy({**net, "network": "toy-s1"}, 20, 0)


def test_a_checker_that_computes_on_the_weights_keeps_its_count_on_the_copies(work):
    """The brute-force proof, and the same proof split over the network's module and the claim's: on every copy
    of the network, down to the coarsest level run, the checker certifies the 64 inputs it certifies on the
    network. The compiled run on the network itself gave what the kernel established, or the proof would not
    be scored. (Run attn-min2-ptl-3's proof, 1,889 inputs: 1,889 on every copy down to level 12; measured, not
    part of this suite.)"""
    for example in (SCORED, SPLIT):
        r = submit(example, work)
        s = r["scoring"]
        assert s["status"] == "scored", s
        lb = s["last_bits"]
        assert lb["passed"] is True and lb["levels"] == [20, 16] and lb["recorded"] == [12, 8] and lb["copies"] == 2
        assert [x["level"] for x in lb["runs"]] == [20, 20, 16, 16, 12, 12, 8, 8] and {x["count"] for x in lb["runs"]} == {64}
        assert lb["least_share"] == 1.0 and lb["holds_to"] == 8
        step = next(x for x in r["steps"] if x["step"] == "last_bits")
        assert step["rc"] == 0 and step["status"] == "ok" and step["timed_out"] is False


def test_a_checker_whose_count_hangs_on_a_stored_weight_is_refused_scoring(work):
    """examples/open_lane/max2_tiny_stored_weight: brute force that also asks that the first embedding weight be
    exactly the number written into the checker's code. Sound, accepted by the kernel, 64 inputs on this network.
    It is the smallest case of the pattern the size budget cannot keep out of a small network: a checker that
    holds the network's numbers, compares the weights with them and rests its count on the comparison (with all
    the weights held, the rest of its work can be done for free on its copy). On every copy of the network the
    comparison fails and it certifies nothing: refused scoring, verified as before, its measured length kept."""
    r = submit(STORED, work)
    assert r["status"] == "accepted" and r["certified_count"] == 64, r["reason"]
    s = r["scoring"]
    assert s["status"] == "refused" and "last-bits test" in s["reason"] and "certifies 0 inputs" in s["reason"], s
    assert s["bill"] is None and s["length"] is None and r["score_eligible"] is False
    assert s["measured_bill"] == 64 * 63 + 64 + 4 and s["measured_length"] == s["measured_bill"] + s["extract"] + s["read"]
    lb = s["last_bits"]
    assert lb["passed"] is False and {x["count"] for x in lb["runs"]} == {0} and lb["least_share"] == 0.0 and lb["holds_to"] is None
    assert s["description_size"] <= s["size_budget"]  # the size budget has nothing against it


def test_the_development_compile_says_what_the_last_bits_test_will_say(work, tmp_path):
    """The preview of a development compile runs the last-bits test as the score step does, so that a count that
    hangs on the weights' last bits is seen for the price of a compile and not of a submission (whose kernel
    check comes first). It is given two minutes at most, and no more than the caller's call has left: a caller
    that stops the call from outside (the pipeline's lean_check) says how long it gives it, and a compile that
    used the time up is reported as compiled, with the test not run."""
    ws = tmp_path / "ws"
    (ws / "Candidate").mkdir(parents=True)
    (ws / "Candidate" / "StoredWeight.lean").write_text((STORED / "Candidate" / "StoredWeight.lean").read_text())
    receipts = len(list((work / "receipts").glob("*")))
    base = [sys.executable, "-B", str(HERE / "accept.py"), "compile", str(ws), "Candidate/StoredWeight.lean", "--repo",
            str(REPO), "--work", str(work), "--model", "tests/max2_tiny", "--network", "max2_tiny-v8-s0", "--claimed", "64",
            "--checker", "Candidate.StoredWeight.D"]
    out = json.loads(subprocess.run(base, capture_output=True, text=True, timeout=1800).stdout)
    lb = out["scoring_preview"]["last_bits"]
    assert out["ok"] is True and out["scoring_preview"]["counted_language"] == "ok", out
    assert (lb["count"], lb["bill"]) == (64, 4100) and lb["passes"] is False and lb["holds_to"] is None, lb
    assert lb["least_count_on_copies"] == 0 and {r["count"] for r in lb["runs"]} == {0}, lb
    out = json.loads(subprocess.run(base + ["--limit-s", "1"], capture_output=True, text=True, timeout=1800).stdout)
    lb = out["scoring_preview"]["last_bits"]
    assert out["ok"] is True and lb["passes"] is None and "no time left" in lb["reason"], out
    assert out["scoring_preview"]["description_size"] > 0  # the rest of the preview is there
    assert len(list((work / "receipts").glob("*"))) == receipts  # and nothing was submitted


def test_a_module_that_replaces_compiled_code_is_refused_scoring(work, tmp_path):
    """The last-bits test runs the checker compiled, where the kernel ran its definition. `implemented_by` gives a
    definition other compiled code than its body, so a checker could pass the test with code the kernel never
    saw. A candidate whose modules use it (or `extern`, `csimp`, `initialize`) is not run and not scored."""
    extra = ("\n\ndef plain (n : Nat) : Nat := n + 1\ndef other (n : Nat) : Nat := n + 2\n"
             "attribute [implemented_by other] plain\n\nend Candidate.Max2TinyScored\n")
    assert SCORED_SOURCE.rstrip().endswith("end Candidate.Max2TinyScored")
    src = SCORED_SOURCE.rstrip()[: -len("end Candidate.Max2TinyScored")].rstrip() + extra
    r = submit(scored_variant(tmp_path, "replaced-code", src), work)
    assert r["status"] == "accepted", r["reason"]
    s = r["scoring"]
    assert s["status"] == "refused" and "implemented_by" in s["reason"] and "Candidate.Max2TinyScored" in s["reason"], s
    assert s["last_bits"]["passed"] is False and s["last_bits"]["runs"] is None and s["measured_length"] is not None



def test_a_checker_without_compiled_code_is_refused_scoring(work, tmp_path):
    """The kernel runs a definition whether or not Lean compiled it; the last-bits test needs the compiled code.
    A `noncomputable` checker is verified, and refused scoring with that reason: the candidate's to mend, not an
    error of the service."""
    r = submit(scored_variant(tmp_path, "no-compiled-code", SCORED_SOURCE.replace(NEW_D, "noncomputable " + NEW_D)), work)
    assert r["status"] == "accepted" and r["certified_count"] == 64, r["reason"]
    s = r["scoring"]
    assert s["status"] == "refused" and "no compiled code" in s["reason"] and "noncomputable" in s["reason"], s
    assert s["last_bits"]["passed"] is False and s["last_bits"]["runs"] is None
    assert s["measured_length"] is not None and s["length"] is None and r["score_eligible"] is False
    assert next(x for x in r["steps"] if x["step"] == "last_bits")["status"] == "uncompiled"


DEEP = """import Protected.N_max2_tiny_v8_s0_c64
import CompactCheck.CountedOps
namespace Candidate.Deep
open CompactCheck Protected.N_max2_tiny_v8_s0_c64

def deep (I : Interp) : Nat → I.M I.N
  | 0 => pure I.nzero
  | n + 1 => do
    let ok ← I.single graph task [0, 0]
    let m ← deep I n
    pure (I.nadd (I.countB ok) m)

@[export candidate_deep_helper]
def helper (n : Nat) : Nat := n + 1

def D : Checker := fun I => deep I 60000
end Candidate.Deep
"""


def test_the_preview_says_why_the_last_bits_test_could_not_say_anything(work, tmp_path):
    """Three ways a development preview has no count to show, each told apart. A module with `export` (a name
    under which other compiled code can be found) is not run. A checker whose runs do not fit the preview's time
    is reported as not run to the end, with how far it came, and not as failing: a preview gives the runs less
    time than a submission does (here 10 s, by the test's hook, for runs of 60,000 forward passes each)."""
    ws = tmp_path / "ws"
    (ws / "Candidate").mkdir(parents=True)
    base = [sys.executable, "-B", str(HERE / "accept.py"), "compile", str(ws), "Candidate/Deep.lean", "--repo", str(REPO),
            "--work", str(work), "--model", "tests/max2_tiny", "--network", "max2_tiny-v8-s0", "--claimed", "64",
            "--checker", "Candidate.Deep.D"]
    (ws / "Candidate" / "Deep.lean").write_text(DEEP)
    out = json.loads(subprocess.run(base, capture_output=True, text=True, timeout=1800).stdout)
    lb = out["scoring_preview"]["last_bits"]
    assert out["ok"] is True and lb["passes"] is False and "`export`" in lb["reason"] and "Candidate.Deep" in lb["reason"], out
    (ws / "Candidate" / "Deep.lean").write_text(DEEP.replace("@[export candidate_deep_helper]\n", ""))
    out = json.loads(subprocess.run(base, capture_output=True, text=True, timeout=1800,
                                    env={**os.environ, "ACCEPT_PREVIEW_LAST_BITS_S": "10"}).stdout)
    lb = out["scoring_preview"]["last_bits"]
    assert out["ok"] is True and lb["passes"] is None, out
    assert "not run to the end" in lb["reason"] and "did not finish within 10 s" in lb["reason"], lb
    assert "on the network" in lb["reason"] or "on copy" in lb["reason"], lb


def test_what_ends_a_run_of_the_last_bits_test_is_laid_at_the_right_door(monkeypatch, tmp_path):
    """The step after the probe, with the probe's answers given (no Lean). What the candidate's own code did is
    a refusal of scoring with the reason, the proof verified as before and its measured length kept: other
    compiled code, no compiled code, a run that ended without a result or ran out of time. What the service
    could not do is an error, and the receipt's scoring is then unsettled: it does not read as scored."""
    sys.path.insert(0, str(HERE))
    import accept
    sys.path.pop(0)
    scored = {"checker": "Candidate.X.D", "claimed_bill": 4032}
    block = {"status": "scored", "reason": None, "bill": 4032, "length": 4112, "measured_bill": 4032, "measured_length": 4112}
    answers = {
        "replaced": ({"status": "replaced", "module": "Candidate.X", "by": "implemented_by"}, "`implemented_by`"),
        "uncompiled": ({"status": "uncompiled", "reason": "(interpreter) unknown declaration 'Candidate.X.D'"}, "no compiled code"),
        "untyped": ({"status": "untyped", "reason": "not a checker: the type of Candidate.X.D is not Checker"}, "not a checker"),
        "stopped": ({"status": "stopped", "done": 3, "reason": "its run on copy 3 of 8 ended without a result (exit code -6)"},
                    "did not run to the end: its run on copy 3 of 8"),
        "other count": ({"status": "ok", "base": {"count": 60, "bill": 4032}, "counts": [(20, 64)] * 8}, "the kernel established 64"),
        "other bill": ({"status": "ok", "base": {"count": 64, "bill": 9}, "counts": [(20, 64)] * 8}, "the kernel established 64 and 4032"),
        "last bits": ({"status": "ok", "base": {"count": 64, "bill": 4032},
                       "counts": [(20, 64), (20, 64), (16, 64), (16, 57), (12, 0), (12, 0), (8, 0), (8, 0)]}, "certifies 57 inputs"),
    }
    for name, (res, said) in answers.items():
        monkeypatch.setattr(accept, "last_bits_runs", lambda *a, _r=res, **k: {"rc": 0, "seconds": 1.0, "timed_out": False, **_r})
        receipt = {"steps": [], "scoring": dict(block)}
        out = accept.last_bits(scored, dict(block), 64, {}, tmp_path / "n.json", [], tmp_path, {}, "process", tmp_path, [],
                               tmp_path, receipt)
        assert out["status"] == "refused" and said in out["reason"], (name, out)
        assert out["bill"] is None and out["length"] is None and out["measured_length"] == 4112, (name, out)
        assert out["last_bits"]["passed"] is False and receipt["steps"][-1]["step"] == "last_bits", (name, out)
    # nine tenths is the line: 58 of 64 keeps it, at the deciding levels only
    kept = {"status": "ok", "base": {"count": 64, "bill": 4032},
            "counts": [(20, 64), (20, 64), (16, 58), (16, 64), (12, 3), (12, 64), (8, 0), (8, 0)]}
    monkeypatch.setattr(accept, "last_bits_runs", lambda *a, **k: {"rc": 0, "seconds": 1.0, "timed_out": False, **kept})
    out = accept.last_bits(scored, dict(block), 64, {}, tmp_path / "n.json", [], tmp_path, {}, "process", tmp_path, [], tmp_path,
                           {"steps": []})
    assert out["status"] == "scored" and out["length"] == 4112 and out["last_bits"]["passed"] is True, out
    assert out["last_bits"]["least_share"] == round(58 / 64, 4) and out["last_bits"]["holds_to"] == 16, out
    # the service's own failure
    monkeypatch.setattr(accept, "last_bits_runs", lambda *a, **k: {"rc": 1, "seconds": 1.0, "timed_out": False, "status": "error",
                                                                   "reason": "unknown command probe"})
    receipt = {"steps": [], "scoring": dict(block)}
    with pytest.raises(accept.Infra, match="unknown command probe"):
        accept.last_bits(scored, dict(block), 64, {}, tmp_path / "n.json", [], tmp_path, {}, "process", tmp_path, [], tmp_path, receipt)
    assert receipt["scoring"]["status"] is None and receipt["scoring"]["length"] is None, receipt
    assert receipt["scoring"]["last_bits"]["passed"] is None and receipt["scoring"]["measured_length"] == 4112


def test_a_probe_that_says_nothing_points_at_the_binary(monkeypatch, tmp_path):
    """An acceptcheck built before the probe existed prints its usage and no line of the probe's. That is the
    service's state, never the candidate's, and the error says what to do about it."""
    sys.path.insert(0, str(HERE))
    import accept
    sys.path.pop(0)
    net = tmp_path / "toy.json"
    net.write_text(json.dumps({"network": "toy-s0", "weights": [{"name": "E", "shape": [2], "exp": -8, "ints": [3, -5]}]}))
    answers = iter([{"rc": 1, "stdout": "", "stderr": "usage: acceptcheck check ...", "timed_out": False, "seconds": 0.1},
                    {"rc": -6, "stdout": '{"status":"loaded"}\n{"status":"run","done":2}\n', "timed_out": False, "seconds": 3.0,
                     "stderr": "libc++abi: terminating: deep recursion was detected at 'interpreter' (potential solution: more)\n#1 x"},
                    {"rc": -9, "stdout": '{"status":"loaded"}\n', "stderr": "timed out", "timed_out": True, "seconds": 9.0},
                    {"rc": -9, "stdout": "", "stderr": "timed out", "timed_out": True, "seconds": 9.0}])
    monkeypatch.setattr(accept, "run_boxed", lambda *a, **k: next(answers))
    monkeypatch.setattr(accept, "acceptcheck_binary", lambda: Path("/nowhere/acceptcheck"))
    monkeypatch.setattr(accept, "toolchain_root", lambda lean: tmp_path)
    run = lambda: accept.last_bits_runs("Candidate.X.D", False, {"module": "Protected.N_toy_s0_c1"}, net, [], tmp_path, {},
                                        "process", tmp_path, [], tmp_path, timeout_s=9)
    r = run()
    assert r["status"] == "error" and "lake build acceptcheck" in r["reason"] and "usage" in r["reason"], r
    r = run()  # ended in the candidate's code, after two runs: the candidate's
    assert r["status"] == "stopped" and r["done"] == 2 and "on copy 2 of 8" in r["reason"], r
    assert "deep recursion was detected at 'interpreter'" in r["reason"] and "potential solution" not in r["reason"], r
    r = run()  # out of time in the candidate's code
    assert r["status"] == "stopped" and r["timed_out"] and "on the network did not finish within 9 s" in r["reason"], r
    r = run()  # out of time before the candidate's code was reached: the service's
    assert r["status"] == "error" and "did not start its runs" in r["reason"], r


# ---- planned checkers (policy v9) ---------------------------------------------------------------------------
PLANNED = PROJECT / "examples" / "open_lane" / "max2_tiny_planned"
PLANNED_SOURCE = (PLANNED / "Candidate" / "Max2TinyPlanned.lean").read_text()
PLANNED_PLAN = json.loads((PLANNED / "manifest.json").read_text())["scored"]["plan"]


def planned_variant(tmp_path: Path, name: str, lean: str | None = None, plan: list | None = None) -> Path:
    """A copy of the planned example; with `plan`, the manifest's plan and the protected module's name in the
    source follow it."""
    d = variant(tmp_path, name, lean=lean, module_path="Candidate/Max2TinyPlanned.lean", base=PLANNED)
    if plan is not None:
        sys.path.insert(0, str(HERE))
        import make_protected
        sys.path.pop(0)
        old = make_protected.module_name("max2_tiny-v8-s0", 60, None, PLANNED_PLAN)
        new = make_protected.module_name("max2_tiny-v8-s0", 60, None, plan)
        src = d / "Candidate" / "Max2TinyPlanned.lean"
        src.write_text(src.read_text().replace(old, new))
        m = json.loads((d / "manifest.json").read_text())
        m["scored"]["plan"] = plan
        (d / "manifest.json").write_text(json.dumps(m))
    return d


def test_a_planned_checker_is_scored_and_its_plan_is_free(work):
    """The plan chooses 60 of the 64 inputs; the checker runs the single rule on those. The plan costs nothing,
    is not part of the description size, and the receipt says how long it was."""
    r = submit(PLANNED, work)
    assert r["status"] == "accepted" and r["certified_count"] == 60, r["reason"]
    s = r["scoring"]
    assert s["status"] == "scored", s
    assert s["bill"] == 60 * 63 and s["read"] == 0 and s["length"] == s["bill"] + s["extract"] + s["read"]
    assert s["plan_entries"] == 64 and s["description_size"] <= s["size_budget"]
    assert s["plan_bits"] == 184 <= s["plan_bits_budget"] == s["weight_bits"] // 4  # 60 ones, 4 zeros: 60 * 3 + 4
    assert r["policy_version"] == "open-lane-policy-v14"


def test_a_planned_soundness_proof_must_hold_for_every_plan(work, tmp_path):
    """A plan is not trusted. A soundness theorem about one plan, written into the candidate as a literal copy, is
    not the shape the kernel is asked to accept (for every plan): refused scoring, still verified. One that names
    the protected module's plan is refused by the general-layer rule, which allows only graph and task."""
    copy = "def myPlan : List Nat := [" + ", ".join(str(v) for v in PLANNED_PLAN) + "]\n\n"
    src = PLANNED_SOURCE.replace("/-- The planned checker", copy + "/-- The planned checker")
    src = src.replace("theorem D_sound : ∀ (p : List Nat) (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),\n"
                      "    CostM.exec (D p Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task := by\n"
                      "  intro p w c n cost h",
                      "theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),\n"
                      "    CostM.exec (D myPlan Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task := by\n"
                      "  intro w c n cost h")
    src = src.replace("pick p (allInputs task.space)) [] n cost h)\n    (pick_sublist p (allInputs task.space))",
                      "pick myPlan (allInputs task.space)) [] n cost h)\n    (pick_sublist myPlan (allInputs task.space))")
    src = src.replace("exact D_sound plan weights cert 60 cost h", "exact D_sound weights cert 60 cost h")
    assert "myPlan Interp.counting" in src and "D_sound weights cert 60" in src
    r = submit(planned_variant(tmp_path, "one-plan", lean=src), work)
    assert r["status"] == "accepted" and r["certified_count"] == 60, r["reason"]
    s = r["scoring"]
    assert s["status"] == "refused" and "Challenge.sound" in s["reason"], s
    src2 = src.replace("CostM.exec (D myPlan Interp.counting)", "CostM.exec (D plan Interp.counting)")
    r = submit(planned_variant(tmp_path, "protected-plan", lean=src2), work)
    assert r["status"] == "accepted", r["reason"]
    s = r["scoring"]
    assert s["status"] == "refused" and ".plan" in s["reason"] and "only" in s["reason"], s


def test_a_plan_over_its_bounds_is_refused_scoring(work, tmp_path):
    """At most 4 entries per input plus 10,000, each below 2^32, as the fixed rules lane bounds its plan, and
    (policy v12) at most a quarter of weight_bits in a prefix code, so that a plan cannot carry a copy of the
    weights: 200 entries of 31 bits past the 64 inputs hold 12,600 bits, a copy of this network's weights about
    1,900. Entries past the 64 inputs are ignored by this checker, so the proofs still verify; only scoring
    refuses them, before the kernel is asked (no measured length)."""
    heavy = PLANNED_PLAN + [2 ** 31] * 200
    r = submit(planned_variant(tmp_path, "heavy-plan", plan=heavy), work)
    assert r["status"] == "accepted" and r["certified_count"] == 60, r["reason"]
    s = r["scoring"]
    assert s["status"] == "refused" and "the plan holds 12784 bits" in s["reason"] and "1/4" in s["reason"], s
    assert s["plan_bits"] == 12784 > s["plan_bits_budget"] and s["measured_length"] is None
    long = PLANNED_PLAN + [5] * (4 * 64 + 10_000 - 64 + 1)
    r = submit(planned_variant(tmp_path, "long-plan", plan=long), work)
    assert r["status"] == "accepted" and r["certified_count"] == 60, r["reason"]
    assert r["scoring"]["status"] == "refused" and "more than 10256" in r["scoring"]["reason"], r["scoring"]
    big = PLANNED_PLAN[:-1] + [2 ** 32]
    r = submit(planned_variant(tmp_path, "big-entry", plan=big), work)
    assert r["status"] == "accepted" and r["certified_count"] == 60, r["reason"]
    assert r["scoring"]["status"] == "refused" and "not below 2^32" in r["scoring"]["reason"], r["scoring"]
    bad = json.loads((PLANNED / "manifest.json").read_text())
    bad["scored"]["plan"] = [1, -1]
    d = variant(tmp_path, "negative-plan", manifest=bad, module_path="Candidate/Max2TinyPlanned.lean", base=PLANNED)
    r = submit(d, work)
    assert r["status"] == "rejected" and "scored.plan" in r["reason"], r["reason"]


# ---- kinds, assurance, zero coverage, the development compile --------------------------------------------
def test_an_auxiliary_lemma_is_accepted_without_a_count(work, tmp_path):
    r = submit(variant(tmp_path, "aux-lemma", manifest={"kind": "auxiliary", "theorem": "Candidate.Max2Tiny.D_sound"}), work)
    assert r["status"] == "accepted", r["reason"]
    assert r["claim_kind"] == "auxiliary" and r["certified_count"] is None and r["score_eligible"] is False
    assert "numCorrect" in r["statement"] and set(r["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}
    r = submit(variant(tmp_path, "aux-def", manifest={"kind": "auxiliary", "theorem": "Candidate.Max2Tiny.D"}), work)
    assert r["status"] == "rejected" and "not a theorem" in r["reason"]


def test_the_kernel_runs_the_networks_graph_through_the_kernels_semantics(work):
    """examples/open_lane/max2_tiny_kernel_run: a lemma in which the kernel evaluates the specification's
    `semGraph` on the network's weights and an input. It rewrites with `semGraph_eqK`
    (CompactCheck/SemanticsKernel.lean) and decides the statement about `semGraphK`, which builds every tensor
    from a list and reads it through a tree; the statement the service records is the one about `semGraph`. The
    specification's own definitions build and read arrays entry by entry, which the kernel, for which an array
    is a list, pays for with the square of their size (docs/COUNTED.md, "Running the specification in the
    kernel")."""
    r = submit(PROJECT / "examples" / "open_lane" / "max2_tiny_kernel_run", work)
    assert r["status"] == "accepted", r["reason"]
    assert r["claim_kind"] == "auxiliary" and r["certified_count"] is None
    assert "CompactCheck.semGraph" in r["statement"] and "semGraphK" not in r["statement"]
    assert set(r["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}


def test_a_scored_proof_is_marked_kernel_checked(work):
    r = submit(SCORED, work)
    assert r["claim_kind"] == "performance" and r["score_eligible"] is True
    assert r["execution_assurance"] == "kernel_checked_instance" and r["scoring"]["assurance"] == "kernel_checked_instance"
    assert r["cost_model"] == "cost-v3"


ZERO = """import Protected.N_max2_tiny_v8_s0_c0
import CompactCheck.Soundness
import CompactCheck.CountedOps

namespace Candidate.Zero
open CompactCheck Protected.N_max2_tiny_v8_s0_c0

def D : Checker := fun I => pure I.nzero

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task := by
  intro w c n cost h
  simp only [D, CostM.exec, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
  omega

theorem D_instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (0, 0) := by decide +kernel

theorem performance : Target := Nat.zero_le _

end Candidate.Zero
"""


def test_zero_coverage_is_accepted_and_scored_not_rejected(work, tmp_path):
    d = variant(tmp_path, "zero", lean=ZERO, module_path="Candidate/Zero.lean", base=SCORED)
    (d / "Candidate" / "Max2TinyScored.lean").unlink()
    m = json.loads((d / "manifest.json").read_text())
    m.update(claimed_count=0, theorem="Candidate.Zero.performance", modules=["Candidate/Zero.lean"],
             scored={"checker": "Candidate.Zero.D", "sound": "Candidate.Zero.D_sound", "instance": "Candidate.Zero.D_instance",
                     "certificate": [], "claimed_bill": 0})
    (d / "manifest.json").write_text(json.dumps(m))
    r = submit(d, work)
    assert r["status"] == "accepted" and r["certified_count"] == 0, r["reason"]
    assert r["scoring"]["status"] == "scored" and r["scoring"]["length"] == 80, r["scoring"]


def test_an_invented_axiom_is_rejected(work, tmp_path):
    src = SOURCE.replace("theorem performance : Target := by", "axiom cheat : Target\n\ntheorem performance : Target := cheat\n\ntheorem performance' : Target := by")
    r = submit(variant(tmp_path, "axiom", lean=src), work)
    assert r["status"] == "rejected" and "axioms that are not allowed" in r["reason"] and "cheat" in r["reason"]


def test_a_soundness_proof_about_another_checker_is_refused_scoring(work, tmp_path):
    """The manifest names D; the soundness theorem is about D2. The service builds the statement for D, so the
    kernel rejects the candidate's theorem at that type: verified, not scored."""
    src = SCORED_SOURCE.replace("/-! ## Specific layer -/", "def D2 : Checker := fun I => pure I.nzero\n\ntheorem D2_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),\n    CostM.exec (D2 Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task := by\n  intro w c n cost h\n  simp only [D2, CostM.exec, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h\n  omega\n\n/-! ## Specific layer -/")
    d = scored_variant(tmp_path, "other-program", src)
    m = json.loads((d / "manifest.json").read_text())
    m["scored"]["sound"] = "Candidate.Max2TinyScored.D2_sound"
    (d / "manifest.json").write_text(json.dumps(m))
    r = submit(d, work)
    assert r["status"] == "accepted" and r["certified_count"] == 64
    assert r["scoring"]["status"] == "refused" and "Challenge.sound" in r["scoring"]["reason"], r["scoring"]


def test_the_development_compile_reports_errors_and_never_accepts(work, tmp_path):
    ws = tmp_path / "ws"
    (ws / "Candidate").mkdir(parents=True)
    (ws / "Candidate" / "Dev.lean").write_text(SCORED_SOURCE.replace("decide +kernel", "exact rfl"))
    cmd = [sys.executable, "-B", str(HERE / "accept.py"), "compile", str(ws), "Candidate/Dev.lean", "--repo", str(REPO),
           "--work", str(work), "--model", "tests/max2_tiny", "--network", "max2_tiny-v8-s0", "--claimed", "64"]
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=1800)
    out = json.loads(r.stdout)
    assert r.returncode == 1 and out["ok"] is False and "error" in out["messages"].lower() and out["protected_module"].endswith("_c64")
    (ws / "Candidate" / "Dev.lean").write_text(SCORED_SOURCE)
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=1800)
    out = json.loads(r.stdout)
    assert r.returncode == 0 and out["ok"] is True
    assert not list((work / "receipts").glob("*Dev*"))  # a compile is not a submission


def test_the_development_compile_previews_the_scoring_checks(work, tmp_path):
    """With --checker, a development compile reports the counted-language closure and the description size, measured
    as the score step measures them: the same size as a submission of the same source, and the same refusal for a
    checker outside the counted language. Run attn-min2-ptl-1 (12 November 2026) learnt of both only from its
    one submission, after the round's budget was spent."""
    final = submit(SCORED, work)["scoring"]
    ws = tmp_path / "ws"
    (ws / "Candidate").mkdir(parents=True)
    (ws / "Candidate" / "Dev.lean").write_text(SCORED_SOURCE)
    base = [sys.executable, "-B", str(HERE / "accept.py"), "compile", str(ws), "Candidate/Dev.lean", "--repo", str(REPO),
            "--work", str(work), "--model", "tests/max2_tiny", "--network", "max2_tiny-v8-s0", "--claimed", "64"]
    r = subprocess.run(base, capture_output=True, text=True, timeout=1800)
    assert r.returncode == 0 and "scoring_preview" not in json.loads(r.stdout)  # only when asked for
    r = subprocess.run(base + ["--checker", "Candidate.Max2TinyScored.D"], capture_output=True, text=True, timeout=1800)
    out = json.loads(r.stdout)
    assert r.returncode == 0 and out["ok"] is True, out
    p = out["scoring_preview"]
    assert p["counted_language"] == "ok" and p["offending"] == [], p
    assert p["description_size"] == final["description_size"] and p["size_budget"] == final["size_budget"], (p, final)
    assert p["within_budget"] is True and p["largest_definitions"][0]["size"] > 0
    # the last-bits test, as the score step ran it on the submission: the count and the bill the compiled checker
    # gives on the network (what the instance theorem will have to state), and the count on every copy
    lb = p["last_bits"]
    assert (lb["count"], lb["bill"]) == (64, final["bill"]) and lb["passes"] is True and lb["holds_to"] == 8, lb
    assert lb["runs"] == final["last_bits"]["runs"] and lb["least_count_on_copies"] == 64, (lb, final["last_bits"])
    # outside the counted language: the preview names the constants the score step would
    bare = SCORED_SOURCE.replace(NEW_D,
                                 "def D : Checker := fun I => countSingles I graph task "
                                 "(if (CostM.billed (countSingles Interp.counting graph task [[0, 0]]) ⟨[], #[]⟩).isSome then allInputs task.space else allInputs task.space)")
    bare = bare.replace("  intro w c n cost h\n  unfold numCorrect\n  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h",
                        "  intro w c n cost h\n  unfold numCorrect\n  simp only [D, ite_self] at h\n  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h")
    (ws / "Candidate" / "Dev.lean").write_text(bare)
    out = json.loads(subprocess.run(base + ["--checker", "Candidate.Max2TinyScored.D"], capture_output=True, text=True,
                                    timeout=1800).stdout)
    p = out["scoring_preview"]
    assert out["ok"] is True and p["counted_language"] == "refused", p
    assert "CompactCheck.Interp.counting" in p["offending"] and "CompactCheck.CostM.billed" in p["offending"], p
    assert "last_bits" not in p  # a checker outside the counted language is not run
    # a name that is not the candidate's
    out = json.loads(subprocess.run(base + ["--checker", "Mathlib.foo"], capture_output=True, text=True, timeout=1800).stdout)
    assert "error" in out["scoring_preview"]
    assert not list((work / "receipts").glob("*Dev*"))  # still not a submission


def test_the_agents_pilot_proof_is_verified_and_refused_scoring_in_the_current_language(work, tmp_path):
    """The pilot's third submission of round 1 (20 October 2026), kept as the agent wrote it: the columns of
    M = U L E, 23 of 64 inputs for a bill of 458. It was written in the first counted language (a concrete
    `CostM Nat`, with concrete booleans); every later version (a checker is a function of the interpreter)
    refuses it: its checker uses `CostM` directly. Its mathematics is still verified (its read lemma migrated
    to policy v10's reads, `migrate_reads`)."""
    r = submit(migrate_reads(AGENT, tmp_path), work)
    assert r["status"] == "accepted" and r["certified_count"] == 23, r["reason"]
    s = r["scoring"]
    assert s["status"] == "refused" and "CostM" in s["reason"], s
    assert r["score_eligible"] is False


# ---- the handoff's remaining fixtures ----------------------------------------------------------------------
def test_the_weights_packed_into_one_literal_are_refused_scoring_not_proving_anti_hiding(work, tmp_path):
    """A copy of the weights encoded in a single big natural number (24 bits each) in a general-layer
    definition: the measure charges a numeral 1 per bit, so the copy weighs 24 per weight."""
    sys.path.insert(0, str(HERE))
    import accept
    sys.path.pop(0)
    accept._repo = REPO
    net = json.loads(accept.export_network(REPO, "tests/max2_tiny", "max2_tiny-v8-s0", work).read_text())
    nums = [abs(v) % (1 << 24) for w in net["weights"] for v in w["ints"]]
    packed = 0
    for v in nums:
        packed = (packed << 24) | v
    table = f"def packed : Nat := {packed}\n\ndef unpack (n k : Nat) : Nat := (n >>> (24 * k)) % (1 <<< 24)\n\n"
    src = SCORED_SOURCE.replace("/-- The checker: every input of the task's space. -/\n" + NEW_D,
                                table + "/-- The checker: every input of the task's space. -/\ndef D : Checker := fun I => countSingles I graph task (if unpack packed 0 = 0 then [] else allInputs task.space)")
    src = src.replace("  intro w c n cost h\n  unfold numCorrect\n  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h",
                      "  intro w c n cost h\n  unfold numCorrect\n  simp only [D] at h\n  rw [if_neg (by decide : ¬ unpack packed 0 = 0)] at h\n  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h")
    r = submit(scored_variant(tmp_path, "weights-packed", src), work, env=SMALL_BUDGET)
    assert r["status"] == "accepted", r["reason"]
    s = r["scoring"]
    assert s["status"] == "refused" and "description size" in s["reason"], s
    assert s["description_size"] >= 24 * len(nums)


def test_option_overrides_in_the_candidate_do_not_reach_the_service(work, tmp_path):
    """A candidate may raise its own elaboration limits; the service's budgets are measured by the service
    (kernel time of the replay, literal weight), so the submission is scored exactly as without them."""
    src = SCORED_SOURCE.replace("/-- The kernel runs the single rule on all 64 inputs",
                                "set_option maxHeartbeats 0 in\nset_option maxRecDepth 100000 in\n/-- The kernel runs the single rule on all 64 inputs")
    assert src != SCORED_SOURCE
    r = submit(scored_variant(tmp_path, "options", src), work)
    assert r["status"] == "accepted" and r["scoring"]["status"] == "scored" and r["scoring"]["length"] == 4112, r


LONG_BILL = """import Protected.N_max2_tiny_v8_s0_c0
import CompactCheck.Soundness
import CompactCheck.CountedOps

namespace Candidate.LongBill
open CompactCheck Protected.N_max2_tiny_v8_s0_c0

/-- One multiply-add per index, on the embedding's 32 entries in turn: one charge each. -/
def macs (I : Interp) (acc : I.V) : List Nat → I.M I.V
  | [] => pure acc
  | i :: is => do
    let x ← I.weight "embedding.weight" (i % 32)
    let acc' ← I.muladd "mac" acc x x
    macs I acc' is

def body (I : Interp) (xs : List Nat) : I.M I.N := do
  let _ ← macs I I.zero xs
  pure I.nzero

def D : Checker := fun I => body I (List.range @K@)

/-- For every list of indices, so that checking soundness never evaluates the run on the concrete one. -/
theorem body_zero (env : Env) (xs : List Nat) (c : Cost) (n : Nat) (c' : Cost)
    (h : (body Interp.counting xs).run env c = some (n, c')) : n = 0 := by
  simp only [body, Interp.counting_bind, Interp.counting_pure, CostM.run_bind] at h
  split at h
  · simp only [CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    exact h.1.symm
  · cases h

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task := by
  intro w c n cost h
  have hD : D Interp.counting = body Interp.counting (List.range @K@) := rfl
  rw [CostM.exec, hD] at h
  have := body_zero ⟨w, c⟩ (List.range @K@) [] n cost h
  omega

@OPTION@theorem D_instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (0, @K@) := by decide +kernel

theorem performance : Target := Nat.zero_le _

end Candidate.LongBill
"""


def long_bill(tmp_path: Path, name: str, k: int, option: str) -> Path:
    """A scored candidate on the tiny linear network claiming nothing, whose checker makes k one-unit charges."""
    d = variant(tmp_path, name, lean=LONG_BILL.replace("@OPTION@", option).replace("@K@", str(k)),
                module_path="Candidate/LongBill.lean", base=SCORED)
    (d / "Candidate" / "Max2TinyScored.lean").unlink()
    m = json.loads((d / "manifest.json").read_text())
    m.update(claimed_count=0, theorem="Candidate.LongBill.performance", modules=["Candidate/LongBill.lean"],
             scored={"checker": "Candidate.LongBill.D", "sound": "Candidate.LongBill.D_sound",
                     "instance": "Candidate.LongBill.D_instance", "certificate": [], "claimed_bill": k})
    (d / "manifest.json").write_text(json.dumps(m))
    return d


def test_a_long_bill_is_one_decided_instance_with_the_recursion_limit_raised(work, tmp_path):
    """27 October: Lean's default recursion limit (maxRecDepth 512) stops `decide +kernel` on a bill of a few
    thousand charges, which the bill's list of `Cost.add` builds one charge at a time, when the kernel checks
    the fact as Lean compiles it; the open lane's first attention pilot built a model of its checker and run
    lemmas to get past it. The option raises the limit while the candidate compiles; the service's replay does
    not need it. Since 13 November a submission is compiled without the kernel's check, so the limit no longer
    applies there: 5,000 one-unit charges are accepted and scored with or without the option (bill 5,000,
    extract 80). A development compile, which keeps the kernel's check, still needs it."""
    r = submit(long_bill(tmp_path, "long-bill-default", 5000, ""), work)
    assert r["status"] == "accepted" and r["scoring"]["status"] == "scored", r
    r = submit(long_bill(tmp_path, "long-bill-raised", 5000, "set_option maxRecDepth 1000000 in\n"), work)
    assert r["status"] == "accepted", r["reason"]
    s = r["scoring"]
    assert s["status"] == "scored", s["reason"]
    assert s["bill"] == 5000 and s["length"] == 5000 + 80


def test_a_candidate_cannot_change_its_sources_during_evaluation(work, tmp_path):
    """The sources the service compiles are its own copy, read-only in the box: a candidate that tries to
    rewrite them while compiling fails to compile, and the copy is what was submitted."""
    src = SOURCE.replace("namespace Candidate.Max2Tiny",
                         '#eval IO.FS.writeFile "Candidate/Max2Tiny.lean" "theorem Candidate.Max2Tiny.performance : True := trivial"\n\nnamespace Candidate.Max2Tiny')
    d = variant(tmp_path, "race", lean=src)
    r = submit(d, work)
    assert r["status"] == "rejected" and "does not compile" in r["reason"], r["reason"]
    copies = sorted((work / "submissions").glob("race-*/Candidate/Max2Tiny.lean"))
    assert copies and copies[-1].read_text() == src


def test_renaming_or_hiding_a_definition_does_not_hide_its_data(work, tmp_path):
    """The size budget is measured over the checker's computational closure, whatever the names: a
    private definition, an underscore name or a `match_1` name carrying a copy of the weights is still
    counted, and the submission refused scoring."""
    sys.path.insert(0, str(HERE))
    import accept
    sys.path.pop(0)
    accept._repo = REPO
    net = json.loads(accept.export_network(REPO, "tests/max2_tiny", "max2_tiny-v8-s0", work).read_text())
    nums = [abs(v) for w in net["weights"] for v in w["ints"]]
    for name, decl in (("private-table", "private def table"), ("underscore-table", "def _table"), ("match-name", "def match_1")):
        ident = decl.split()[-1]
        table = f"{decl} : List Nat := [" + ", ".join(str(v) for v in nums) + "]\n\n"
        src = SCORED_SOURCE.replace("/-- The checker: every input of the task's space. -/\n" + NEW_D,
                                    table + "/-- The checker: every input of the task's space. -/\ndef D : Checker := fun I => countSingles I graph task "
                                    f"(if {ident}.length = 0 then [] else allInputs task.space)")
        src = src.replace("  intro w c n cost h\n  unfold numCorrect\n  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h",
                          f"  intro w c n cost h\n  unfold numCorrect\n  simp only [D, {ident}, List.length_cons, Nat.succ_ne_zero, ite_false] at h\n  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h")
        r = submit(scored_variant(tmp_path, name, src), work, env=SMALL_BUDGET)
        assert r["status"] == "accepted", (name, r["reason"])
        s = r["scoring"]
        assert s["status"] == "refused" and "description size" in s["reason"], (name, s)
        assert s["description_size"] >= copy_bound(nums)


def test_a_table_of_booleans_or_a_church_encoding_is_refused_scoring_not_proving_anti_hiding(work, tmp_path):
    """A copy of the weights as a list of booleans (one constructor per bit) and as a Church encoding (one
    function per number applying `c0` or `c1` per bit, no numeral anywhere): the description size counts
    every node, so both weigh at least two per bit, more than the weights as numerals, and both are
    refused."""
    sys.path.insert(0, str(HERE))
    import accept
    sys.path.pop(0)
    accept._repo = REPO
    net = json.loads(accept.export_network(REPO, "tests/max2_tiny", "max2_tiny-v8-s0", work).read_text())
    nums = [abs(v) % (1 << 24) for w in net["weights"] for v in w["ints"]]
    bits = [(v >> k) & 1 for v in nums for k in range(24)]
    bools = "def table : List Bool := [" + ", ".join("true" if b else "false" for b in bits) + "]\n\n"
    # one function per number (24 applications deep; a single 1920-deep term overflows the elaborator)
    chunks = ", ".join("fun z => " + "".join(f"c{(v >> k) & 1} (" for k in range(24)) + "z" + ")" * 24 for v in nums)
    church = (f"def table (c0 c1 : Nat → Nat) (z : Nat) : Nat := [{chunks}].foldl (fun z f => f z) z\n\n"
              "def decoded : Nat := table (fun n => 2 * n) (fun n => 2 * n + 1) 0\n\n")
    for name, defs, cond in (("bool-table", bools, "table.length = 0"), ("church-table", church, "decoded = 0")):
        src = SCORED_SOURCE.replace("/-- The checker: every input of the task's space. -/\n" + NEW_D,
                                    defs + "/-- The checker: every input of the task's space. -/\ndef D : Checker := fun I => countSingles I graph task "
                                    f"(if {cond} then [] else allInputs task.space)")
        # the tables are too large for simp to unfold (recursion depth), so the condition is decided by the kernel
        proof = (f"  intro w c n cost h\n  unfold numCorrect\n  simp only [D] at h\n  rw [if_neg (by decide +kernel : ¬ {cond})] at h\n"
                 "  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h")
        src = src.replace("  intro w c n cost h\n  unfold numCorrect\n  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h", proof)
        r = submit(scored_variant(tmp_path, name, src), work, env=SMALL_BUDGET)
        assert r["status"] == "accepted", (name, r["reason"])
        s = r["scoring"]
        assert s["status"] == "refused" and "description size" in s["reason"], (name, s)
        assert s["description_size"] >= 2 * 24 * len(nums), (name, s["description_size"])


def test_branching_into_the_checkers_own_code_is_not_expressible(work, tmp_path):
    """The reviewers' counterexamples to versions 2 and 3, as written: the continuation `I.ifN bit (k 1)
    (k 0)` and the masked conditional `nadd (nmask b (k 1)) (nmask nb (k 0))`. Neither `ifN` nor `nmask`
    exists in version 4, so neither checker compiles; the only uses of a truth value are countB, nscale,
    selectV and the charged gates, none of which runs the checker's own code or conditions a count."""
    src = SCORED_SOURCE.replace("    pure (I.nadd (I.countB ok) n)",
                                "    I.ifN ok (pure (I.nadd (I.nofNat 1) n)) (pure (I.nadd (I.nofNat 0) n))")
    assert src != SCORED_SOURCE
    r = submit(scored_variant(tmp_path, "continuation", src), work)
    assert r["status"] == "rejected" and "does not compile" in r["reason"] and "ifN" in r["reason"], r["reason"]
    src = SCORED_SOURCE.replace("    pure (I.nadd (I.countB ok) n)",
                                "    let nok ← I.bnot \"m\" ok\n    pure (I.nadd (I.nmask ok (I.nofNat 1)) (I.nmask nok n))")
    assert src != SCORED_SOURCE
    r = submit(scored_variant(tmp_path, "masked-conditional", src), work)
    assert r["status"] == "rejected" and "does not compile" in r["reason"] and "nmask" in r["reason"], r["reason"]


def test_a_decision_tree_over_truth_values_bills_every_node(work):
    """The version 3 reviewer's decoder written in version 4 (examples/open_lane/max2_tiny_decision_tree):
    the path indicator passes a charged gate at every node, so a tree over k = 4 truth values of one weight
    bills 3 (2^4 - 1) = 45 gates on top of the 4 numerals and 4 comparisons that made the truth values,
    whatever its leaves compute (here nothing: count 0). This is the accounting the free mask broke."""
    r = submit(TREE, work)
    assert r["status"] == "accepted" and r["certified_count"] == 0, r["reason"]
    s = r["scoring"]
    assert s["status"] == "scored", s["reason"]
    assert s["bill"] == 53 == 2 * 4 + 3 * (2 ** 4 - 1) and s["length"] == 53 + 80


def test_the_ported_column_proof_is_scored_under_language_v4(work, tmp_path):
    """The agent's column proof ported by hand to version 4 (examples/open_lane/max2_tiny_cols23_v3): the
    interface keeps a meaningful method expressible, provable and scoreable. 23 of 64, bill 562 (the
    agent's 458 plus 104 charged gates), length 642; its description size calibrates the default budget. Its
    read lemma migrated to policy v10's reads (`migrate_reads`)."""
    r = submit(migrate_reads(PORT, tmp_path), work)
    assert r["status"] == "accepted" and r["certified_count"] == 23, r["reason"]
    s = r["scoring"]
    assert s["status"] == "scored", s["reason"]
    assert s["bill"] == 562 and s["length"] == 642 and s["description_size"] <= s["size_budget"]
    assert r["score_eligible"] is True


def test_weight_bits_counts_the_sign_and_the_significant_bits_of_each_weight():
    """weight_bits by hand: a weight's trailing zeros (the tensor's common exponent) carry nothing, its sign one
    bit, a zero weight one bit; the exporter's #const weights are not parameters. size_budget (policy v11) is
    v10's 8192 + 4 E, raised where it is lower to half of weight_bits, the share raising it to at most 16,384;
    since policy v14 no budget is above 24,576."""
    sys.path.insert(0, str(HERE))
    import accept
    sys.path.pop(0)
    net = {"weights": [{"name": "W", "ints": [0, 1, -1, 2, 12, -40, 2 ** 40]}, {"name": "#const0", "ints": [12345]}]}
    assert accept.weight_bits(net) == 1 + 2 + 2 + 2 + 3 + 4 + 2
    assert accept.size_budget(1296, 31127) == 15563  # attn-min2-v64d8-s1: half of weight_bits
    assert accept.size_budget(544, 13052) == 8192 + 4 * 544  # attn-max4-v16-s1: the base
    assert accept.size_budget(1500, 40000) == 16384  # the cap
    assert accept.size_budget(3000, 72000) == 8192 + 4 * 3000  # from E = 2,048 on, v10's budget
    assert accept.size_budget(4096, 98000) == 8192 + 4 * 4096 == 24576  # up to the cap of policy v14
    assert accept.size_budget(8256, 198333) == 24576  # and no further: v10's budget here was 41,216


def test_plan_bits_is_the_length_of_a_prefix_code():
    """plan_bits by hand (Elias gamma of each entry plus one), and its bound: a quarter of weight_bits. The honest
    plan of the windowed proof of attn-min2 v64d8 (335 window lengths up to 182) measures 775; a copy of that
    network's weights holds at least 31,127."""
    sys.path.insert(0, str(HERE))
    import accept
    sys.path.pop(0)
    assert [accept.plan_bits([v]) for v in (0, 1, 2, 3, 6, 7, 63, 2 ** 32 - 1)] == [1, 3, 3, 5, 5, 7, 13, 65]
    assert accept.plan_bits([]) == 0 and accept.plan_bits([0, 1, 2, 63, 2 ** 31]) == 83
    assert accept.plan_bits_budget(31127) == 7781
    assert accept.plan_problem([1] * 2000, 4096, 31127) is None  # 6,000 bits
    assert "holds 9000 bits" in accept.plan_problem([1] * 3000, 4096, 31127)


def test_a_table_written_with_an_alphabet_of_variables_measures_a_third_of_its_bits_a_known_gap(work, tmp_path):
    """What the description size does not bound (measured 17 November 2026). The measure counts a variable as one
    node, whichever variable it is. A function of 256 variables, bound to 0 to 255 where it is applied, is an
    alphabet: each use of a variable holds 8 bits and measures 1 (about 2 with the application around it). So
    4,096 random bytes, 32,768 bits, more than a copy of attn-min2 v64d8's weights holds, measure 11,536: under
    that network's budget (15,563, and v10's 13,376), where the same bits as numerals measure over 39,000. Charging
    a variable, a constant or a constructor the bits that name it would close this and make honest code measure
    three to four times as much, more than the weights of a network of that size. So there the size budget stops
    a plain copy and no more; what holds against a copy is the pipeline's seed check (the checker locked and run on
    a second seed, where a copy certifies nothing) with the plan's bits bounded. This test pins the gap so that a
    change of the measure shows here."""
    import random
    rng = random.Random(1)
    K, W, N = 256, 32, 4096
    syms = [rng.randrange(K) for _ in range(N)]
    body = "[]"
    for i in reversed(range(0, N, W)):
        body = "(pack " + " ".join(f"c{v}" for v in syms[i:i + W]) + " " + body + ")"
    src = ("namespace Candidate.Alpha\n\n"
           f"def pack ({' '.join(f'a{i}' for i in range(W))} : Nat) (r : List Nat) : List Nat :=\n"
           f"  {' :: '.join(f'a{i}' for i in range(W))} :: r\n\n"
           "set_option maxRecDepth 100000 in\n"
           f"def tableF ({' '.join(f'c{i}' for i in range(K))} : Nat) : List Nat :=\n  {body}\n\n"
           f"def table : List Nat := tableF {' '.join(str(i) for i in range(K))}\n\n"
           "def D : Nat := table.length\n\nend Candidate.Alpha\n")
    ws = tmp_path / "ws"
    (ws / "Candidate").mkdir(parents=True)
    (ws / "Candidate" / "Alpha.lean").write_text(src)
    r = subprocess.run([sys.executable, "-B", str(HERE / "accept.py"), "compile", str(ws), "Candidate/Alpha.lean",
                        "--repo", str(REPO), "--work", str(work), "--model", "tests/max2_tiny", "--network",
                        "max2_tiny-v8-s0", "--claimed", "64", "--checker", "Candidate.Alpha.D"],
                       capture_output=True, text=True, timeout=1800)
    out = json.loads(r.stdout)
    assert r.returncode == 0 and out["ok"] is True, out
    p = out["scoring_preview"]
    assert p["counted_language"] == "ok" and p["offending"] == [], p
    assert p["description_size"] == 11536 and 8 * N == 32768, p  # 2.84 bits per unit
    # the constant measured here is a number, not a checker: the preview's last-bits test says so and runs nothing
    assert p["last_bits"]["passes"] is None and "not a checker" in p["last_bits"]["reason"], p


def test_the_default_size_budget_is_below_a_copy_of_the_weights_on_every_zoo_setting():
    """The policy's arithmetic, with no Lean, for one network of every size setting of every model in the
    pipeline's zoo, its weights as the exporter writes them (integers over the tensor's common power-of-two
    exponent). A copy holds at least weight_bits (each weight's sign and significant bits; at most the
    exporter's bits plus a sign per weight), which is over the default budget everywhere, and at least twice
    it where the share decides it. No budget is below v10's 8192 + 4 E up to the cap of policy v14 (24,576, which
    decides from 4,097 parameters on, where no network has a proof yet), and from E = 2,048 to the cap none
    differs. Above the cap the budget no longer grows with the network, so the room it leaves for a copy falls as
    the network grows: beside 3,000 units of other code, at the 2.84 bits a unit can hold, 14 bits per weight at
    4,352 parameters, 7 at 8,256 and 5 at 12,352 (13 at both before the cap). An exact copy, 24 bits per weight,
    did not fit at those sizes before the cap either; a rounded one fits with it too, coarser, which the budget
    does not keep out at the zoo's sizes.
    The tiny test network (E = 80) is the exception the other size tests work around with SMALL_BUDGET."""
    sys.path.insert(0, str(HERE))
    import accept
    sys.path.pop(0)
    from fractions import Fraction
    import numpy as np
    seen = []
    for manifest in sorted((REPO / "models").glob("*/zoo/manifest.json")):
        m = json.loads(manifest.read_text())
        settings = set()
        for n in m["networks"]:
            if n["setting"] in settings:
                continue
            settings.add(n["setting"])
            z = np.load(manifest.parent / n["weights"])
            weights = []
            for key in z:
                arr = np.asarray(z[key])
                if arr.dtype.kind != "f":
                    continue
                fr = [Fraction(float(v)) for v in arr.reshape(-1).astype(np.float64)]
                den = max([f.denominator for f in fr] + [1])
                weights.append({"name": key, "ints": [int(f * den) for f in fr]})
            E = sum(len(w["ints"]) for w in weights)
            bits = accept.weight_bits({"weights": weights})
            budget, v10 = accept.size_budget(E, bits), 8192 + 4 * E
            row = (manifest.parent.parent.name, n["setting"], E, bits, budget)
            seen.append(row)
            assert bits <= sum(copy_bound(w["ints"]) for w in weights) + E, row
            cap = accept.SIZE_BUDGET_CAP
            assert cap == 24576 and budget == min(cap, max(v10, budget)), row
            assert budget >= min(v10, cap) and (E < 2048 or budget == min(v10, cap)), row
            assert bits > budget and (budget in (v10, cap) or bits >= 2 * budget), row
            if v10 > cap:
                # capped: a copy of the weights does not fit in the whole budget, even written as densely as the
                # densest encoding measured (32,768 bits in 11,536 units: the alphabet of 256 variables below)
                assert budget == cap and bits >= 4 * cap and budget * 32768 < bits * 11536, row
    assert len(seen) >= 6 and any(8192 + 4 * E > 24576 for _, _, E, _, _ in seen), seen
    # the cap is over every real checker measured (14,043, run attn-min2-ptl-1) and over the budget of every network
    # that has a proof (attn-min2 v64d8: 15,563)
    assert accept.size_budget(1296, 31127) == 15563 and accept.size_budget(8256, 198000) == 24576


def test_a_copy_of_the_weights_is_refused_under_the_default_policy_on_a_real_network(work, tmp_path):
    """max2 v64 (E = 1,088): a numeral table of the weights' significant bits alone (each integer without its
    trailing zeros, with no sign and no exponent, so less than any usable copy) in the general layer measures
    above the default budget, half of weight_bits = 13,010 (v10's 8192 + 4 E is 12,544), and is refused
    scoring, with no test hook. The checker certifies nothing (count 0, so the kernel work is small); the proof
    stays verified."""
    sys.path.insert(0, str(HERE))
    import accept
    sys.path.pop(0)
    accept._repo = REPO
    net = json.loads(accept.export_network(REPO, "models/max2", "max2-v64-s0", work).read_text())
    nums = [abs(v) >> ((abs(v) & -abs(v)).bit_length() - 1) if v else 0 for w in net["weights"] for v in w["ints"]]
    assert len(nums) == 1088
    src = "\n".join([
        "import Protected.N_max2_v64_s0_c0", "import CompactCheck.Soundness", "import CompactCheck.CountedOps", "",
        "namespace Candidate.Max2V64Copy", "open CompactCheck Protected.N_max2_v64_s0_c0", "",
        "def table : List Nat := [" + ", ".join(str(v) for v in nums) + "]", "",
        "def D : Checker := fun I => pure (I.nofNat (table.length - table.length))", "",
        "theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),",
        "    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task := by",
        "  intro w c n cost h",
        "  have h' : (pure (table.length - table.length) : CostM Nat).run ⟨w, c⟩ [] = some (n, cost) := h",
        "  rw [CostM.run_pure] at h'",
        "  simp only [Option.some.injEq, Prod.mk.injEq, Nat.sub_self] at h'",
        "  rw [← h'.1]", "  exact Nat.zero_le _", "",
        "theorem D_instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (0, 0) := by",
        "  decide +kernel", "",
        "theorem performance : Target := by",
        "  show claimedCount ≤ numCorrect graph weights task", "  exact Nat.zero_le _", "",
        "end Candidate.Max2V64Copy", ""])
    manifest = {"model": "models/max2", "network": "max2-v64-s0", "claimed_count": 0,
                "theorem": "Candidate.Max2V64Copy.performance", "modules": ["Candidate/Max2V64Copy.lean"],
                "scored": {"checker": "Candidate.Max2V64Copy.D", "sound": "Candidate.Max2V64Copy.D_sound",
                           "instance": "Candidate.Max2V64Copy.D_instance", "certificate": [], "claimed_bill": 0}}
    d = variant(tmp_path, "v64-copy", lean=src, manifest=manifest, module_path="Candidate/Max2V64Copy.lean", base=SCORED)
    (d / "Candidate" / "Max2TinyScored.lean").unlink()
    r = submit(d, work)
    assert r["status"] == "accepted" and r["certified_count"] == 0, r["reason"]
    s = r["scoring"]
    assert s["status"] == "refused" and "description size" in s["reason"], s
    assert s["weight_bits"] == accept.weight_bits(net) and s["size_budget"] == accept.size_budget(1088, s["weight_bits"]) == 13010, s
    assert s["description_size"] >= copy_bound(nums) > s["size_budget"], s


def test_the_service_reports_the_identity_its_receipts_carry(work):
    """`accept.py identity` is what a run records when it starts and checks when it resumes: the project's
    commit, the toolchain, trusted-source and policy digests every receipt carries, and the binary."""
    r = subprocess.run([sys.executable, "-B", str(HERE / "accept.py"), "identity"], capture_output=True, text=True, timeout=600)
    ident = json.loads(r.stdout)
    assert set(ident) == {"commit", "dirty", "toolchain", "lean_project", "policy", "acceptcheck"}
    receipt = submit(SCORED, work)
    assert receipt["status"] == "accepted"
    for k in ("commit", "toolchain", "lean_project", "policy", "acceptcheck"):
        assert receipt["digests"][k] == ident[k], k
    assert "dirty" not in receipt["digests"]
    with_hook = subprocess.run([sys.executable, "-B", str(HERE / "accept.py"), "identity"], capture_output=True, text=True,
                               timeout=600, env={**os.environ, **SMALL_BUDGET})
    assert json.loads(with_hook.stdout)["policy"] != ident["policy"]  # the hooks are part of the policy


PILOT2 = PROJECT / "examples" / "open_lane" / "pilot2_max2_tiny"
PILOT2_EXPECTED = {  # from the receipts the Mac's service wrote on 22 October 2026 (receipt-mac-2026-10-22.json),
    # under policy v3; under policy v4 (the audited match-compiler constants allowed) ColFull is scored
    "r1_ColFull": (64, "scored", 943, 1023),
    "r1_ColFull2": (64, "scored", 951, 1031),
    "r1_Col21": (21, "scored", 455, 535),
    "r2_Six": (6, "scored", 189, 269),
    "r2_Col32": (32, "scored", 453, 533),
    "r3_Col38": (38, "scored", 456, 536),
    "r4_Full64": (64, "scored", 639, 719),
}


@pytest.mark.parametrize("name", sorted(PILOT2_EXPECTED))
def test_the_pilot_2_proofs_reproduce_their_receipts(work, name, tmp_path):
    """The agent's seven submissions of pilot 2 (examples/open_lane/pilot2_max2_tiny), resubmitted: the same
    count, scoring status, bill and length as the receipts of the run, and the description size recorded
    there, under the default policy, their read lemmas migrated to policy v10's reads (`migrate_reads`)."""
    count, status, bill, length = PILOT2_EXPECTED[name]
    r = submit(migrate_reads(PILOT2 / name, tmp_path), work)
    assert r["status"] == "accepted" and r["certified_count"] == count, (name, r["reason"])
    s = r["scoring"]
    assert s["status"] == status, (name, s)
    assert s.get("bill") == bill and s.get("length") == length, (name, s)
    recorded = json.loads((PILOT2 / name / "receipt-mac-2026-10-22.json").read_text())["scoring"]
    if recorded.get("description_size") is not None:
        assert s.get("description_size") == recorded.get("description_size"), (name, s, recorded)
    else:
        assert recorded["status"] == "refused" and "Eq.ndrec_symm" in recorded["reason"]  # policy v3's refusal, kept as the record


MATCH_HELPERS = """inductive Term where
  | pair (a b : Nat)
  | single (a : Nat)

/-- A match on numeral patterns and a two-list recursion with a wildcard: Lean's match compiler injects
    constants for both. -/
def dropPair : List Term → List Term
  | [] => []
  | t :: ts => (match t with | .pair 6 7 => [] | _ => [t]) ++ dropPair ts

def zipAdd : List Nat → List Nat → List Nat
  | a :: as, b :: bs => (a + b) :: zipAdd as bs
  | _, _ => []

def termInputs : List Term → List Input
  | [] => []
  | .pair a b :: ts => [a, b] :: termInputs ts
  | .single a :: ts => [a, a] :: termInputs ts

"""


def test_the_match_compilers_constants_are_allowed(work, tmp_path):
    """Pilot 2's first proof was refused scoring for `Eq.ndrec_symm`, injected by a `match` on numeral
    patterns; a wildcard in a two-list recursion injects `Nat.ne_of_beq_eq_false`. Both are audited and on
    the allowlist (cost-v4): a checker whose plan goes through such helpers is scored."""
    inputs = "termInputs (dropPair [.pair 6 7, .pair 0 1, .single 2]) ++ (zipAdd [1, 2] [2, 3]).map (fun a => [a, a])"
    src = SCORED_SOURCE.replace("/-- The checker: every input of the task's space. -/\n" + NEW_D,
                                MATCH_HELPERS + "/-- The checker: a plan through the helpers. -/\ndef D : Checker := fun I => countSingles I graph task (" + inputs + ")")
    src = src.replace("  intro w c n cost h\n  unfold numCorrect\n  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h",
                      "  intro w c n cost h\n  unfold numCorrect\n  have h' := countSingles_le ⟨w, c⟩ _ [] n cost h\n"
                      "  refine le_trans h' (List.Subperm.countP_le _ (List.subperm_of_subset ?_ ?_))\n  · decide +kernel\n  · intro x hx; revert x; decide +kernel")
    src = src.replace("theorem D_instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (64, 64 * 63) := by",
                      "theorem D_instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (4, 4 * 63) := by")
    src = src.replace("  exact D_sound weights cert 64 cost h", "  exact D_sound weights cert 4 cost h")
    src = src.replace("N_max2_tiny_v8_s0_c64", "N_max2_tiny_v8_s0_c4")
    manifest = json.loads((SCORED / "manifest.json").read_text())
    manifest["claimed_count"] = 4
    manifest["scored"]["claimed_bill"] = 4 * 63
    r = submit(variant(tmp_path, "match-constants", lean=src, manifest=manifest, module_path="Candidate/Max2TinyScored.lean", base=SCORED), work)
    assert r["status"] == "accepted", r["reason"]
    s = r["scoring"]
    assert s["status"] == "scored", s
    assert s["bill"] == 4 * 63


def test_a_checker_may_build_a_graph_of_the_linear_family_and_run_single_on_it(work, tmp_path):
    """Policy v4: `Graph.mk` and the linear family's `Op` constructors are allowed, so a checker can call
    `single` on a graph of its own over the same weight names (a cheaper well-formedness guard than the
    protected graph's forward pass, as pilot 2's agent proposed). `single` prices any graph at its
    forward-pass cost; the soundness statement stays about the protected graph. Here the checker's graph
    equals the protected one, so the bill is the brute-force bill and the proof goes through the equality."""
    helpers = ("def myGraph : Graph := { positions := 2, values := 8, nodes := [.input, .sum 0 1, "
               ".linear 1 \"embedding.weight\" none, .linear 2 \"linear.weight\" none, .linear 3 \"unembedding.weight\" none], "
               "output := 4 }\n\ntheorem myGraph_eq : myGraph = graph := rfl\n\n")
    src = SCORED_SOURCE.replace("/-- The checker: every input of the task's space. -/\n" + NEW_D,
                                helpers + "/-- The checker: brute force through the checker's own graph. -/\n"
                                "def D : Checker := fun I => countSingles I myGraph task (allInputs task.space)")
    src = src.replace("  intro w c n cost h\n  unfold numCorrect\n  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h",
                      "  intro w c n cost h\n  unfold numCorrect\n  simp only [D, myGraph_eq] at h\n  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h")
    r = submit(scored_variant(tmp_path, "own-graph", src), work)
    assert r["status"] == "accepted" and r["certified_count"] == 64, r["reason"]
    s = r["scoring"]
    assert s["status"] == "scored", s
    assert s["bill"] == 64 * 63 and r["policy_version"] == "open-lane-policy-v14"


def test_weight_sizes_are_read_for_free(work, tmp_path):
    """Policy v4: `I.weightSize` gives a tensor's data length, free like `weightShape`, so a checker
    establishes well-formedness (length equals the product of the shape) by a concrete comparison instead
    of a forward pass. Here the brute force runs only if the three weights are well formed; the bill is
    unchanged, the reads cost nothing, and `CostM.weightSize_spec` is what a soundness proof uses."""
    helpers = ("def wellFormed (I : Interp) (name : String) : I.M Bool := do\n"
               "  let sh ← I.weightShape name\n  let n ← I.weightSize name\n  pure (sh.foldl (· * ·) 1 == n)\n\n")
    src = SCORED_SOURCE.replace("/-- The checker: every input of the task's space. -/\n" + NEW_D,
                                helpers + "/-- The checker: brute force, after a free well-formedness check. -/\n"
                                "def D : Checker := fun I => do\n  let a ← wellFormed I \"embedding.weight\"\n"
                                "  let b ← wellFormed I \"linear.weight\"\n  let c ← wellFormed I \"unembedding.weight\"\n"
                                "  if a && b && c then countSingles I graph task (allInputs task.space) else pure I.nzero")
    src = src.replace("  intro w c n cost h\n  unfold numCorrect\n  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h",
                      "  intro w c n cost h\n  unfold numCorrect\n  have h' : (D Interp.counting).run ⟨w, c⟩ [] = some (n, cost) := h\n"
                      "  simp only [D] at h'\n  obtain ⟨a, c1, -, h'⟩ := bind_some h'\n  obtain ⟨b, c2, -, h'⟩ := bind_some h'\n"
                      "  obtain ⟨c3, c4, -, h'⟩ := bind_some h'\n  split at h'\n"
                      "  · exact countSingles_le ⟨w, c⟩ (allInputs task.space) c4 n cost h'\n"
                      "  · rw [CostM.run_pure] at h'\n    simp only [Option.some.injEq, Prod.mk.injEq] at h'\n    rw [← h'.1]\n    exact Nat.zero_le _")
    src = src.replace("theorem D_sound :", """theorem bind_some {α β : Type} {x : CostM α} {f : α → CostM β} {env : Env} {c c' : Cost} {b : β}
    (h : (x >>= f).run env c = some (b, c')) :
    ∃ a c1, x.run env c = some (a, c1) ∧ (f a).run env c1 = some (b, c') := by
  rw [CostM.run_bind] at h
  split at h
  · rename_i a c1 ha; exact ⟨a, c1, ha, h⟩
  · cases h

theorem D_sound :""")
    r = submit(scored_variant(tmp_path, "weight-sizes", src), work)
    assert r["status"] == "accepted" and r["certified_count"] == 64, r["reason"]
    s = r["scoring"]
    assert s["status"] == "scored", s
    assert s["bill"] == 64 * 63


# ---- general networks (attention) ---------------------------------------------------------------------
def test_a_scored_proof_on_an_attention_network_splits_its_instance(work):
    """Brute force on the tiny attention network (tests/attn_max2_tiny, 64 inputs, 136 weights) through the
    general single rule `I.gsingle`, its instance proved from one kernel-decided fact per input: one
    `decide +kernel` over the 64 forward passes does not fit in memory. Scored at 64 times 191, the Python
    checker's charge for a single leaf of this network (scripts/test_gsingle_cost.py), plus extract 136."""
    r = submit(ATTN, work)
    assert r["status"] == "accepted", r["reason"]
    assert r["certified_count"] == 64 and r["execution_assurance"] == "kernel_checked_instance"
    s = r["scoring"]
    assert s["status"] == "scored", s["reason"]
    assert s["bill"] == 64 * 191 and s["extract"] == 136 and s["read"] == 0
    assert s["length"] == 64 * 191 + 136
    assert set(s["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}


WEIGHT_ARITH = """import Protected.N_attn_max2_tiny_v8d4_s1_c0
import CompactCheck.Soundness
import CompactCheck.CountedOps
import CompactCheck.CountedGeneralSound

namespace Candidate.WeightArith
open CompactCheck Protected.N_attn_max2_tiny_v8d4_s1_c0

/-- The protected graph with two additions on the weights alone appended: U + U, then that doubled. -/
def g2 : Graph := { graph with nodes := graph.nodes ++ [.add 24 24, .add 26 26] }

def D : Checker := fun I => do
  let _ ← I.gsingle g2 task [0, 0]
  pure I.nzero

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task := by
  intro w c n cost h
  simp only [D, CostM.exec, Interp.counting_bind, Interp.counting_pure, CostM.run_bind] at h
  split at h
  · simp only [CostM.run_pure, Interp.counting_nzero, Option.some.injEq, Prod.mk.injEq] at h
    omega
  · cases h

theorem D_instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (0, 255) := by decide +kernel

theorem performance : Target := Nat.zero_le _

end Candidate.WeightArith
"""


ATTN_ZERO = """import Protected.N_attn_max2_tiny_v8d4_s1_c0
import CompactCheck.Soundness
import CompactCheck.CountedOps

namespace Candidate.AttnZero
open CompactCheck Protected.N_attn_max2_tiny_v8d4_s1_c0

def D : Checker := fun I => pure I.nzero

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task := by
  intro w c n cost h
  simp only [D, CostM.exec, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
  omega

theorem D_instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (0, 0) := by decide +kernel

theorem performance : Target := Nat.zero_le _

end Candidate.AttnZero
"""

def zero_candidate(tmp_path: Path, name: str, lean: str, module: str, namespace: str, bill: int) -> Path:
    """A scored candidate on the attention example's network claiming nothing: its count is 0 whatever the
    weights, so only its bill and the service's scoring decisions are under test."""
    d = variant(tmp_path, name, lean=lean, module_path=f"Candidate/{module}.lean", base=ATTN)
    (d / "Candidate" / "AttnTinyScored.lean").unlink()
    m = json.loads((d / "manifest.json").read_text())
    m.update(claimed_count=0, theorem=f"{namespace}.performance", modules=[f"Candidate/{module}.lean"],
             scored={"checker": f"{namespace}.D", "sound": f"{namespace}.D_sound", "instance": f"{namespace}.D_instance",
                     "certificate": [], "claimed_bill": bill})
    (d / "manifest.json").write_text(json.dumps(m))
    return d


def test_arithmetic_on_the_weights_in_a_graph_of_the_checkers_own_is_charged(work, tmp_path):
    """Review of 23 October: `gsingle` left out of its bill the operations that do not depend on the input, and
    a checker may pass a graph of its own built from the protected graph's nodes, so arithmetic on the weights
    alone was free (the reviewer's submission did 24 such additions for 7 units). Every operation is charged on
    every call now: the protected graph's forward pass (191) and the two additions appended, 32 entries each."""
    d = zero_candidate(tmp_path, "weight-arith", WEIGHT_ARITH, "WeightArith", "Candidate.WeightArith", 255)
    r = submit(d, work)
    assert r["status"] == "accepted" and r["certified_count"] == 0, r["reason"]
    s = r["scoring"]
    assert s["status"] == "scored" and s["bill"] == 191 + 2 * 32, s


def test_a_network_with_charged_operations_on_the_weights_alone_is_refused_scoring(tmp_path):
    """cost-v3 charges a general network's operations that do not depend on the input once per proof, to
    extract; the open lane does not compute that charge yet, so the service refuses scoring on such a network
    (the proof stays verified). The zoo has none, so the test exports the example's network, appends one
    (the unembedding added to itself) and places it where the service caches exported networks."""
    work = tmp_path / "work"
    (work / "networks").mkdir(parents=True)
    net_json = work / "networks" / "attn_max2_tiny-v8d4-s1.json"
    r = subprocess.run([sys.executable, "-B", str(HERE / "export_network.py"), str(REPO), "tests/attn_max2_tiny",
                        "attn_max2_tiny-v8d4-s1", str(net_json)], capture_output=True, text=True, timeout=1800)
    assert r.returncode == 0, r.stderr[-1000:]
    net = json.loads(net_json.read_text())
    unembed = [i for i, op in enumerate(net["graph"]["nodes"]) if op.get("op") == "param" and op.get("weight") == "U"]
    assert unembed, "the example's network has no unembedding weight U"
    net["graph"]["nodes"].append({"op": "binary", "fn": "add", "left": unembed[0], "right": unembed[0], "name": "extra"})
    net_json.write_text(json.dumps(net))
    d = zero_candidate(tmp_path, "attn-zero", ATTN_ZERO, "AttnZero", "Candidate.AttnZero", 0)
    r = submit(d, work)
    assert r["status"] == "accepted" and r["certified_count"] == 0, r["reason"]
    s = r["scoring"]
    assert s["status"] == "refused" and "do not depend on the input" in s["reason"], s
    assert s["extract"] is None and s["size_budget"] is None


INTERVAL_CALL = """import Protected.N_attn_max2_tiny_v8d4_s1_c0
import CompactCheck.Soundness
import CompactCheck.CountedOps
import CompactCheck.CountedGeneralSound

namespace Candidate.IntervalCall
open CompactCheck Protected.N_attn_max2_tiny_v8d4_s1_c0

GINTERVAL_DEF

def D : Checker := fun I => do
  let _ ← GINTERVAL graph task [⟨3, 3⟩, ⟨3, 3⟩]
  pure I.nzero

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task := by
  intro w c n cost h
  simp only [D, CostM.exec, Interp.counting_bind, Interp.counting_pure, CostM.run_bind] at h
  split at h
  · simp only [CostM.run_pure, Interp.counting_nzero, Option.some.injEq, Prod.mk.injEq] at h
    omega
  · cases h

theorem D_instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (0, 367) := by decide +kernel

theorem performance : Target := Nat.zero_le _

end Candidate.IntervalCall
"""

# the interval rule called by name, and through a primitive projection an elaborator builds (no constant named)
BY_NAME = INTERVAL_CALL.replace("GINTERVAL_DEF\n\n", "").replace("GINTERVAL", "I.ginterval")
BY_PROJECTION = INTERVAL_CALL.replace("GINTERVAL_DEF", """open Lean Elab Term Meta in
/-- `ginterval` of an interpreter as a primitive projection, which names no projection function. -/
elab "rawGInterval " i:term : term => do
  let e ← elabTerm i (some (mkConst ``CompactCheck.Interp))
  let fields := getStructureFields (← getEnv) ``CompactCheck.Interp
  let some idx := fields.findIdx? (· == `ginterval) | throwError "no field ginterval"
  return mkProj ``CompactCheck.Interp idx e""").replace("GINTERVAL graph", "(rawGInterval I) graph")


@pytest.mark.parametrize("how,lean", [("by-name", BY_NAME), ("by-projection", BY_PROJECTION)])
def test_the_interval_rule_for_general_networks_is_scored_only_in_the_maximum_knowledge_condition(work, tmp_path, how, lean):
    """`I.ginterval`, the fixed rules lane's interval rule for general networks, is an operation of the maximum-knowledge
    condition only (accept/allowlist-maximum.txt). Called once on a box of one input of the tiny attention
    network (charge 367: twice the forward pass's arithmetic, the lookups and the final comparison), it is
    scored under --knowledge maximum and refused scoring under the default, minimal condition, also when an
    elaborator reaches the field through a primitive projection instead of its name. The proof stays verified;
    the receipt records the condition."""
    for knowledge in ("maximum", "minimal"):
        d = zero_candidate(tmp_path / knowledge, f"interval-{how}", lean, "IntervalCall", "Candidate.IntervalCall", 367)
        r = submit(d, work, knowledge=knowledge)
        assert r["status"] == "accepted" and r["certified_count"] == 0 and r["knowledge"] == knowledge, r["reason"]
        s = r["scoring"]
        if knowledge == "maximum":
            assert s["status"] == "scored" and s["bill"] == 367, s
        else:
            assert s["status"] == "refused" and "CompactCheck.Interp.ginterval" in s["reason"], s


TOKENS_CALL = """import Protected.N_attn_max2_tiny_v8d4_s1_c0
import CompactCheck.Soundness
import CompactCheck.CountedOps
import CompactCheck.CountedGeneralSound

namespace Candidate.TokensCall
open CompactCheck Protected.N_attn_max2_tiny_v8d4_s1_c0

def D : Checker := fun I => do
  let _ ← I.gtokenIntervals graph task [[⟨3, 3⟩, ⟨3, 3⟩]]
  pure I.nzero

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task := by
  intro w c n cost h
  simp only [D, CostM.exec, Interp.counting_bind, Interp.counting_pure, CostM.run_bind] at h
  split at h
  · simp only [CostM.run_pure, Interp.counting_nzero, Option.some.injEq, Prod.mk.injEq] at h
    omega
  · cases h

theorem D_instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (0, 384) := by decide +kernel

theorem performance : Target := Nat.zero_le _

end Candidate.TokensCall
"""


def test_the_token_interval_rule_for_general_networks_is_scored_only_in_the_maximum_knowledge_condition(work, tmp_path):
    """`I.gtokenIntervals`, the fixed rules lane's token_interval rule for general networks, is an operation of the
    maximum-knowledge condition only. Called on one box of one input of the tiny attention network (charge 160
    to token_interval and 224 to tables, as the Python checker charges the leaf: scripts/test_gtokens_cost.py),
    it is scored under --knowledge maximum and refused scoring under the minimal condition."""
    for knowledge in ("maximum", "minimal"):
        d = zero_candidate(tmp_path / knowledge, "tokens-call", TOKENS_CALL, "TokensCall", "Candidate.TokensCall", 384)
        r = submit(d, work, knowledge=knowledge)
        assert r["status"] == "accepted" and r["certified_count"] == 0 and r["knowledge"] == knowledge, r["reason"]
        s = r["scoring"]
        if knowledge == "maximum":
            assert s["status"] == "scored" and s["bill"] == 384, s
        else:
            assert s["status"] == "refused" and "CompactCheck.Interp.gtokenIntervals" in s["reason"], s


def test_a_scored_proof_with_token_interval_leaves_splits_its_instance_per_leaf(work):
    """The tiny attention network certified by 15 token_interval leaves in one `I.gtokenIntervals` call
    (examples/open_lane/attn_max2_tiny_tokens): for each largest token, the inputs with it at the first
    position and those with it only at the second. The instance comes from one kernel-decided fact per leaf.
    Bill 8112 (the leaves' own work) + 1792 (the rows that depend on their token alone, once for all the leaves)
    = 9904, below brute force through `gsingle` (64 x 191 = 12224); plus extract 136."""
    r = submit(ATTN_TOKENS, work, knowledge="maximum")
    assert r["status"] == "accepted", r["reason"]
    assert r["certified_count"] == 64 and r["execution_assurance"] == "kernel_checked_instance"
    s = r["scoring"]
    assert s["status"] == "scored", s["reason"]
    assert s["bill"] == 9904 and s["extract"] == 136 and s["read"] == 0
    assert s["length"] == 9904 + 136


DEMOS = ["attn_min2_tiny_tokens_demo", "attn_max2_tiny_tokens_demo", "attn_max4_tiny_tokens_demo", "attn_min4_tiny_tokens_demo"]


@pytest.mark.parametrize("demo", DEMOS)
def test_the_token_interval_demonstrations_are_scored_under_the_maximum_condition(work, demo):
    """The worked examples a maximum-condition run shows its agent: three boxes of the other task's network
    (a complete proof of the run's own network would be a proof handed over; docs/OPEN_LANE.md). Each is
    accepted and scored at the count and bill its manifest claims."""
    d = PROJECT / "examples" / "open_lane" / demo
    m = json.loads((d / "manifest.json").read_text())
    r = submit(d, work, knowledge="maximum")
    assert r["status"] == "accepted", r["reason"]
    assert r["certified_count"] == m["claimed_count"] and r["execution_assurance"] == "kernel_checked_instance"
    s = r["scoring"]
    assert s["status"] == "scored" and s["bill"] == m["scored"]["claimed_bill"], s


def test_the_knowledge_condition_is_part_of_the_policy_digest():
    """A run records the service's identity under its condition and checks every receipt against it, so one
    frontier never mixes the conditions."""
    out = {}
    for knowledge in ("minimal", "maximum"):
        r = subprocess.run([sys.executable, "-B", str(HERE / "accept.py"), "identity", "--knowledge", knowledge],
                           capture_output=True, text=True, timeout=600)
        assert r.returncode == 0, r.stderr
        out[knowledge] = json.loads(r.stdout)
    assert out["minimal"]["policy"] != out["maximum"]["policy"]
    assert {k: v for k, v in out["minimal"].items() if k != "policy"} == {k: v for k, v in out["maximum"].items() if k != "policy"}



# ---- the seatbelt box (macOS's sandbox-exec) ------------------------------------------------------------
# The profile and the command are tested here as text, on any machine; the two tests after them run only on a
# Mac and are the box's real test (a proof accepted inside it, a write outside it refused).
def _accept_module():
    sys.path.insert(0, str(HERE))
    import accept
    sys.path.pop(0)
    return accept


def test_the_seatbelt_profile_reads_what_the_landlock_box_reads_and_writes_only_out_and_tmp(tmp_path):
    accept = _accept_module()
    ws, home, work = tmp_path / "work" / "ws", tmp_path / "home", tmp_path / "work"
    text = accept.seatbelt_profile(ws, [str(ws), "/opt/lean"], [str(home), str(work)], ["/opt/py/bin/python3", "/opt/lean/bin/lean"],
                                   ["/dev/null"])
    lines = text.splitlines()
    assert lines[:2] == ["(version 1)", "(allow default)"]
    assert "(deny network*)" in lines and "(deny process-fork)" in lines and "(deny process-exec)" in lines
    assert '(allow process-exec (literal "/opt/lean/bin/lean") (literal "/opt/py/bin/python3"))' in lines
    assert "(deny signal)" in lines and "(allow signal (target self))" in lines
    write = next(l for l in lines if l.startswith("(allow file-write*"))
    assert write == f'(allow file-write* (subpath "{ws / "out"}") (subpath "{ws / "tmp"}") (literal "/dev/null"))'
    assert lines.index("(deny file-write*)") < lines.index(write)
    # a later rule wins: the home folder and the work folder are refused, then the workspace allowed again
    deny = next(l for l in lines if l.startswith("(deny file-read*"))
    allow = next(l for l in lines if l.startswith("(allow file-read*"))
    assert f'(subpath "{home}")' in deny and f'(subpath "{work}")' in deny
    assert f'(subpath "{ws}")' in allow and '(subpath "/opt/lean")' in allow
    assert lines.index(deny) < lines.index(allow) and lines[-1] == "(allow file-read-metadata)"
    assert accept._sb('/a "b') == '"/a \\"b"'


def test_in_seatbelt_mode_the_command_starts_under_sandbox_exec(tmp_path, monkeypatch):
    accept = _accept_module()
    seen = []

    def run(argv, **kw):
        seen.append(argv)
        return subprocess.CompletedProcess(argv, 0, "", "")

    monkeypatch.setattr(accept.subprocess, "run", run)
    monkeypatch.setattr(accept, "_repo", REPO)
    monkeypatch.setattr(accept, "_work", tmp_path / "work")
    ws = tmp_path / "work" / "ws"
    ws.mkdir(parents=True)
    r = accept.run_boxed(ws, ["/opt/lean/bin/lean", "-o", "x.olean", "x.lean"], {}, "seatbelt", 60, ["/opt/lean"])
    assert r["rc"] == 0
    argv = seen[0]
    assert argv[:2] == [accept.SEATBELT, "-p"] and argv[3:] == [sys.executable, "-I", "-B", str(ws / "_boxrun.py"), str(ws / "job.json")]
    profile = argv[2]
    assert '(literal "/opt/lean/bin/lean")' in profile and f'(literal "{sys.executable}")' in profile
    deny = next(l for l in profile.splitlines() if l.startswith("(deny file-read*"))
    allow = next(l for l in profile.splitlines() if l.startswith("(allow file-read*"))
    for p in (Path.home(), REPO, tmp_path / "work"):
        assert f'(subpath "{os.path.realpath(p)}")' in deny
    assert f'(subpath "{ws}")' in allow and '(subpath "/opt/lean")' in allow
    # the box itself is _boxrun.py's: no Landlock policy in the job, the limits as in every mode
    job = json.loads((ws / "job.json").read_text())
    assert job["policy"] is None and job["limits"]["RLIMIT_AS"] == accept.MEMORY_MB << 20
    # in the other modes nothing changes
    seen.clear()
    accept.run_boxed(ws, ["/opt/lean/bin/lean"], {}, "process", 60, [])
    assert seen[0][0] == sys.executable


def test_seatbelt_is_used_only_when_asked_for_and_only_on_a_mac(monkeypatch):
    accept = _accept_module()
    monkeypatch.setattr(accept, "_repo", REPO)
    monkeypatch.setattr(accept, "seatbelt_available", lambda: False)
    with pytest.raises(accept.Infra, match="seatbelt"):
        accept.box_mode("seatbelt")
    monkeypatch.setattr(accept, "seatbelt_available", lambda: True)
    assert accept.box_mode("seatbelt") == "seatbelt"
    assert accept.box_mode("hardened") in ("landlock", "process")
    assert accept.box_mode("process") == "process"


@pytest.mark.skipif(sys.platform != "darwin", reason="seatbelt is macOS only")
def test_the_hand_built_proof_is_accepted_in_the_seatbelt_box(work):
    r = submit(EXAMPLE, work, mode="seatbelt")
    assert r["status"] == "accepted", r["reason"]
    assert r["certified_count"] == 64 and r["isolation"] == "seatbelt"


@pytest.mark.skipif(sys.platform != "darwin", reason="seatbelt is macOS only")
def test_the_seatbelt_box_blocks_writes_and_reads_outside_it(work, tmp_path):
    target = work / "receipts" / "forged-seatbelt.json"
    src = SOURCE.replace("namespace Candidate.Max2Tiny",
                         f'#eval IO.FS.writeFile "{target}" "{{}}"\n\nnamespace Candidate.Max2Tiny')
    r = submit(variant(tmp_path, "writer-seatbelt", lean=src), work, mode="seatbelt")
    assert r["status"] == "rejected" and "does not compile" in r["reason"]
    assert not target.exists()
    secret = REPO / "README.md"  # the pipeline: refused, as everything in the home folder outside the box
    src = SOURCE.replace("namespace Candidate.Max2Tiny",
                         f'#eval do let _ ← IO.FS.readFile "{secret}"; pure ()\n\nnamespace Candidate.Max2Tiny')
    r = submit(variant(tmp_path, "reader-seatbelt", lean=src), work, mode="seatbelt")
    assert r["status"] == "rejected" and "does not compile" in r["reason"]
