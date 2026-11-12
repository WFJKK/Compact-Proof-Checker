# The open lane

Proofs that are not proof files. A candidate submits Lean modules that prove a protected target, the
acceptance service checks them with the kernel, and a receipt records the result. The design decisions are
in the project notes (claude/lean-open-lane-decisions.md); this page is what is built and how to use it.

## What a candidate is

A folder with `manifest.json` and the modules it names:

    {"schema": "open-lane-candidate-v1", "candidate_id": "max2-tiny-brute",
     "model": "tests/max2_tiny", "network": "max2_tiny-v8-s0", "claimed_count": 63,
     "theorem": "Candidate.Max2Tiny.performance", "modules": ["Candidate/Max2Tiny.lean"]}

The modules live under `Candidate/` and may import only each other, the protected module, `CompactCheck.*`
and `Mathlib.*`. The theorem must have the type `Protected.<module>.Target`, which is

    claimedCount ≤ numCorrect graph weights task

for the network's exported graph, exact weights and task, with `numCorrect` from `Spec.lean`: the number
of inputs the network answers correctly over the reals, ties counting as wrong.

## What the service does

`python3 scripts/accept.py submit <candidate> --repo <pipeline repo> --work <work dir> [--knowledge minimal|maximum]`

(`--knowledge` chooses the experimental condition: which operations a scored checker may use; docs/COUNTED.md,
"Knowledge conditions".)

1. Checks the manifest and the modules' imports.
2. Exports the network (`scripts/export_network.py`, the pipeline's own tracer and exact weights) and
   writes the protected module `Protected.N_<network>_c<claimed>` with `scripts/make_protected.py`; compiles
   it; and checks its constants against the network file with `acceptcheck protected`, which reads the file
   with the checker's reader (`parseNetwork`) and compares graph, weights and task.
3. Compiles each candidate module with `lean` in a box: on Linux, Landlock with no sockets, reading only the
   toolchain, this project, the workspace and system files, writing only the workspace's `out/` and `tmp/`;
   on macOS with `--mode seatbelt` (asked for by name until it has passed its test on a Mac), a
   `sandbox-exec` profile with no network, no other programs and no signals, refusing to read the home
   folder, the work folder and the pipeline except the paths the Landlock box may read, and writing only
   the workspace's `out/` and `tmp/`; elsewhere a plain process, recorded in the receipt as weak isolation.
   Time and memory limits apply.
4. Runs `acceptcheck check` in the box: it imports the trusted modules only, replays every constant of the
   candidate's `.olean` files through the kernel (`Lean.Kernel.Environment.replay`, as lean4checker does),
   and asks the kernel to accept `Challenge.proof : Target := <theorem>`. No candidate source is elaborated
   by the service's own tool, so a macro or notation in a candidate module changes nothing. A candidate
   constant with a trusted constant's name is refused, except an identical copy of a trusted theorem (same
   statement and universe parameters), which is left out of the replay: Lean generates equation lemmas such
   as `Tensor.get.eq_1` in whichever module first unfolds the definition, so a candidate module can carry
   its own copy of one the trusted modules already have.
5. Allows only the axioms `propext`, `Classical.choice` and `Quot.sound`. `sorryAx` and `Lean.ofReduceBool`
   (`native_decide`) are rejected.

The receipt (`<work>/receipts/<candidate>-<time>.json`) has `status` accepted, rejected, unsupported,
timeout or error; `certified_count` only with accepted; the axioms; the isolation mode; a digest of the
network file, of each module and of this project's source; and every step's outcome. The box cannot write
to the receipts folder.

## What is trusted

The Lean toolchain; the `.olean` files of this project and its dependencies, built here; `Spec.lean` and
the files it rests on; `scripts/export_network.py`; `scripts/make_protected.py` with the check of step 2;
`AcceptMain.lean` (the challenge and the axiom walk); and `scripts/accept.py` with its box. A candidate's
own build output is never trusted: its constants are replayed through the kernel from scratch. `partial`
and `unsafe` definitions are skipped by the replay, so a theorem that depends on one is rejected.

## The two layers

Every scored proof has the shape the example `examples/open_lane/max2_tiny_brute` has: a general layer
that never mentions the weights (a checker `D` and the theorem `D w ≤ numCorrect graph w task` for all
`w`) and a specific layer that evaluates `D` on the protected weights. In the example `D` is brute force
and the kernel evaluates it on all 64 inputs of a tiny network (`tests/max2_tiny` in the pipeline). A proof
in this shape is verified; to get a length as well, `D` is written in the counted language as a function
of the interpreter (`docs/COUNTED.md`), as `examples/open_lane/max2_tiny_scored` does, and the manifest's
`scored` block names the checker, its soundness theorem and its instance. The other examples:
`max2_tiny_agent_cols23`, the pilot agent's proof in the first counted language (verified, refused
scoring); `max2_tiny_cols23_v3`, that proof ported by hand to the current language (scored);
`max2_tiny_decision_tree`, a reviewer's counterexample written in the current language, where it bills
every node of its tree; `attn_max2_tiny_scored`, brute force on a tiny attention network through the
general single rule, its instance proved from one kernel-decided fact per input (docs/COUNTED.md, "Attention
networks"); `attn_max2_tiny_tokens`, the same network certified by 15 token_interval leaves in one call of
the maximum-knowledge condition's `gtokenIntervals`, one kernel-decided fact per leaf (docs/COUNTED.md, "The
token_interval rule").

## Kinds of submission

A manifest is a performance claim by default (a proof of `Target`); `"kind": "auxiliary"` submits a lemma
with any statement instead, which is compiled, replayed and axiom-checked the same way and accepted with no
count and no score (its statement and axioms are in the receipt). The pipeline's `compile` subcommand of
`scripts/accept.py` compiles a module of a candidate's workspace in the box for development; its output is
never evidence.

## Tests

    python3 -m pytest scripts/test_accept.py -v
    python3 -m pytest scripts/test_gsingle_cost.py -v   # the general single and interval rules' charges against Python's
    python3 -m pytest scripts/test_gtokens_cost.py -v   # the token_interval rule's charges against Python's
    python3 -m pytest scripts/test_gtokens_synthetic.py -v   # the same on the token rules the zoo never reaches

needs the project built (`lake build` of the library and `lake build acceptcheck`; candidates may import any
`Mathlib.*` module, so a machine that built only the library's own imports also needs the tactic modules the
pilot's proofs use, `lake build Mathlib.Tactic.IntervalCases Mathlib.Tactic.Linarith Mathlib.Tactic.Ring`, or
a candidate fails to compile through no fault of its own) and the pipeline
repository next to this one (or `COMPACT_PROOF_REPO`). The tests submit the example and every kind of wrong
candidate: a claim one too high, `sorry`, `native_decide`, a theorem of another type, a conditional claim,
another network's target, a macro that rewrites `theorem`, bad manifests, a module that tries to write a
receipt, and a tampered protected module.
