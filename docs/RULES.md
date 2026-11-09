# The rules lane: proof files and the verified checker

In the rules lane a proof is a JSON file: a plan that splits the inputs into boxes and names a rule for
each box. This page describes the rules, what is proved about them, and the files that implement them.
(The agent's code still calls this lane the legacy lane.) The overview is in the [README](../README.md).

## What is proved

`checkProofFile_sound` in `CompactCheck/FileSound.lean`: for every network
file and every proof file, if the checker certifies `n` inputs, then the
network answers at least `n` inputs correctly.

"Correctly" is defined in `CompactCheck/Spec.lean`, over the real numbers,
with the real exponential. The proof uses only Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`); `#print axioms
checkProofFile_sound` shows them.

The checker checks each network the way the Python checker does:

- Linear networks (`input`, `linear`, `sum`, `add`) with `checkProof`, and
  every rule of the Python checker for them: `single`, `skip` and
  `interval` leaves, and the `contract`, `symmetry` and `approximate`
  rules. The theorem for these is `check_sound` in `Soundness.lean`.
- Attention networks and the xorformer (`core/check/general.py`) with
  `checkProofGeneral`: `single`, `skip`, `interval` and `token_interval`
  leaves. The theorem for these is `checkGeneral_sound` in
  `TokensLeafSound.lean`.

A proof with a rule adopted through the rule route (such as
`token_convex`) is rejected for now, so every count the checker gives is
backed by the theorem.

An `interval` leaf certifies every input of its box at once.
`intervalLeaf_sound` in `IntervalSound.lean` proves that every input of an
accepted box passes the single test. It uses the same bounds as the Python
checker, which are exact when the output map sees the summed one-hot input
directly (after a full contraction) and all positions but one hold a single
token.

A `contract` entry replaces a chain of linear maps by their product,
computed exactly. `contractAll_sound` in `ContractSound.lean` proves that
whatever the contracted network outputs, the original network outputs too,
so the leaves can be checked on the contracted network.

With `"symmetry": true`, a certified leaf counts its inputs in sorted order
and all their reorderings. The rule needs a network that reads its input
only through a sum over the positions, and a task whose label does not
depend on the order; each task in `Task.lean` says whether it is, with a
proof. `evalGraph_perm` in `SymmetrySound.lean` proves that such a network
computes the same output on every reordering of an input.

An `approximate` entry gives a simpler matrix `P` for a linear map with
weight `W` (dense, low rank, or constant on row segments). The checker
computes `eps = max |W - P|` exactly, and interval leaves that name the
approximation bound the differences `W[l, t] - W[j, t]` by those of `P`
minus `2 eps` (`approxTerm_le` in `IntervalSound.lean`). Numbers in proof
files are read as the Python checker reads them (`parseNumber` in
`Json.lean`).

## Attention networks

Every value is a tensor of intervals, stored as Python's interval tensors
store them (`IT` in `core/check/interval.py`): integers with one power of
two per tensor. Sums, differences and products are exact, so every bound
has the value Python's has and both checkers accept the same leaves. `exp`
and `softmax` use the bounds of `Exp.lean`, as `core/check/interval.py`
computes them: a Taylor series after halving the argument, rounded
outwards at 2^-120, then squared back.

A `single` leaf runs the network on its one input. An `interval` leaf runs
it on all inputs of its box at once: the one-hot input may only be
multiplied by a weight matrix, which gives at each position the smallest
and largest entry of each column over the allowed tokens. Either leaf
certifies its inputs if the lower bound of the label's logit is above the
upper bound of every other logit.

`ExpSound.lean` proves the bounds on `exp` and `softmax`.
`GeneralOpsSound.lean` proves that each operation keeps every true value
inside its interval, and `GeneralSound.lean` puts the operations together
for single and interval leaves. The contract, symmetry and approximate
rules need a linear network; on these networks the Python checker refuses
them, and so does this one.

## token_interval leaves

`Tokens.lean` checks a `token_interval` leaf as `core/check/tokens.py`
does. An interval leaf turns each position's tokens into one box at the
first lookup. A token_interval leaf keeps the tokens apart for as long as
the graph allows: the rows of a weight matrix for each allowed token at
each position, weighted sums of such rows, and, when at most one position
varies, one value per input of the box. An operation outside these rules
turns its arguments into interval tensors, as Python does. The leaf
certifies its box if the lowest margin bound over its inputs is positive.

Lean computes the same margin bounds as Python, as exact fractions:
`scripts/compare_tokens.py` compares them box by box (175,102 random boxes
on the 60 development networks, all equal).

In a few edge cases Lean does not follow Python's rules:

- A product of rows with a constant whose intervals agree along a
  dimension, but whose real values may differ there. Python treats it as
  one weight per position, which can give a wrong bound. Lean declines
  that rule, as Python declines any other inexact constant.
- Rules that rely on a shape Python does not check. Lean checks the shape
  and declines otherwise.

None of these cases occurs on the networks of the zoo, so both checkers
certify the same inputs there.

The proof fixes an input of the box and relates every value of the leaf to
the real value on that input (`TokensSepSound.lean`,
`TokensMixSound.lean`, `TokensLeaveSound.lean`). Every operation keeps the
relation (`TokensSound.lean`), and the margin bound is below the real
margin (`lowestMargin_sound` in `TokensLeafSound.lean`).

## Files

Paths are relative to `CompactCheck/` unless they say otherwise.

| File | What it is |
| --- | --- |
| `Spec.lean` | the spec: what the network computes over the reals, `Correct`, `numCorrect` |
| `Eval.lean` | what each operation of linear networks computes, written once for any number type |
| `Semantics.lean` | what the operations of attention networks compute, also for any number type |
| `Network.lean` | networks as graphs of operations, with named weights |
| `Task.lean` | tasks: the input space, the correct label (max, min), and a proved test for boxes with one label |
| `Tensor.lean` | tensors: a shape and its entries in row-major order |
| `Walk.lean` | split trees, the walk, and `walk_partition` |
| `LinAlg.lean` | vectors and matrices over the rationals |
| `Interval.lean` | the interval rule: bounds over a box of inputs, with or without an approximation |
| `Contract.lean` | the contract rule: products of linear maps |
| `Approx.lean` | the approximate rule: checking an approximation and its error |
| `Symmetry.lean` | the symmetry rule: the test on the network, and the count |
| `Check.lean` | the checker on linear networks: contractions, approximations, then the leaves |
| `Exp.lean` | bounds on `exp` and `softmax`, as the Python checker computes them |
| `General.lean` | the checker on attention networks: interval tensors of dyadic numbers |
| `IntervalSound.lean` | `intervalLeaf_sound` and the lemmas it rests on |
| `ContractSound.lean` | `contractAll_sound` and the lemmas it rests on |
| `SymmetrySound.lean` | `evalGraph_perm` and the lemmas it rests on |
| `Soundness.lean` | `check_sound` and the lemmas it rests on |
| `ExpSound.lean` | the bounds of `Exp.lean` hold |
| `GeneralOpsSound.lean` | each operation of `General.lean` keeps the true values inside its intervals |
| `GeneralSound.lean` | single and interval leaves of attention networks are sound |
| `Tokens.lean` | the token_interval leaves, as `core/check/tokens.py` computes them |
| `TokensIndex.lean` | facts about shapes and indices for the token rules |
| `TokensSepSound.lean` | the relation between a leaf's values and the real values; rows per position |
| `TokensMixSound.lean` | weighted sums of rows |
| `TokensLeaveSound.lean` | values that leave the domain: one per input, or interval tensors |
| `TokensSound.lean` | every operation of a token_interval leaf keeps the relation |
| `TokensLeafSound.lean` | the margin bound, the leaf, and `checkGeneral_sound` |
| `FileSound.lean` | `checkProofFile_sound`: both checkers, as the program runs them |
| `Counted.lean` | the counted language of the open lane: a monad whose every operation on a number is charged |
| `CountedCheck.lean` | the checker with its bill: `cost-v4` for proof files (`compactcheck cost`) |
| `CountedOps.lean` | the checker's rules as charged operations, each with its specification |
| `CountedGeneral.lean`, `CountedGeneralSound.lean` | the single and interval rules on attention networks as counted operations (`gsingle`; `ginterval`, maximum-knowledge condition only), and the soundness of the token_interval operation |
| `TokensCost.lean` | the token_interval rule priced as `cost-v3` prices it (its rows kept once per call), as the counted operation `gtokenIntervals` (maximum-knowledge condition only) |
| `../AcceptMain.lean` | the `acceptcheck` program: the open lane's trusted check |
| `Json.lean`, `../Main.lean` | reading files, and the `compactcheck` program |
| `*Test.lean` | tests; the build fails if one fails |
| `Tutorial.lean` | Lean basics, with exercises |

## What has to be trusted

- `Spec.lean`, `Eval.lean`, `Semantics.lean`, `Network.lean`, and in
  `Task.lean` the input spaces and labels: they say what "correct" means. A task's test for boxes
  with one label, and whether its label depends on the order of the tokens,
  come with proofs and need no trust.
- `scripts/export_network.py`: it writes down the graph PyTorch traces,
  with the names proof files use for its operations, and the exact
  weights. `scripts/compare_with_python.py` (linear networks) and
  `scripts/compare_floats.py` (any network, in float64) check the result
  against PyTorch, and `compare_with_python.py` and `compare_general.py`
  against the Python checker.
- For the `compactcheck` program: the Lean compiler and the JSON reader.
  The theorems themselves are checked by Lean's kernel.

`Check.lean`, `Interval.lean`, `Contract.lean`, `Approx.lean`,
`Symmetry.lean`, `General.lean`, `Tokens.lean`, `Exp.lean`, `Walk.lean` and
`LinAlg.lean` need no trust: the theorem is about them. Nor does the network file's flag
that says which checker to use: both are sound. Nor does reading the numbers of an approximation: whatever
matrix the reader produces, its error is computed from it.

## Build

    lake build                  # library, proofs and tests
    lake build compactcheck     # the program
    lake build acceptcheck      # the open lane's service (docs/OPEN_LANE.md)

## Use

The scripts need the pipeline's Python environment (numpy, torch).

    # export a network of the pipeline
    python3 scripts/export_network.py <repo> models/max2 max2-v64-s0 max2-v64-s0.json

    # check a proof file; the last line is {"certified": n}
    .lake/build/bin/compactcheck max2-v64-s0.json proof.json

    # check a proof and bill it under cost-v4 (linear networks for now)
    .lake/build/bin/compactcheck cost max2-v64-s0.json proof.json

    # check every input on its own
    .lake/build/bin/compactcheck brute max2-v64-s0.json

    # compare with the Python pipeline on every development network
    python3 scripts/compare_with_python.py <repo> models/max2

    # the same for an attention model or the xorformer, leaf by leaf;
    # resumes from the log if interrupted
    python3 scripts/compare_general.py <repo> models/attn-max2 --log attn-max2.jsonl

    # the open lane's single and interval rules on an attention network: verdict and cost-v3 charge
    .lake/build/bin/compactcheck gsingle attn-max2-v64-s0.json inputs.json
    .lake/build/bin/compactcheck ginterval attn-max2-v64-s0.json boxes.json
    .lake/build/bin/compactcheck gtokens attn-max2-v64-s0.json boxes.json

    # token_interval margin bounds against Python's, box by box
    python3 scripts/compare_tokens.py <repo> models/attn-max2 --log tokens-attn-max2.jsonl

    # Lean's semantics in float64 against PyTorch, on every development network
    python3 scripts/compare_floats.py <repo> models/attn-max2

    # check every proof of a pipeline run (development networks) against
    # the counts the Python checker recorded; resumes if interrupted
    python3 scripts/check_run.py <repo> ~/auto-research-compact-proof-runs/<run id>
