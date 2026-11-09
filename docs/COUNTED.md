# The counted language (step 2 of the open lane; version 4 of the language, policy v7, 23 October)

How a scored open-lane proof gets a length: its checker `D` is written against an abstract interpreter
whose operations are the only way to touch a number of the network, the service runs it with the
interpreter that charges `cost-v3`'s prices, a mechanical check of `D`'s definition makes sure it reaches
no other interpreter, and the kernel evaluates the result on the protected weights.

## The problem

Length must be the operation count of `cost-v3`, not time, and the service must control the bill: `D` must
not be an arbitrary Lean function that reports how much work it did. A plain monad does not do it: a
`StateM Nat` computation can call any pure Lean function for free, including one that inspects the weights.

## The design (`Counted.lean`, `CountedOps.lean`)

A checker is a function of an interpreter:

    abbrev Checker := (I : Interp) → I.M I.N

`Interp` (CountedOps.lean) is a structure of abstract types and operations: a monad `M`, numbers `V`,
truth values `B`, counts `N`; `weight`, `weightShape`, `weightSize`, `cert`, `certSize`, `lit`, `zero`; `add`, `sub`, `muladd`, `neg`, `min`,
`max`; `lt`, `le`, `eq`; `exp`; `charge`, `fail`; `btrue`, `bfalse`, `countB`, `nscale`, `selectV`,
`bnot`, `band`, `bor`; `nzero`, `nsucc`, `nadd`, `nofNat`; and the checker's own rules as operations,
`single` and `interval` (linear networks), `gsingle` (any network the general checker follows, such as
attention; below), and `ginterval` and `gtokenIntervals` (the interval and token_interval rules on such
networks, in the maximum-knowledge condition only; below). The checker's own code is ordinary Lean on lists, `Nat` indices and strings
around these calls, and it has to typecheck for every `I`: so it can never look inside a value of `I.V`,
`I.B` or `I.N`. There is no branching on a truth value: it can only become a count (`countB`, or
`nscale k`: a concrete `k` if true), a choice between two numbers (`selectV`, charged) or another truth
value through a charged gate. So nothing learned about the network ever decides what the checker's own
code does next, and the bill the interpreter keeps is the whole cost of the computation. The shapes of
the weights (`weightShape`) and the certificate's size are concrete and may be branched on: they are
public structure, not the network's numbers.

Counts are terminal. The operations that make an `N` are `nzero`, `nsucc`, `nadd`, `nofNat` (concrete
numbers) and `countB`, `nscale` (a concrete multiple of one truth value); none takes a count together
with a truth value or a number, and none takes a count and returns anything but a count. So every count
is a sum of concrete numbers and concrete multiples of truth values that charged operations produced, and
a count never encodes a computation on the network: a product of two truth values exists only through a
charged gate. The full list of signatures is the structure itself (CountedOps.lean); the test
`test_a_decision_tree_over_truth_values_bills_every_node` shows what the rule costs.

`Interp.counting` is the interpreter the service runs: `M` is `CostM` (Counted.lean, a structure around
`Env → Cost → Option (α × Cost)` with the weights and the certificate in `Env` and the bill in `Cost`),
`V` is `Q` (a structure around `ℚ`), `B` is `Bool`, `N` is `Nat`. Its charges are `cost-v3`'s:

- `add`, `sub`, `muladd`, `neg`, `min`, `max`: 1 each; `lt`, `le`, `eq`: 1 each;
- `weight name i`: free (the weights are charged once per proof, as `extract`, E); `weightShape` and
  `weightSize` (a tensor's shape and data length): free, structural metadata, not numbers of the network.
  With them a checker establishes that the weights are well formed (length equals the product of the
  shape) by a concrete comparison; before policy v4 (22 October) the only way was a whole forward pass
  through `single`, 63 operations on the tiny network, which every one of pilot 2's proofs paid once;
- `cert i`: free (the certificate is charged once per proof, as `read`, 1 per number);
- `lit n` for a numeral: 1 (as a number read from the proof file);
- `exp`: the exponential's enclosure (`Exp.lean`), charged 3, as `cost-v3` charges a softmax entry;
- `charge category n`: adds to the bill (a program can only make itself longer);
- `single graph task x`: the single-input rule, charged `singleCost` (one exact forward pass and the
  comparison, exactly what `cost-v3` charges a `single` leaf); `interval graph task box`: the interval
  rule on a box, charged `intervalCost`; both for linear networks;
- `gsingle graph task x`: the single-input rule on a general network (attention), charged what `cost-v3`
  charges a `single` leaf of such a network (below);
- `ginterval graph task box`: the interval rule on a general network, charged what `cost-v3` charges an
  `interval` leaf of such a network; maximum-knowledge condition only (below);
- `gtokenIntervals graph task boxes`: the token_interval rule on a list of boxes, one verdict per box,
  charged what `cost-v3` charges those `token_interval` leaves in one proof; maximum-knowledge condition
  only (below);
- loops, conditionals on `Nat`, lists and arrays, `nsucc`, `nadd`: free, as the Python checker's
  bookkeeping is free.

`CostM.exec (D Interp.counting) env : Option (Nat × Cost)` is the result and the bill; `CostM.billed`
the result and the bill's total, which is what the instance theorem states. Every operation of the
counting interpreter is a `CostM` function with a specification lemma (`CostM.single_spec`,
`CostM.interval_spec`, `run_bind`, `run_pure`, `exec_of_billed`), and `Interp.counting` is reducible, so a
soundness proof unfolds `D Interp.counting` to those functions and never looks inside the monad.

### Why this shape, after three reviews

The first version (20 October, morning) was a concrete monad, `D : CostM Nat`, with `Bool` results from
the charged comparisons and free `Nat` arithmetic: a reviewer showed that bits from comparisons can be
turned back into numbers by free arithmetic, so a checker could binary-search every weight at about 50
charged operations each and then run the network for nothing. The second version (that evening) made
numbers, truth values and counts abstract but kept `ifN : B → M N → M N → M N` and free gates: the
reviewer showed that `I.ifN bit (k 1) (k 0)` hands the bit to the checker's own code `k` through which
branch runs, whatever the branch returns, and that gates alone give bit-level arithmetic. Version 3 (21
October) removed branching and charged the gates, but kept a free mask `nmask : B → N → N`: the reviewer
showed that `nadd (nmask b (k 1)) (nmask nb (k 0))` is a conditional on counts, so a recursive decoder
selects `f` of the number a list of truth values spells, for nothing, with `f` any Lean function. Hence
version 4: no operation takes a count and a truth value; a truth value becomes a count only as a concrete
multiple (`nscale`), and a product of truth values costs a gate. The decoder written in version 4
(`examples/open_lane/max2_tiny_decision_tree`) bills every node of its tree. This is the shape of the
split-tree checker too, whose structure comes from the certificate and whose results only become counts.

## The check (`acceptcheck closure`)

The service walks the constants `D` uses, transitively through the candidate's own definitions (not into
proofs: a theorem computes nothing), and requires every other constant to be on an allowlist
(`accept/allowlist.txt`, part of the trusted base and of the policy digest). The allowlist holds the
interface (`Interp` and its fields, `instMonadInterp`, `Checker`), the monad classes, the structural
functions of core Lean on `Nat`, `Bool`, `List`, `Array`, `Option`, `Prod`, `Fin` and `String`, and the
checker's own structural types (inputs, boxes, the task's shape). The protected module's `graph` and
`task` are allowed (the soundness statement mentions them); its `weights`, `cert`, `claimedCount` and
`Target` are not. Not on the list: `Interp.counting`, anything of `CostM` or `Q`, anything of `ℚ` or
`ℝ`, `Classical.*`, `cast`, `Eq.mpr` and the other ways to decide or rewrite an abstract equation. A
`D` that uses anything else is refused scoring, with the names listed; the proof stays verified.

Why this is enough: the abstraction does the work (above); the allowlist makes sure the checker does not
reach the counting interpreter or a classical decision by name, which are the only ways around it.

Policy v4 (22 October 2026, after pilot 2 and the reviewer's round 7) added three things to the allowlist,
each with a regression test in `scripts/test_accept.py`: `Graph.mk` and the `Op` constructors of the
linear family (`input`, `sum`, `linear`, `add`), so a checker may build a graph over the same weight
names and call `single` on it, which `single` prices at that graph's forward-pass cost while the soundness
statement stays about the protected graph; and two constants Lean's `match` compiler injects,
`Eq.ndrec_symm` (a transport along an equation, produced by numeral patterns; a checker can only transport
along equations between concrete values, since no operation yields an equation between abstract ones) and
`Nat.ne_of_beq_eq_false` (a theorem, produced by a wildcard in a recursion over two lists). The pilot's
first proof had been refused for the former. The policy's version is in every receipt (`policy_version`)
and in the policy digest; the prices themselves (`cost-v3`) are unchanged.

## The two statements (`acceptcheck score`)

The service builds both statements itself and asks the kernel to accept the candidate's theorems at
exactly these types, as it does for the target:

    Challenge.sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
        CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task

    Challenge.instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (claimedCount, claimedBill)

The instance is always kernel-checked (`decide +kernel` in the candidate; the service never runs
candidate code). Proofs about `D` use `run_bind`, `run_pure`, the operations' specification lemmas
(`single_spec`, `interval_spec`) and `exec_of_billed`, which turns the instance into the hypothesis of
soundness, so the target follows inside the candidate.

## Why the reported cost is the cost

Proving that a checker's count is right says nothing about its bill, so the bill is never reported by the
candidate: the instance theorem `CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (n, L)` is
accepted by the kernel at a statement the service builds, so `L` is what the counting interpreter charges
on the protected weights, as the kernel computes it. What makes that charge the whole cost is the
interface: every number reaches `D` as an abstract `I.V`, every truth value is an abstract `I.B`, and
neither can decide what `D`'s own code does next or be turned into anything but counts, numbers and
truth values through charged operations. So no work on a value of the network can happen outside the
bill. The description-size budget bounds the free structure around it; it is a bound, not a proof. A receipt's `execution_assurance` is `kernel_checked_instance` for this reason: the count and the
bill are both kernel-checked for the exact checker, certificate and weights; nothing of a candidate is ever
executed by the service.

## The instance in one theorem: Lean's recursion limit (27 October)

`decide +kernel` makes the kernel run the counting interpreter on the protected weights, so the instance
needs no lemma about the bill and no model of the checker. Lean's default recursion limit
(`maxRecDepth`, 512) stops that evaluation once the bill has a few thousand charges: the bill is built one
`Cost.add` at a time and evaluated at the end, and the kernel reports `(kernel) deep recursion detected,
use set_option maxRecDepth <num> to increase the limit` (a test checker of one-unit charges passed at
2,000 and failed at 3,000). The option applies while the candidate is compiled; the service's replay
(`Kernel.Environment.replay`) does not apply it and accepts the proof. So a candidate writes

    set_option maxRecDepth 1000000 in
    theorem D_instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (n, L) := by
      decide +kernel

Through the service, a checker of 5,000 one-unit charges is rejected without the option and accepted with
it in 23 s (`test_a_long_bill_is_one_decided_instance_with_the_recursion_limit_raised`); one of 30,000 was
accepted in 70 s; the compile of one of 60,000 was killed at over 4 GB on a machine of 7 GB (memory, below). The first open-lane pilot on the tiny
attention network (26 October) built an exact-rational model of its checker and run lemmas to get past this
limit, at the cost of rounds; the option makes that unnecessary. Splitting (below) is the way past memory,
not past the recursion limit.

A soundness proof can meet the same evaluation: a `simp` or `split` on the run of `D` with its concrete list
of inputs can leave the kernel a term whose check evaluates that run (the test checker's first soundness
proof failed this way). The test states its lemma for every list of indices and reaches
`D Interp.counting` through a `rfl` equation and `rw`, as the examples do.

## Attention networks: the general single rule and split instances (23 October)

`single` runs the linear checker; on a network with attention its cost function has no price for softmax
and the rule fails, so on such a network not even brute force could be written. `gsingle graph task x`
(`CountedGeneral.lean`) is the single rule for every network the general checker of `General.lean`
follows, the fixed rules lane's checker for these networks (`checkGeneral_sound`): it runs the network on one
input with that checker's exact dyadic arithmetic, `exp` and softmax enclosed in rational bounds, and
certifies the input if the label's lower bound is above every other output's upper bound. Its charge is
`cost-v3`'s for a `single` leaf of a general network (`core/check/general.py`):

- a product with the one-hot input (a lookup): the output's size; any other matrix product: the output's
  size times the inner dimension;
- a sum, difference, product, addition, negation or `exp`: the output's size; a sum over a dimension: the
  output's size times (the summed length - 1); a softmax: 3 per entry;
- indexing, transposing, reshaping, concatenating, stacking, parameters: nothing;
- the final comparison of the label's logit with the others: (outputs - 1).

Every operation is charged on every call. `cost-v3` charges the operations that do not depend on the input
once, to `extract`; in the zoo's attention networks they are all structural (parameters, transposes,
indexing), which cost nothing, so a call's charge is `cost-v3`'s single leaf exactly. The open lane does not
compute such a once-per-proof charge yet, so the service refuses scoring on a protected network that has
charged ones. A checker may pass `gsingle` a graph of its own, built from the protected graph's nodes, and
there an operation on the weights alone must cost what it computes: the first version (1bd760f) left
input-independent operations out of the bill, and a review on 23 October did 24 additions on the weights
for 7 units through a graph of its own (`test_arithmetic_on_the_weights_in_a_graph_of_the_checkers_own_is_charged`).
Charging every call can only overcharge. `extract` for a general network is its number of weights, not
counting the scalar constants the exporter adds (`#const`), as in `cost-v3`.
`scripts/test_gsingle_cost.py` compares the charge and the verdict with the Python checker's single leaf
on every development network of the attention models; `compactcheck gsingle` prints them.

Specifications: `CostM.gsingle_correct` (`CountedGeneralSound.lean`): a call that returns true means the
network classifies the input correctly, from `generalSingle_correct`; `CostM.gsingle_run_of`: a decided
fact about `gsingleRun` on the weights gives the call's run and charge.

**Split instances.** On the tiny attention network (`tests/attn_max2_tiny`: 64 inputs, 136 weights) the
brute-force instance cannot be one `decide +kernel`: within one theorem the kernel's memory grows with
every forward pass (about 0.1 GB each) and is released only when the theorem is done, and the run did not
fit in 8 GB. One theorem per call keeps it flat: `examples/open_lane/attn_max2_tiny_scored` (generated by
`scripts/gen_attn_brute_example.py`) proves one fact per input (`run1 [a, b] = some (true, 191)`, each
`decide +kernel`), a glue lemma by induction over the inputs (`countSingles_run`: the run of the checker
is the runs of its calls in sequence, through `run_bind`, `run_pure` and `gsingle_run_of`), and the
instance from the glue. The service's statement does not change; only its proof is compositional. The
example compiles in about two minutes at 2.5 GB and is scored at 64 times 191 plus extract 136.

One trap: the kernel must never be asked to compare two different `CostM.run` terms by unfolding. It
unfolds a structure projection before anything else, and unfolding this one runs the whole checker, the
evaluation the split avoids (43 s and 5.7 GB on the tiny network when an `exact` relied on unfolding
`CostM.exec` and `D`). Rewrite with the definitions' equations instead (`rw [CostM.billed, CostM.exec]`,
and the checker's own definition as a separate `rfl` equation), so that the terms compared are identical.

The service compiles candidates with sequential elaboration (`-DElab.async=false`): with Lean's default,
every theorem is a task, and a module of many theorems makes Lean start threads whose stacks reserve more
address space than the box can allow (64 GB was not enough for the example's 64 facts). The constants
built are the same.

## Knowledge conditions (23 October, policies v6 and v7)

An open-lane run is one of two experimental conditions, set per run (`--knowledge minimal | maximum` to the
service; `open_lane.knowledge` in the pipeline's run config):

- **minimal**: the base allowlist (`accept/allowlist.txt`). On a network with attention a checker has
  `gsingle`, the arithmetic and comparison primitives and `exp`; any bound over a group of inputs it builds
  and proves itself.
- **maximum**: the base allowlist plus `accept/allowlist-maximum.txt`: the fixed rules lane's group rules (one
  bound for a whole box of inputs) on general networks, as operations, proved sound and priced as `cost-v3`
  prices the leaf: `ginterval` (policy v6) and `gtokenIntervals` (policy v7). `token_convex` (not yet in
  Lean) is to follow.

The two runs differ only in what the agent is given, so their difference measures how much the agent
depends on the supplied rules. The condition is part of the policy digest and recorded in every receipt
(`knowledge`); a run records the service's identity under its condition and checks every receipt against
it, so one frontier never mixes the two. In the minimal condition a checker that uses `ginterval` is
refused scoring, also when it reaches the field without naming it: the closure check counts a primitive
projection of a trusted structure (`Expr.proj CompactCheck.Interp i I`, which an elaborator can build) as
the projection function of field `i` (`test_the_interval_rule_for_general_networks_is_scored_only_in_the_maximum_knowledge_condition`).

`ginterval graph task box` (`CountedGeneral.lean`) runs the general checker's interval leaf
(`generalInterval`): the one-hot input is the box (per position, the tokens `lo..hi`), its product with a
weight matrix gives per position the smallest and largest row entry, and everything after is interval
arithmetic; the box is certified when the label, constant on it, has a lower bound above every other
output's upper bound. A box whose label is not constant answers false and costs nothing, as the Python
checker never runs the rule there. The charge (`gopCostBox`): the lookup from the box, per position `d`
for one token and `2 d (hi - lo + 1)` otherwise (`d` the matrix's columns); every other operation twice the
single rule's price; the final comparison. Specifications: `CostM.ginterval_correct` (a true answer means
every input of the box is answered correctly, from `generalInterval_correct`) and `CostM.ginterval_run_of`
(for split instances). `compactcheck ginterval` prints verdict and charge per box;
`scripts/test_gsingle_cost.py` compares both with the Python checker's interval leaf on every development
network of the attention models (55 of 55).

## The token_interval rule (23 October, policy v7)

`gtokenIntervals graph task boxes` (`TokensCost.lean`) runs the general checker's token_interval leaf
(`generalTokenInterval`, `Tokens.lean`) on each box of a list and returns one verdict per box, `false` for
a box whose label is not constant (no charge there, as in Python). The leaf keeps each position's rows
apart per token for as long as the graph allows (rows that depend on one position's token, a constant plus
weighted rows, per-input values where only one position varies), as `core/check/tokens.py` does; its
soundness is `generalTokenInterval_correct`, and `CostM.gtokenIntervals_correct` gives, for a run, one
verdict per box and the correctness of every input of a box answered true.

The price is `cost-v3`'s, in its two categories:

- `token_interval`: each leaf's own work, operation by operation as the Python evaluator charges it
  (`tcostOp`, which follows `tevalOp` step by step and computes each value with the same functions,
  `tcostOp_fst`), and twice the single rule's price for the operations the token rules do not cover;
- `tables`: the rows that depend on their token alone (a lookup, then constants). Python keeps them for the
  whole proof under a key (node, origin, position, and for a term the matrix products since) and charges
  each row once. Each leaf here returns its requests for such rows (`RowReq`), and `tablesCharge` charges
  them once over the list, in order.

Why a list: the bill cannot hold the memo. A checker can write any category to the bill (`charge`, and
the category argument of every primitive), so a marker meaning "these rows are paid" could be planted, or
paid for with work the checker does anyway. Within one call the memo is out of the checker's reach. A
proof that puts all its token_interval leaves in one call pays `cost-v3`'s price exactly; several calls pay
for their rows again, never less.

`scripts/test_gtokens_cost.py` compares, box by box, the verdict, the charge to `token_interval` and what
the box adds to `tables` with the Python checker over a sequence of sixteen boxes per network (single
inputs, one varying position, several, a repeated box, overlapping ranges, a box without a constant
label), one Python program for the sequence as for one proof: 58 of 58 development networks of the
attention models. The zoo's networks use only some of the token rules, and a checker may pass a graph of its
own, so `scripts/test_gtokens_synthetic.py` does the same on two small networks with random weights built to
take the others (rows times a vector, sums over a row's dimension, softmax, exponential, negation and
indexing of what leaves the domain, a constant added to a weighted sum, matrix products of per-input values;
the test checks that Python's evaluator took each of them): 6 of 6. `compactcheck gtokens` prints the same,
and each box's requests.

**Split instances.** One fact per leaf, `(dweights weights).bind (gtokenLeaf graph · task box) = some r`,
each `decide +kernel` (`TokenLeafFacts`), and `CostM.gtokenIntervals_run_of_facts` puts them together: the
call's run, whose bill is arithmetic on the facts' small lists of requests. On the tiny attention network,
`examples/open_lane/attn_max2_tiny_tokens` (generated by `scripts/gen_attn_tokens_example.py`) certifies
all 64 inputs with 15 leaves, for each largest token `m` the inputs with `m` first and those with `m` only
second, at 8,112 + 1,792 = 9,904 (brute force through `gsingle`: 12,224). The largest leaf, eight inputs
at once, takes the kernel 9.5 s; the module compiles in 76 s at 3.7 GB. The count is
`certifiedCount_le_numCorrect` (`CountedGeneralSound.lean`): no two boxes share an input (`pairwiseApart`)
and every box lies in the space (`fits`), both decided on the boxes.

A second form of the trap above: two terms that differ only by a definitional unfolding under `CostM.run`
also make the kernel unfold the run. `D Interp.counting` has type `CostM Interp.counting.N`, and a lemma
instantiated by unification may write `Nat` there; comparing the two ran all fifteen leaves in one theorem
(30 s). The example states the checker's run for any environment and bill (`D_run`, from the call's run)
and rewrites the instance with it, so no comparison of that kind meets the protected weights.

## The manifest and the receipt

A scored submission adds to its manifest

    "scored": {"checker": ..., "sound": ..., "instance": ..., "certificate": [numbers], "claimed_bill": L}

The certificate (integers, floats, or `[p, q]` pairs) becomes the protected module's `cert`, and its hash
becomes part of the module's name. The receipt's `claim_kind` is `performance` (a proof of Target) or
`auxiliary` (a lemma with any statement, accepted with no count and no score: `"kind": "auxiliary"` in the
manifest), `score_eligible` says whether it was scored, and the `scoring` block says `scored` or `refused`
(with the reason) and gives the length in `cost-v3` units:

    length = claimed_bill + extract + read,  extract = number of weight entries,  read = certificate size

The mapping to `cost-v3`'s categories: `single`, `interval`, `gsingle` (billed as `single`), `ginterval`
(billed as `interval`) and `gtokenIntervals` (billed as `token_interval` and `tables`) through the counted
operations, `extract`
and `read` as above, the arithmetic categories through the primitives. `tree` has no counterpart: the
structure of a scored proof is its program, bounded by the literal budget below rather than charged. The
fixed rules lane does not charge a proof file's plan either, so the same proof costs the same in both lanes.

## General-layer safeguards

The general layer is the checker, its soundness proof and everything they depend on. Beyond the closure
check, the service enforces, as policy (recorded in the receipt's policy digest):

- no reference to a protected constant other than `graph` and `task` from the general layer
  (`acceptcheck score` rejects it; the closure check catches it in `D` first);
- a description-size budget: the size of the checker's computational closure (the checker and the
  definitions it uses, transitively through definitions and never through theorems: what it computes is
  a function of these bodies and of the interpreter), every node of every body counted 1, a numeral 1 per
  bit, a string 8 per byte, measured as a tree (a repeated subterm counts each time), with no exemption by name, is at most `8192 + 4 E`. A
  reviewer showed that data can live in constructors (`[true, false, ...]`) and in the shape of
  applications alone (`fun c0 c1 z => c0 (c1 (c0 z))`), so the whole term is measured, and the rates make
  a number of `b` bits cost at least `b` however it is written (a numeral or a string `b`, constructors
  or applications at least `2 b`). An exported weight has 23 to 35 bits (its mantissa over the tensor's
  common exponent), so a copy of the weights costs at least about `24 E`, against `4 E` plus the base: on
  every size setting of the pipeline's zoo a copy is over the budget (max2 v64, E = 1,088: at least
  34,044 against 12,544; `scripts/test_accept.py` checks the arithmetic on the zoo and refuses an actual
  copy on max2 v64 under the default policy), while the pilot's column checker is under 8,000. This
  bounds description length; it does not show the absence of compressed information, and on the tiny
  test network (E = 80) the whole set of weights is smaller than any checker, so the budget separates
  nothing there (its tests use a smaller base through an environment hook, recorded in the policy
  digest);
- a kernel budget: replaying the general layer (timed on its own, before the rest) takes at most 120 s.

These bound what the general layer can hide; they do not prove that nothing is hidden. The adversarial
tests in `scripts/test_accept.py` say so in their names.

## Reproduction (`CountedCheck.lean`, `compactcheck cost`)

`checkProofCounted` walks a split-tree proof file as `checkProof` does and bills it with `cost-v4`'s
formulas, category by category: `extract`, `read` (the numbers of the approximations), `single`,
`interval`, `contract`, `approximate`. The plan (the tree, the rule names, the contraction chains, the
symmetry flag) is free, as a checker's code is in the open lane. The gate: on the four
max2 baselines and every proof of the recorded max2 runs, the bill equals the Python length to the unit
and the count equals the Python count (`scripts/test_cost.py`). Its soundness comes from the count being
`checkProof`'s, which is proved sound.

## What stays open

`token_convex` for general networks as a counted operation of the maximum-knowledge condition (needed to
reproduce the attention frontiers at their price in the fixed rules lane); the input-free operations of a general network in
`extract`; the `interval` operation with an approximation; a literal budget calibrated on more than the
brute-force example.
