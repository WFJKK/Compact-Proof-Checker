# The counted language (step 2 of the open lane; version 4 of the language, policy v13, 17 November)

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
- `cert i`: free (the certificate is charged once per proof, as `read`, 1 per number). Since policy v10
  both `weight` and `cert` read through a balanced tree, for the kernel's sake only (section "Reading
  weights in the kernel" below);
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

The same closure, with the checker's description size, can be asked for during development:
`accept.py compile --checker <constant>` runs it after a successful compile and reports whether the checker
stays in the counted language (and the constants it is refused for), its description size against the budget,
measured by the same functions as `score`, and its largest definitions. It is a preview, not a verdict: the
soundness and instance theorems and the general layer's kernel time are checked only on submission.

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

Since 13 November 2026 the service asks for both in the replay that verifies the candidate,
`acceptcheck check-score`, instead of a second replay with `acceptcheck score`: the general layer first and
timed, then the rest, then the target's challenge, then these two (what is accepted and what is scored are
unchanged; the separate commands remain). And a submission's modules are compiled without the kernel's check
of each declaration (`debug.skipKernelTC`): the replay checks every constant of the candidate, so a false
`decide +kernel` fact compiles and is then rejected there (`test_a_submission_compiles_without_the_kernel_and_the_replay_is_the_check`).
On run attn-min2-ptl-1's 672-input proof the old path took 540 s to compile (the instance's decided facts
checked by the kernel as Lean added them), 505 s to check and 440 s to score: the same kernel work three times.

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

## Reading weights in the kernel (policy v10, 16 November)

In compiled code an `Array` is an array; the kernel knows `Array` only as a structure around a `List`. Up
to policy v9, `weight name i` read `t.data[i]!`: the kernel walked `i` cells for every read, and walked
again for the next one, since it remembers finished results, not partial walks. A checker that reads every
entry of a tensor of `n` entries cost the kernel about `n^2 / 2` cell steps, and the memory of all of them
until the theorem was done. On run attn-min2-ptl-3 (vocabulary 64, width 8) the reads were about 85% of
the kernel's time: a fact reading 656 entries took 11.6 s at 2.8 GB on a 2-core cloud machine, one reading
about 1,900 took 34 s at 5.2 GB.

Since v10, `weight` and `cert` read through a `ReadTree` (`Counted.lean`): a balanced binary tree of the
array's entries, built in one pass, in which entry `i` is found by going left or right at each node. Every
read of one array in a theorem asks for the same tree (`ReadTree.ofList t.data.toList`), so the kernel
builds it once per theorem and keeps it, and a read descends about `log₂ n` levels. Nothing else changes:
the reads are free, they return the same numbers, and the statements the service builds are the same.
Compiled code (`#eval`, the scoring preview) shares nothing between calls and would rebuild the tree at
every read (the round-2 checker's `#eval` took 67 s instead of 1.5 s), so `weight` and `cert` are
`@[implemented_by]` the array's own `a[i]?` (`weightImpl`, `certImpl`); `weightImpl_eq` and `certImpl_eq`
prove the two the same function. The kernel never runs the implementations.

Measured on the same 2-core machine (time of the module, peak memory of the process; same verdicts and
bills):

| | up to v9 | v10 |
| --- | --- | --- |
| round 2's 16 box facts (`FarB1`) | 190.8 s, 2.78 GB | 28.5 s, 0.77 GB |
| round 2's first row facts (`FarS1`) | 271.0 s, 5.12 GB | 38.5 s, 1.08 GB |
| round 2's last row facts (`FarS7`) | 128.2 s, 3.53 GB | 25.5 s, 0.98 GB |
| one theorem reading the first 64 / 128 / 256 / 512 entries of a 512-entry tensor, each value compared | 0.3 / 0.8 / 2.8 / 13.2 s | 0.2 / 0.2 / 0.4 / 1.1 s |
| one read in a theorem of its own (16 such theorems) | about 63 ms each | about 81 ms each |

Within a theorem the tree is built once (the cost grows with the number of reads, not their square); a new
theorem builds it again, so a fact with only a few reads pays a little more than before.

What a soundness proof uses:

- `CostM.weight_run_eq`: `(weight name i).run env c` is entry `i` of the tensor named `name`, when there is
  one (`(lookup name).bind (·.data[i]?)`), and the bill unchanged; `weight_spec` the same read backwards,
  `weight_run_of_lookup` forwards, `weight_run_get` in the form `v.val = t.get i ∧ c' = c`;
- `CostM.cert_run_eq`, `cert_spec`, `cert_run_of_lt`, `cert_run_get` likewise for the certificate.

A proof written against the old definitions (one that unfolded `CostM.weight` or `CostM.cert` and split on
its `if`) goes through after replacing the unfolding by `rw [CostM.weight_run_eq_ite]` or
`rw [CostM.cert_run_eq_ite]`: those are the old definitions, as equations. The examples kept from earlier
runs are resubmitted that way by the tests (`test_accept.py`, `migrate_reads`), their files unchanged.

## Running the specification in the kernel (`SemanticsKernel.lean`, 17 November)

The fast reads above are for a checker's reads of the weights. A proof can also need the kernel to run the
specification itself: `semOps g w x ops vals` or `semGraph g w x` (`Semantics.lean`) on numbers, or on
symbols in place of the weights, to get the network's function in closed form. Run attn-min2-ptl-3 did the
second, in three decided theorems; that module needs more memory than a 6 GB machine gives a process.

The specification's definitions are written for reading and for compiled code. For the kernel an `Array` is
a `List`:

- building: `(Array.range n).map f` (in `Tensor.ofFn` and the linear operations), `Array.map` and
  `Array.ofFn` add one entry at a time at the end of the list, so the kernel walks the list for every entry
  and keeps every step until the theorem is done. Measured on a 2-core cloud machine, over the 2.1 GB a
  module's imports take: an array of 128 entries costs 1 s and 60 MB, 256 entries 2 s and 270 MB, 512
  entries 9 s and 1.05 GB. The same list built with `List.range` and `List.map` costs nothing measurable;
- reading: `t.data.getD i 0` walks `i` cells at every read, as a checker's reads did before policy v10.

`CompactCheck/SemanticsKernel.lean` gives every operation a second definition, a copy of the specification's
text in which a tensor is built as a list (`Tensor.ofFnK`, `rangeMapK`, `Tensor.mapK`) and read through a
`ReadTree` (`Tensor.getK`, `Tensor.entryK`), and proves each equal to the specification's (`matmulOp_eqK`
and so on, up to `semOps_eqK` and `semGraph_eqK`). The specification is not changed, and nothing trusted is
added: the equations are theorems. A proof rewrites with them and lets the kernel decide the statement about
`semOpsK`:

    theorem run : (semOps g w x ops vals).map f = some r := by
      rw [semOps_eqK]; decide +kernel

Measured on that run's three theorems (time of a module with one theorem, peak memory of the process; the
imports alone are 2.4 s and 2.1 GB; same machine):

| the run of | `semOps`, as submitted | `semOpsK`, the run's tensors | `semOpsK`, tensors built from lists |
| --- | --- | --- | --- |
| operations 1 to 4 (embedding) | killed at 5.8 GB after 79 s | 18.3 s, 3.9 GB | 7.4 s, 2.8 GB |
| operations 5 to 20 (attention) | 13.6 s, 2.6 GB | 3.4 s, 2.5 GB | 3.8 s, 2.4 GB |
| operations 21 to 25 (unembedding) | 39.1 s, 5.8 GB | 19.5 s, 2.8 GB | 6.2 s, 2.6 GB |

The middle column is the run's module with `rw [semOps_eqK]` added and nothing else. What it still pays for
is its own symbolic weights, written with `Array.ofFn` (512 entries twice): a tensor a proof writes itself
is built by the kernel too, and is cheap as `((List.range n).map f).toArray` (the last column).
`examples/open_lane/max2_tiny_kernel_run` is a lemma of that form, accepted by the service.

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

and, for a planned checker, `"plan": [natural numbers]`. The certificate (integers, floats, or `[p, q]` pairs)
becomes the protected `cert`, in a module of its own named by its hash, and that hash is part of the claim
module's name; a plan becomes `plan` in the same way (the next section). The receipt's `claim_kind` is `performance` (a proof of Target) or
`auxiliary` (a lemma with any statement, accepted with no count and no score: `"kind": "auxiliary"` in the
manifest), `score_eligible` says whether it was scored, and the `scoring` block says `scored` or `refused`
(with the reason) and gives the length in `cost-v3` units:

    length = claimed_bill + extract + read,  extract = number of weight entries,  read = certificate size

A proof that the kernel verified and a budget of the general layer then refused (description size, kernel
time) has no `bill` and no `length`, and keeps `measured_bill` and `measured_length` (policy v12): what the
instance proves and the length it gives. No frontier or score uses them; they are there so that a refused
proof's measurement is not lost. A scored proof has the same numbers in both pairs.

The mapping to `cost-v3`'s categories: `single`, `interval`, `gsingle` (billed as `single`), `ginterval`
(billed as `interval`) and `gtokenIntervals` (billed as `token_interval` and `tables`) through the counted
operations, `extract`
and `read` as above, the arithmetic categories through the primitives. `tree` has no counterpart: the
structure of a scored proof is its program, bounded by the literal budget below rather than charged. The
fixed rules lane does not charge a proof file's plan either, so the same proof costs the same in both lanes.

## The protected modules: the network apart from the claim (policy v13, 17 November)

The protected module of a claim, `Protected.N_<network>_c<claimed>`, has the certificate's and the plan's
hashes in its name. Every change of the claimed count, the certificate or the plan gives it another name, so
every candidate module that imports it has to be edited and compiled again, the kernel facts about the
weights among them. In run attn-min2-ptl-3 that was about 20 compiles in a round.

The claim's module stays what it was, text for text. Beside it `scripts/make_protected.py` now writes the
same definitions in modules whose names do not change with the claim:

| module | holds | changes with |
| --- | --- | --- |
| `Protected.N_<network>_c<claimed>[_h..][_p..]` | `graph`, `weights`, `task`, `cert`, `plan`, `claimedCount`, `Target` | the network, the claim, the certificate, the plan |
| `Protected.N_<network>` | `graph`, `weights`, `task` | the network |
| `Protected.N_<network>_h<hash>` | `cert` | the certificate |
| `Protected.N_<network>_p<hash>` | `plan` | the plan |

What a candidate gains: a module that imports `Protected.N_<network>` alone does not depend on the claim. A
checker, its soundness proof and every kernel fact about the weights can be such modules; a fact about the
certificate imports the certificate's module, which changes only when the certificate does. Only the module
that proves `Target` (and states the instance in the service's form) names the claim's module.
`Protected.N_<network>.weights` and the claim's `weights` are two constants with one definition, term for
term, so a fact about the first is a fact about the second: Lean and the kernel see it by unfolding both and
finding the same term (`exact`, `show`, `rfl`). `examples/open_lane/max2_tiny_split` is the brute-force
proof in that shape; the tests compile its fact once and then prove another claimed count against it without
compiling it again.

Why the claim's module does not import the network's and rename its constants (the first version of this
change did, with `abbrev`): a proof that unfolds `graph` by name (`simp only [graph, ...]`, `unfold graph`)
then stops at the network's name instead of reaching the operations. A proof kept from an earlier run broke
that way. With the definitions written out in both modules, everything written against the claim's module
compiles as it did.

How it is built: the network's, certificate's and plan's modules are compiled once each
(`<work>/protected/parts/<module>`, cached by source), and their object files are copied beside the claim's
module (`<work>/protected/<claim module>/out`), because Lean looks for every module of the package `Protected`
in the first folder of its search path that has that package. A candidate is compiled against that one folder
and may import the protected modules of its own submission and no other.

Wide networks: a weight tensor of 2,048 entries (width 32, vocabulary 64) needs more than Lean's default
recursion depth, and one of 4,096 entries (vocabulary 128) more than its compiler's default step limit. The
protected module of such a network did not compile, so the open lane stopped at width 8. The modules now set
both for the weights (`set_option maxRecDepth ... in`, `set_option maxHeartbeats 0 in`; the service limits a
compile's time itself). Measured on a 2-core cloud machine: the two modules of attn-min2-v64-s0 (8,257
weights) compile and check in 78 s, those of attn-min2-v128-s0 (12,353 weights) in 143 s. The claim's module
is about half of that, and it is compiled again for every new claim: at these widths a change of the
claimed count costs a minute before the candidate's own modules.

What is trusted: the claim's module, as before. `acceptcheck protected` evaluates its `graph`, `weights` and
`task` and compares them with the network file, and every statement the service checks (the target, the
soundness statement, the instance) is written with its constants. The other three modules are a convenience
and need not be trusted: a fact about one of their constants counts only where the kernel finds that constant
equal to the claim's.

What stays as it was: the general layer may use `graph` and `task` (of the network's module or the claim's)
and no other protected constant; the weights, the certificate and the plan reach a checker only through the
interpreter and the instance. Nothing about the score changes: the same proof has the same bill, length and
description size in one module or in three (a test compares them).

### A theorem held by two modules

Lean derives a definition's equation lemmas (`f.eq_1`, `f.eq_def`) in the module that first unfolds `f`, under
`f`'s name. Two modules that unfold `f` and do not import each other each hold a copy, and Lean imports both:
the same theorem. The service refused such a proof ("the candidate declares Candidate.Far.rows.eq_2 twice",
attn-min2-ptl-3, round 1). Since policy v13 a second copy of a theorem with the same universe parameters and
the same statement is skipped: the kernel replays the first, and everything that uses the name is checked
against that one. A definition in two modules, or one name with two statements, is refused as before: there
the copy a later stage reads would be the candidate's choice.

## Planned checkers (policy v9, 13 November 2026)

A checker often needs data computed offline that says where to look: which inputs go into which group, where a
loop stops. Written into the checker's code it counts toward the description size, and a certificate cannot
carry it (`I.cert` returns an abstract number, not an index). A planned checker takes it as an argument:

    D : List Nat → Checker
    theorem D_sound : ∀ (p : List Nat) (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
        CostM.exec (D p Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task
    theorem D_instance : CostM.billed (D plan Interp.counting) ⟨weights, cert⟩ = some (N, L)

`acceptcheck score-planned` asks the kernel for these two statements. The plan is

- free: it is ordinary Lean data the checker reads, as the fixed rules lane's plan is free (cost-v4); turning
  an entry into a number for arithmetic goes through `I.lit`, charged 1, as reading a certificate number is;
- not trusted: the soundness theorem holds for every plan, and the general layer may not mention the protected
  module's `plan` (only `graph` and `task`), so only the instance runs the checker on it;
- bounded as the fixed rules lane bounds its tree: at most 4 entries per input plus 10,000, each below 2^32
  (`plan_problem` in `accept.py`; the bounds are in the policy digest);
- bounded in information (policy v12, 17 November): `plan_bits`, the plan's length in a prefix code (Elias
  gamma of each entry plus one: 0 costs 1 bit, 1 and 2 cost 3, 63 costs 13), is at most a quarter of
  `weight_bits` (below).

A plan says which checks run where, every check's work on the network's numbers is charged where it runs, and a
soundness proof cannot rely on what the plan says. But a plan's entries are plain numbers, and a checker may
compute on them for free. A plan that held a copy of the weights, which the checker compared with the weights
at about one charged operation each, would let the forward pass itself run on the copy uncharged, with a
soundness proof that holds for every plan (a plan that is not a copy certifies nothing). The entry bounds do
not exclude that: 4 entries per input of 32 bits are far more than the weights. The information bound does: a
copy holds at least `weight_bits`, and a plan a quarter of that at most. Honest plans are far below it: the
plan of attn-min2 v64d8's windowed proof (335 window lengths) measures 775 bits against a bound of 7,781.
The receipt and the development preview give `plan_bits` and `plan_bits_budget`.

`examples/open_lane/max2_tiny_planned` chooses 60 of the 64 inputs by a plan of 64 flags (bill 3,780, length
3,860; 184 bits); the tests show that a soundness theorem for one plan only, or one that names the protected
plan, is refused scoring, as is a plan over its bounds. Unplanned submissions are checked exactly as before.

## General-layer safeguards

The general layer is the checker, its soundness proof and everything they depend on. Beyond the closure
check, the service enforces, as policy (recorded in the receipt's policy digest):

- no reference to a protected constant other than `graph` and `task` (the network module's or the claim
  module's) from the general layer (`acceptcheck score` rejects it; the closure check catches it in `D`
  first);
- a description-size budget: the size of the checker's computational closure (the checker and the
  definitions it uses, transitively through definitions and never through theorems: what it computes is
  a function of these bodies and of the interpreter), every node of every body counted 1, a numeral 1 per
  bit, a string 8 per byte, measured as a tree (a repeated subterm counts each time), with no exemption by
  name, is at most the network's budget (below). A reviewer showed that data can live in constructors
  (`[true, false, ...]`) and in the shape of applications alone (`fun c0 c1 z => c0 (c1 (c0 z))`), so the
  whole term is measured, and the rates make a number of `b` bits cost at least `b` however it is written
  (a numeral or a string `b`, constructors or applications at least `2 b`). This bounds description length;
  it does not show the absence of compressed information;
- a kernel budget: replaying the general layer (timed on its own, before the rest) takes at most 120 s.

These bound what the general layer can hide; they do not prove that nothing is hidden. The adversarial
tests in `scripts/test_accept.py` say so in their names.

### The size budget (policy v11, 16 November)

What the budget blocks: a checker that holds a copy of the weights in its own code, checks the copy against
the weights at about one charged operation per weight, and then computes on the copy in free arithmetic.
So the budget is set from the least a copy holds, `weight_bits`: for each weight its sign and its
significant bits, from its highest to its lowest nonzero bit (the trailing zeros that the tensor's common
exponent adds carry nothing; where the bits sit is not counted, so a real copy holds more). On the zoo these
bits do not compress (lzma, bz2 and zlib save under 1%) and the signs are balanced; a float32 weight has
about 24 of them.

    budget = max(8192 + 4 E, min(W / 2, 16384))    (W / 2 rounded down)

with `W` = `weight_bits` and `E` the parameter count (the `#const` weights are in neither).

- Where half of `W` decides the budget, a checker holds at most half of what the weights are, and a copy
  measures at least twice the budget. Half, because a quantity computed from tensors that hold more than
  half the bits stays out of reach: in the zoo's attention networks the embedding and the unembedding,
  which every logit needs, hold 47 to 79% of the bits, and where half of `W` decides the budget (v24,
  v64d8) a copy of both leaves under 700 units for the checker's code, or none.
- Where `8192 + 4 E` decides it, the network is small (attention at v16, E = 544) and an honest checker is
  about as large as the weights; the budget is v10's there. A copy is still over it (about 1.25 times),
  but a copy of the embedding and the unembedding alone fits beside 4,000 units of code, as it did before.
  On the tiny test network (E = 80) the weights are smaller than any checker and the budget separates
  nothing (its tests use a smaller base and no share through environment hooks, recorded in the policy
  digest).
- The cap keeps the share from raising the budget of a large network: from E = 2,048 on, `8192 + 4 E` is
  over every honest checker so far (the largest measured 14,043), and half a copy would mostly be room for
  a partial copy. No budget is lower than v10's.

| network | E | `W` | v10 | v11 |
| --- | --- | --- | --- | --- |
| attn-min2 v64d8 (s1) | 1,296 | 31,127 | 13,376 | 15,563 |
| max2 v64 (s0) | 1,088 | 26,020 | 12,544 | 13,010 |
| attn-max4 v24 (s0) | 1,200 | 28,857 | 12,992 | 14,428 |
| xorformer-majority n12h1d8 (s0) | 393 | 20,814 | 9,764 | 10,407 |
| attn-max4 v16 (s1) | 544 | 13,052 | 10,368 | 10,368 |
| attn-min2 v64 (s0) | 8,256 | 198,155 | 41,216 | 41,216 |

`scripts/test_accept.py` checks the rule on one network of every size setting of the zoo (a copy holds more
than the budget, at least twice where the share decides; no budget below v10's) and refuses on max2 v64 a
checker whose code holds only the significant bits of the weights (no signs, no exponents) under the default
policy. Receipts carry `weight_bits` beside `size_budget`.

### What the size budget does not bound (measured 17 November)

The rates above were meant to make a table of `b` bits measure at least `b`. They do not. The measure counts a
variable, a constant or a constructor as one node, whichever it is, so a large set of them is an alphabet. A
function of 256 variables, bound to 0 to 255 where it is applied, holds 8 bits in each use of a variable, which
measures 1 (about 2 with the application around it):

| 32,768 random bits written as | description size |
| --- | --- |
| numerals of 32 bits | 39,239 |
| 4,096 uses of 256 variables, 32 to an application | 11,536 |

That is 2.84 bits per unit, and under the budget of attn-min2 v64d8 (15,563 in v11, 13,376 in v10), whose
weights hold 31,127 bits. A candidate's own constants or the constructors of its own type do the same.
Charging every such node the bits that name it would close this, and would make honest code measure three to
four times as much: more than the weights of a network of that size. So on such a network no size budget both
lets an honest checker through and keeps a copy out, whatever the measure. The budget stops a plain copy
(numerals, strings, booleans, Church encodings), and that is all it is relied on for.

What holds against a copy is not a size. The pipeline's seed check locks the checker and runs it, unchanged,
on a second network: a copy in the code certifies nothing there, since the code was fixed before that
network was shown, and everything the agent writes for the second network is the instance, of which the
plan (bounded in information, above) is the only free data. `scripts/test_accept.py` pins the measurement
(`..._a_known_gap`), so that a change of the measure shows.

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
