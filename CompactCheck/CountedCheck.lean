import CompactCheck.Check
import CompactCheck.Counted

/-!
# The checker, with its bill: `cost-v4` for proof files

`checkProofCounted` certifies exactly what `checkProof` certifies (it calls it) and charges what the
Python checker charges for the same proof, operation by operation, as `core/check/cost.py` and the charge
sites of `core/check/evaluate.py`, `approx.py` and `checker.py` define it. The bill is computed from the
shapes of the (contracted) graph, the boxes of the leaves and the forms of the approximations, by the
same formulas. The gate for this file is reproduction: on every proof file the pipeline has checked, the
bill here equals the Python length to the unit (`scripts/test_cost.py`).

Soundness is `check_sound`: the count is `checkProof`'s. The bill does not affect it.

Categories, as the Python checker names them: `extract`, `read`, `contract`, `approximate`, `single`,
`interval`. Under `cost-v4` the plan is free, as a checker's code is in the open lane: the split tree,
the leaf rules, the contraction chains, the symmetry flag and the names cost nothing (`cost-v3` charged
1 per tree node, 1 per number, string or boolean of the file and 1 per leaf certified under symmetry), and
`read` charges only the numbers the proof supplies, the entries of its approximations. So the same proof
costs the same in both lanes.

This file uses only core Lean.
-/

namespace CompactCheck

/-- The parameters of the network: `extract`, E. -/
def paramCount (w : Weights Rat) : Nat :=
  (w.map fun p => p.2.data.size).sum

/-! ## The contract rule's charges

Python multiplies the chain's matrices in the cheapest order (a matrix-chain dynamic programme over the
dimensions) and charges `a * b * c` per product, then pushes the biases through, input side first, at one
matrix-vector product each and one vector addition per bias. The composition in `Contract.lean` goes left
to right; the product is the same, so only the charge follows the cheapest order here. -/

/-- The dimensions `d_0, ..., d_k` of a chain of maps with shapes `[d_1, d_0], ..., [d_k, d_{k-1}]`, input
    side first, and the cheapest cost of multiplying them out. -/
def chainCost (dims : List Nat) : Nat :=
  let n := dims.length - 1  -- the number of matrices
  if n ≤ 1 then 0 else
  -- cost i j: the cheapest cost of multiplying matrices i to j (0-based), computed bottom up by length
  let d (i : Nat) := dims.getD i 0
  let init : Array (Array Nat) := Array.replicate n (Array.replicate n 0)
  let table := (List.range (n - 1)).foldl (fun (table : Array (Array Nat)) len' =>
    let len := len' + 2  -- chains of 2, ..., n matrices
    (List.range (n - len + 1)).foldl (fun (table : Array (Array Nat)) i =>
      let j := i + len - 1
      let best := (List.range (len - 1)).foldl (fun (best : Option Nat) s' =>
        let s := i + s'
        let c := (table.getD i #[]).getD s 0 + (table.getD (s + 1) #[]).getD j 0 + d i * d (s + 1) * d (j + 1)
        match best with
        | some b => some (min b c)
        | none => some c) none
      table.set! i ((table.getD i #[]).set! j (best.getD 0))) table) init
  (table.getD 0 #[]).getD (n - 1) 0

/-- The `contract` charge of one chain of the graph: the cheapest product order, then the biases. -/
def contractCost (g : Graph) (w : Weights Rat) (chain : List Nat) : Option Nat := do
  let maps ← chain.mapM fun i =>
    match (g.nodes[i]? : Option Op) with
    | some (Op.linear _ wn bn) =>
      match List.lookup wn w with
      | some W => some (W.shape.getD 0 0, W.shape.getD 1 0, bn.isSome)
      | none => none
    | _ => none
  match maps with
  | [] => none
  | (out0, in0, _) :: _ =>
    let dims := in0 :: maps.map (·.1)  -- d_0 = in of the first map, then each map's out
    let products := chainCost dims
    -- biases, input side first: once a bias exists, every later map pushes it through (out * in),
    -- and each bias adds a vector (out)
    let biases := (maps.foldl (fun (acc : Bool × Nat) (m : Nat × Nat × Bool) =>
      let (carrying, cost) := acc
      let (out, inn, hasB) := m
      let cost := if carrying then cost + out * inn else cost
      if hasB then (true, cost + out) else (carrying, cost)) (false, 0)).2
    let _ := out0
    some (products + biases)

/-! ## The approximate rule's charges -/

/-- The `read` charge of an approximation: 1 per number the file supplies for it (every value of a
    dense form, every entry of a low-rank form's two factors, the start, end and value of every segment). -/
def approxReadCost : RawForm → Nat
  | .dense values => (values.map List.length).sum
  | .lowRank F G => (F.map List.length).sum + (G.map List.length).sum
  | .rowSegments rows => 3 * (rows.map List.length).sum

/-- Checking an approximation: `2` per entry for the error, plus the low-rank product or the segment
    index. -/
def approxBuildCost (W : Tensor Rat) : RawForm → Nat
  | .dense _ => 2 * W.data.size
  | .lowRank F _ =>
    let r := (F.headD []).length
    W.shape.getD 0 0 * r * W.shape.getD 1 0 + 2 * W.data.size
  | .rowSegments rows => 3 * W.data.size + 2 * (rows.map List.length).sum

/-- The segments of a row that meet `[lo, hi]`, clipped to it, as `_clip` in `core/check/approx.py`. -/
def clipSegments (row : List (Int × Int × Rat)) (lo hi : Nat) : List (Int × Int) :=
  row.filterMap fun (a, b, _) =>
    if b < (lo : Int) || a > (hi : Int) then none else some (max a lo, min b hi)

/-- The merge steps of two rows' clipped segments: 1 per step, as the loop of `row_min_diffs`. -/
def mergeSteps : List (Int × Int) → List (Int × Int) → Nat
  | [], _ => 0
  | _, [] => 0
  | (_, e1) :: as, (_, e2) :: bs =>
    1 + (if e1 < e2 then mergeSteps as ((0, e2) :: bs)
         else if e1 > e2 then mergeSteps ((0, e1) :: as) bs
         else mergeSteps as bs)
termination_by a b => a.length + b.length

/-- The `interval` charge of bounding one range `[lo, hi]` through an approximation (`row_min_diffs`),
    for every output `j`, given the form the file wrote. -/
def approxRangeCost (nOut l lo hi : Nat) : RawForm → Nat
  | .dense _ => 2 * nOut * (hi - lo + 1)
  | .lowRank F _ =>
    let r := (F.headD []).length
    2 * r * (hi - lo + 1) + 3 * nOut * r
  | .rowSegments rows =>
    let mine := clipSegments (rows.getD l []) lo hi
    let ops := ((List.range nOut).map fun j => mergeSteps mine (clipSegments (rows.getD j []) lo hi)).sum
    2 * ops + 2 * (nOut + 1)

/-! ## One exact forward pass (`single`) -/

/-- What the Python evaluator knows about a value when it runs one input: the one-hot input, its sum
    over the positions, or an exact tensor of this shape. -/
inductive SKind where
  | oneHot
  | summed
  | dense (shape : List Nat)

/-- The positions of the graph the output depends on. The Python checker deletes a contraction's inner
    maps; here they stay in the graph unused, so they are left out of the bill the same way. -/
def reachable (g : Graph) : List Nat :=
  go (g.nodes.length) [g.output] [g.output]
where
  go : Nat → List Nat → List Nat → List Nat
    | 0, _, seen => seen
    | fuel + 1, [], seen => let _ := fuel; seen
    | fuel + 1, i :: todo, seen =>
      let args := match g.nodes[i]? with
        | some op => op.args
        | none => []
      let new := args.filter (fun a => !seen.contains a)
      go fuel (todo ++ new) (seen ++ new)

/-- The `single` charge of one input, as `_run_concrete` charges it: a linear map on the one-hot input
    costs its output size per position (a lookup), on a vector `in * out` per leading index; a bias, a sum or
    an addition its output size; the final comparison `outputs - 1`. -/
def singleCost (g : Graph) (w : Weights Rat) : Option Nat := do
  let keep := reachable g
  let (cost, kinds) ← g.nodes.foldlM (init := (0, (#[] : Array SKind))) fun (cost, kinds) op => do
    let i := kinds.size
    let charged := keep.contains i
    match op with
    | .input => pure (cost, kinds.push .oneHot)
    | .sum a d =>
      match kinds[a]? with
      | some .oneHot => if normDim d 3 == some 1 then pure (cost, kinds.push .summed) else none
      | some .summed => none
      | some (.dense s) =>
        let dim ← normDim d s.length
        let n := s.getD dim 0
        let s' := s.eraseIdx dim
        let c := shapeSize s' * (n - 1)
        pure (if charged then cost + c else cost, kinds.push (.dense s'))
      | none => none
    | .linear a wn bn =>
      let W ← List.lookup wn w
      let out := W.shape.getD 0 0
      let inn := W.shape.getD 1 0
      let (c, s') ← match kinds[a]? with
        | some .oneHot => some (g.positions * out, [1, g.positions, out])
        | some .summed => some (g.positions * out, [1, out])
        | some (.dense s) => some (shapeSize s * out, s.dropLast ++ [out])
        | none => none
      let _ := inn
      let c := if bn.isSome then c + shapeSize s' else c
      pure (if charged then cost + c else cost, kinds.push (.dense s'))
    | .add a b =>
      match kinds[a]?, kinds[b]? with
      | some (.dense s), some (.dense _) => pure (if charged then cost + shapeSize s else cost, kinds.push (.dense s))
      | _, _ => none
    | _ => none
  match kinds[g.output]? with
  | some (.dense s) => some (cost + (s.getLast?.getD 0 - 1))
  | _ => none

/-! ## The interval rule's charges -/

/-- What the Python interval run knows about a value: the one-hot input, its sum, or a box (centre
    and radius) of this shape. Every value after the input is a box, as in Python's `run_interval`
    on a linear network. -/
inductive IKind where
  | oneHot
  | summed
  | box (shape : List Nat)

/-- The charge of a linear map on the one-hot input over the box, per position (`_onehot_box`). -/
def oneHotBoxCost (box : Box) (out : Nat) : Nat :=
  (box.map fun r => if r.lo == r.hi then out else 2 * out * (r.hi - r.lo + 1)).sum

/-- The `interval` charge of one leaf, as `run_interval` charges it, with the margins at the output:
    `none` if the rule cannot follow the network (the leaf is then rejected by `checkProof` too). -/
def intervalCost (g : Graph) (w : Weights Rat) (box : Box) (l : Nat) (approx : Option (Approx × RawForm)) :
    Option Nat := do
  let keep := reachable g
  let step := fun (acc : Option (Nat × Array IKind × Option Nat)) (op : Op) => do
    let (cost, kinds, done) ← acc
    if done.isSome then pure (cost, kinds.push .oneHot, done) else
    let i := kinds.size
    let charged := keep.contains i
    let add (c : Nat) := if charged then cost + c else cost
    match op with
    | .input => pure (cost, kinds.push .oneHot, none)
    | .sum a d =>
      match kinds[a]? with
      | some .oneHot => if normDim d 3 == some 1 then pure (cost, kinds.push .summed, none) else none
      | some .summed => none
      | some (.box s) =>
        let dim ← normDim d s.length
        let n := s.getD dim 0
        let s' := s.eraseIdx dim
        pure (add (2 * shapeSize s' * (n - 1)), kinds.push (.box s'), none)
      | none => none
    | .linear a wn bn =>
      let W ← List.lookup wn w
      let nOut := W.shape.getD 0 0
      let inn := W.shape.getD 1 0
      let arg ← kinds[a]?
      if i == g.output then
        -- the margins at the output (`_final_margins`), then the decision
        let c ← match arg with
          | .summed =>
            match approx with
            | none => some ((box.map fun r => if r.hi > r.lo then 2 * nOut * (r.hi - r.lo + 1) else nOut).sum)
            | some (_, raw) =>
              some ((box.map fun r =>
                if r.lo == r.hi then nOut else approxRangeCost nOut l r.lo r.hi raw + nOut).sum)
          | .oneHot => none
          | .box s => if s == [1, inn] then some (3 * nOut * inn) else none
        let c := if bn.isSome then c + nOut else c
        pure (cost + c + (nOut - 1), kinds.push (.box [1, nOut]), some (nOut - 1))
      else
        let (c, s') ← match arg with
          | .oneHot => some (oneHotBoxCost box nOut, [1, g.positions, nOut])
          | .summed => some (oneHotBoxCost box nOut, [1, nOut])
          | .box s => some (2 * (shapeSize s / inn) * inn * nOut, s.dropLast ++ [nOut])
        let c := if bn.isSome then c + shapeSize s' else c
        pure (add c, kinds.push (.box s'), none)
    | .add a b =>
      match kinds[a]?, kinds[b]? with
      | some (.box s), some (.box _) => pure (add (2 * shapeSize s), kinds.push (.box s), none)
      | _, _ => none
    | _ => none
  let (cost, kinds, done) ← g.nodes.foldl step (some (0, #[], none))
  match done with
  | some _ => some cost
  | none =>
    -- the output is not a linear map: `_margins_from_value` on a box, then the decision
    match kinds[g.output]? with
    | some (.box s) =>
      let n := s.getLast?.getD 0
      some (cost + 2 * n + (n - 1))
    | _ => none

/-! ## The whole proof -/

/-- The bill of a proof file, by category, as the Python checker would charge it; an error where the
    Python checker would reject the proof (`checkProof` rejects it too). The plan (tree, rules, chains,
    symmetry flag, names) is not charged. -/
def proofCost (g : Graph) (w : Weights Rat) (task : Task) (proof : ProofFile) :
    Except String Cost := do
  let c : Cost := [("extract", paramCount w)]
  -- contractions, applied one by one as `contractAll` applies them, so that later chains see the
  -- contracted graph; each chain is billed on the graph it meets
  let (g', w', _, _, contractC) ← proof.contractions.foldlM (init := (g, w, ([] : List Nat), 0, 0))
    fun (g, w, removed, step, acc) chain => do
      let some cc := contractCost g w chain | throw "contract: the chain's shapes could not be read"
      match contractOne g w removed step chain with
      | .ok (g', w', removed') => pure (g', w', removed', step + 1, acc + cc)
      | .error e => throw s!"contract: {e}"
  let c := c.add "contract" contractC
  -- approximations
  let approxs ← match buildApproxs g' w' proof.approximations with
    | .ok as => pure as
    | .error e => throw s!"approximate: {e}"
  let raws := proof.approximations.map (·.form)
  let readC := (raws.map approxReadCost).sum
  let c := c.add "read" readC
  let approxC := (List.zip approxs raws).foldl (fun acc (a, raw) => acc + approxBuildCost a.W raw) 0
  let c := c.add "approximate" approxC
  -- the tree: walked for free
  let leaves ← match walk proof.tree (rootBox task.space) with
    | .ok ls => pure ls
    | .error e => throw s!"tree: {e}"
  let withRaw (name : String) : Option (Approx × RawForm) :=
    (List.zip approxs raws).find? (·.1.name == name)
  -- every leaf's rule is charged; which leaves are accepted, and what they certify (under symmetry
  -- too), is counted for free
  leaves.foldlM (init := c) fun c leaf => do
    match leaf.rule with
    | .skip => pure c
    | .single =>
      let some _ := boxInput leaf.box | throw "single: the leaf holds more than one input"
      let some singleC := singleCost g' w' | throw "single: the forward pass could not be billed"
      pure (c.add "single" singleC)
    | .interval name =>
      match task.constantLabel leaf.box with
      | none => pure c
      | some l =>
        let a ← match name with
          | none => pure none
          | some n =>
            match withRaw n with
            | some ar => pure (some ar)
            | none => throw s!"interval: unknown approximation {n}"
        let some ic := intervalCost g' w' leaf.box l a
          | throw s!"interval: the leaf {repr leaf.box} could not be billed"
        pure (c.add "interval" ic)
    | .tokenInterval =>
      -- as Python: no charge when the label is not constant; otherwise `checkProof` has already
      -- rejected the proof, since the rule is for networks beyond linear maps
      match task.constantLabel leaf.box with
      | none => pure c
      | some _ => throw "token_interval: the rule is for networks beyond linear maps"

/-- The checker with its bill: `checkProof`'s count, and the proof's length under `cost-v4`. -/
def checkProofCounted (g : Graph) (w : Weights Rat) (task : Task) (proof : ProofFile) :
    Except String (Nat × Cost) :=
  match checkProof g w task proof with
  | .error e => .error e
  | .ok n =>
    match proofCost g w task proof with
    | .ok c => .ok (n, c)
    | .error e => .error s!"the bill could not be computed: {e}"

end CompactCheck
