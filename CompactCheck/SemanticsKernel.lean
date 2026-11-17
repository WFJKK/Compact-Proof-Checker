import CompactCheck.Semantics
import CompactCheck.Counted

/-!
# The semantics, written for the kernel

`Semantics.lean` says what every operation computes, and it is the specification: nothing here changes it.
This file gives each operation a second definition that computes the same tensor and that the kernel
evaluates in reasonable time and memory, with a proof that the two are equal (`semOps_eqK`, `semGraph_eqK`,
and one `_eqK` for each operation). A proof that needs the kernel to run a graph (`decide +kernel` on
`semOps g w x ops vals`, with numbers or with symbols for the weights) states the fact about `semOpsK` and
rewrites with `semOps_eqK`:

    theorem run : (semOps g w x ops vals).map f = some r := by
      rw [semOps_eqK]; decide +kernel

Why the kernel needs another definition. Compiled code has arrays; the kernel knows `Array` only as a
structure around a `List`, and evaluates by unfolding definitions.

- Building: `(Array.range n).map f` (in `Tensor.ofFn`), `Array.ofFn` and `Array.map` add one entry at a time
  to the end of the list under the array, so the kernel walks the list for every entry: `n^2 / 2` steps, each
  kept in memory until the theorem is done. An array of 512 entries costs about a second and a gigabyte.
  Here every tensor is built as a list (`List.range`, `List.map`) and turned into an array at the end, which
  for the kernel is no step at all (`Tensor.ofFnK`, `rangeMapK`, `Tensor.mapK`).
- Reading: `t.data.getD i 0` walks `i` cells for every read. Here a read goes through a balanced tree of the
  tensor's entries (`ReadTree`, `Counted.lean`), built once for a tensor and theorem: about `log₂ n` steps
  (`Tensor.getK`, `Tensor.entryK`).

The copies are made from the text of `Eval.lean` and `Semantics.lean` by replacing those leaves and nothing
else, so each proof is the leaves' equations and `rfl`. They are for the kernel only: compiled code should
run the specification's own definitions, which use real arrays.

A tensor a proof writes itself (symbolic weights, an expected result) is built by the kernel too: write its
data as `((List.range n).map f).toArray`, not as `Array.ofFn f`.
-/

set_option linter.unusedSectionVars false

namespace CompactCheck

/-- `(Array.range n).map g`, built from a list. -/
def rangeMapK {β : Type} (n : Nat) (g : Nat → β) : Array β :=
  ((List.range n).map g).toArray

theorem rangeMap_eqK {β : Type} (n : Nat) (g : Nat → β) : (Array.range n).map g = rangeMapK n g := by
  apply Array.ext'
  simp [rangeMapK]

namespace Tensor

variable {α β : Type}

/-- `Tensor.get`, read through a tree: entry `i` in row-major order, or 0 out of range. -/
def getK [Zero α] (t : Tensor α) (i : Nat) : α :=
  match (ReadTree.ofList t.data.toList).get t.data.size i with
  | some v => v
  | none => 0

theorem get_eqK [Zero α] (t : Tensor α) (i : Nat) : t.get i = t.getK i := by
  have h := ReadTree.get_ofList t.data.toList i
  rw [Array.length_toList] at h
  simp only [get, getK, h, Array.getElem?_toList]
  cases hh : t.data[i]? <;> simp [Array.getD_eq_getD_getElem?, hh]

/-- `Tensor.entry`, read through a tree. -/
def entryK [Zero α] (t : Tensor α) (i : List Nat) : α :=
  t.getK (ravel t.shape i)

theorem entry_eqK [Zero α] (t : Tensor α) (i : List Nat) : t.entry i = t.entryK i := by
  simp only [entry, entryK, get_eqK]

/-- `Tensor.ofFn`, built from a list. -/
def ofFnK (shape : List Nat) (f : List Nat → α) : Tensor α :=
  ⟨shape, rangeMapK (shapeSize shape) fun j => f (unravel shape j)⟩

theorem ofFn_eqK (shape : List Nat) (f : List Nat → α) : ofFn shape f = ofFnK shape f := by
  simp only [ofFn, ofFnK, rangeMap_eqK]

/-- `Tensor.map`, built from a list. -/
def mapK (f : α → β) (t : Tensor α) : Tensor β :=
  ⟨t.shape, (t.data.toList.map f).toArray⟩

theorem map_eqK (f : α → β) (t : Tensor α) : map f t = mapK f t := by
  simp only [map, mapK]
  congr 1
  apply Array.ext'
  simp

end Tensor

theorem replicate_eqK {β : Type} (n : Nat) (v : β) : Array.replicate n v = (List.replicate n v).toArray := by
  apply Array.ext'
  simp

section eval

variable {α : Type} [Zero α] [One α] [Add α] [Mul α]

/-- `oneHotInput`, as the kernel computes it best (`oneHotInput_eqK`). -/
def oneHotInputK (positions values : Nat) (x : Input) : Option (Tensor α) :=
  if x.length == positions && x.all (· < values) then
    some ⟨[1, positions, values], rangeMapK (positions * values) fun j =>
      if x.getD (j / values) 0 = j % values then 1 else 0⟩
  else none

theorem oneHotInput_eqK (positions values : Nat) (x : Input) :
    (oneHotInput positions values x : Option (Tensor α)) = oneHotInputK positions values x := by
  simp only [oneHotInput, oneHotInputK, rangeMap_eqK]
  all_goals rfl

/-- `linearOp`, as the kernel computes it best (`linearOp_eqK`). -/
def linearOpK (W : Tensor α) (b : Option (Tensor α)) (t : Tensor α) : Option (Tensor α) :=
  let out := W.shape.getD 0 0
  let inn := W.shape.getD 1 0
  let pre := shapeSize t.shape.dropLast
  let biasOk := match b with
    | some b => b.shape == [out] && b.data.size == out
    | none => true
  if W.shape == [out, inn] && t.shape.getLast? == some inn && W.data.size == out * inn &&
      t.data.size == pre * inn && biasOk then
    some ⟨t.shape.dropLast ++ [out], rangeMapK (pre * out) fun j =>
      let p := j / out
      let o := j % out
      ((List.range inn).map fun i => W.getK (o * inn + i) * t.getK (p * inn + i)).sum +
        (match b with
         | some b => b.getK o
         | none => 0)⟩
  else none

theorem linearOp_eqK (W : Tensor α) (b : Option (Tensor α)) (t : Tensor α) : linearOp W b t = linearOpK W b t := by
  simp only [linearOp, linearOpK, rangeMap_eqK, Tensor.get_eqK]
  all_goals rfl

/-- `sumOp`, as the kernel computes it best (`sumOp_eqK`). -/
def sumOpK (dim : Int) (t : Tensor α) : Option (Tensor α) :=
  match normDim dim t.shape.length with
  | none => none
  | some d =>
    let outer := shapeSize (t.shape.take d)
    let n := t.shape.getD d 0
    let inner := shapeSize (t.shape.drop (d + 1))
    if t.data.size == outer * n * inner then
      some ⟨t.shape.eraseIdx d, rangeMapK (outer * inner) fun j =>
        let o := j / inner
        let i := j % inner
        ((List.range n).map fun k => t.getK ((o * n + k) * inner + i)).sum⟩
    else none

theorem sumOp_eqK (dim : Int) (t : Tensor α) : sumOp dim t = sumOpK dim t := by
  simp only [sumOp, sumOpK, rangeMap_eqK, Tensor.get_eqK]
  all_goals rfl

/-- `addOp`, as the kernel computes it best (`addOp_eqK`). -/
def addOpK (a b : Tensor α) : Option (Tensor α) :=
  if a.shape == b.shape && a.data.size == b.data.size then
    some ⟨a.shape, rangeMapK a.data.size fun j => a.getK j + b.getK j⟩
  else none

theorem addOp_eqK (a b : Tensor α) : addOp a b = addOpK a b := by
  simp only [addOp, addOpK, rangeMap_eqK, Tensor.get_eqK]
  all_goals rfl

/-- `evalOp`, as the kernel computes it best (`evalOp_eqK`). -/
def evalOpK (g : Graph) (w : Weights α) (x : Input) (vals : Array (Tensor α)) :
    Op → Option (Tensor α)
  | .input => oneHotInputK g.positions g.values x
  | .linear a wn bn =>
    match vals[a]?, List.lookup wn w with
    | some t, some W =>
      match bn with
      | none => linearOpK W none t
      | some bn =>
        match List.lookup bn w with
        | some b => linearOpK W (some b) t
        | none => none
    | _, _ => none
  | .sum a d =>
    match vals[a]? with
    | some t => sumOpK d t
    | none => none
  | .add a b =>
    match vals[a]?, vals[b]? with
    | some ta, some tb => addOpK ta tb
    | _, _ => none
  | _ => none

theorem evalOp_eqK (g : Graph) (w : Weights α) (x : Input) (vals : Array (Tensor α)) (op : Op) :
    evalOp g w x vals op = evalOpK g w x vals op := by
  cases op <;> simp only [evalOp, evalOpK, oneHotInput_eqK, linearOp_eqK, sumOp_eqK, addOp_eqK]
  all_goals rfl

end eval

section ops

variable {α : Type} [Zero α] [One α] [Add α] [Mul α] [Neg α] [ExpDiv α]

/-- `broadcastOp`, as the kernel computes it best (`broadcastOp_eqK`). -/
def broadcastOpK (f : α → α → α) (a b : Tensor α) : Option (Tensor α) :=
  if a.wellFormed && b.wellFormed then
    (broadcastShape a.shape b.shape).map fun s =>
      Tensor.ofFnK s fun i =>
        f (a.entryK (broadcastIndex a.shape i)) (b.entryK (broadcastIndex b.shape i))
  else none

theorem broadcastOp_eqK (f : α → α → α) (a b : Tensor α) : broadcastOp f a b = broadcastOpK f a b := by
  simp only [broadcastOp, broadcastOpK, Tensor.ofFn_eqK, Tensor.entry_eqK]
  all_goals rfl

/-- `matmulOp`, as the kernel computes it best (`matmulOp_eqK`). -/
def matmulOpK (a b : Tensor α) : Option (Tensor α) :=
  if !a.wellFormed || !b.wellFormed then none else
  (matmulShape a.shape b.shape).map fun p =>
    let a' : Tensor α := ⟨p.sa, a.data⟩
    let b' : Tensor α := ⟨p.sb, b.data⟩
    ⟨p.out, (Tensor.ofFnK (p.batch ++ [p.m, p.n]) fun i =>
      let bi := i.take p.batch.length
      ((List.range p.k).map fun t =>
        a'.entryK (broadcastIndex p.ba bi ++ [i.getD p.batch.length 0, t]) *
        b'.entryK (broadcastIndex p.bb bi ++ [t, i.getD (p.batch.length + 1) 0])).sum).data⟩

theorem matmulOp_eqK (a b : Tensor α) : matmulOp a b = matmulOpK a b := by
  simp only [matmulOp, matmulOpK, Tensor.ofFn_eqK, Tensor.entry_eqK]
  all_goals rfl

/-- `indexOp`, as the kernel computes it best (`indexOp_eqK`). -/
def indexOpK (t : Tensor α) (items : List IndexItem) : Option (Tensor α) :=
  if items.length ≤ t.shape.length && t.wellFormed &&
      (List.zipWith IndexItem.fits (t.shape.take items.length) items).all id then
    some (Tensor.ofFnK ((List.zipWith IndexItem.dims (t.shape.take items.length) items).flatten ++
      t.shape.drop items.length) fun i => t.entryK (sourceIndex items i))
  else none

theorem indexOp_eqK (t : Tensor α) (items : List IndexItem) : indexOp t items = indexOpK t items := by
  simp only [indexOp, indexOpK, Tensor.ofFn_eqK, Tensor.entry_eqK]
  all_goals rfl

/-- `transposeOp`, as the kernel computes it best (`transposeOp_eqK`). -/
def transposeOpK (t : Tensor α) : Option (Tensor α) :=
  match t.shape with
  | [m, n] =>
    if t.wellFormed then some (Tensor.ofFnK [n, m] fun i => t.entryK [i.getD 1 0, i.getD 0 0]) else none
  | [] => some t
  | [_] => some t
  | _ => none

theorem transposeOp_eqK (t : Tensor α) : transposeOp t = transposeOpK t := by
  simp only [transposeOp, transposeOpK, Tensor.ofFn_eqK, Tensor.entry_eqK]
  all_goals rfl

/-- `expandOp`, as the kernel computes it best (`expandOp_eqK`). -/
def expandOpK (t : Tensor α) (shape : List Int) : Option (Tensor α) :=
  if shape.length < t.shape.length || !t.wellFormed then none else
  match expandShape t.shape shape with
  | none => none
  | some full =>
    if (List.zipWith (fun d f => d == f || d == 1) t.shape
        (full.drop (shape.length - t.shape.length))).all id then
      some (Tensor.ofFnK full fun i => t.entryK (broadcastIndex t.shape i))
    else none

theorem expandOp_eqK (t : Tensor α) (shape : List Int) : expandOp t shape = expandOpK t shape := by
  simp only [expandOp, expandOpK, Tensor.ofFn_eqK, Tensor.entry_eqK]
  all_goals rfl

/-- `catOp`, as the kernel computes it best (`catOp_eqK`). -/
def catOpK (ts : List (Tensor α)) (dim : Int) : Option (Tensor α) :=
  if ts.all (·.wellFormed) then
    match catShape (ts.map (·.shape)) dim with
    | none => none
    | some (d, sizes, shape) =>
      some (Tensor.ofFnK shape fun i =>
        let (p, first) := locate sizes (i.getD d 0) 0
        (ts.getD p ⟨[], #[]⟩).entryK (i.set d (i.getD d 0 - first)))
  else none

theorem catOp_eqK (ts : List (Tensor α)) (dim : Int) : catOp ts dim = catOpK ts dim := by
  simp only [catOp, catOpK, Tensor.ofFn_eqK, Tensor.entry_eqK]
  all_goals rfl

/-- `stackOp`, as the kernel computes it best (`stackOp_eqK`). -/
def stackOpK (ts : List (Tensor α)) (dim : Int) : Option (Tensor α) :=
  if ts.all (·.wellFormed) then
    match stackShape (ts.map (·.shape)) dim with
    | none => none
    | some (d, shape) =>
      some (Tensor.ofFnK shape fun i => (ts.getD (i.getD d 0) ⟨[], #[]⟩).entryK (i.eraseIdx d))
  else none

theorem stackOp_eqK (ts : List (Tensor α)) (dim : Int) : stackOp ts dim = stackOpK ts dim := by
  simp only [stackOp, stackOpK, Tensor.ofFn_eqK, Tensor.entry_eqK]
  all_goals rfl

/-- `softmaxOp`, as the kernel computes it best (`softmaxOp_eqK`). -/
def softmaxOpK (t : Tensor α) (dim : Int) : Option (Tensor α) :=
  match normDim dim t.shape.length with
  | none => none
  | some d =>
    if t.wellFormed then
      some (Tensor.ofFnK t.shape fun i =>
        ExpDiv.div (ExpDiv.exp (t.entryK i))
          ((List.range (t.shape.getD d 0)).map fun k => ExpDiv.exp (t.entryK (i.set d k))).sum)
    else none

theorem softmaxOp_eqK (t : Tensor α) (dim : Int) : softmaxOp t dim = softmaxOpK t dim := by
  simp only [softmaxOp, softmaxOpK, Tensor.ofFn_eqK, Tensor.entry_eqK]
  all_goals rfl

/-- `semOp`, as the kernel computes it best (`semOp_eqK`). -/
def semOpK (g : Graph) (w : Weights α) (x : Input) (vals : Array (Tensor α)) :
    Op → Option (Tensor α)
  | .param n => List.lookup n w
  | .binary f a b =>
    match vals[a]?, vals[b]? with
    | some ta, some tb => broadcastOpK f.apply ta tb
    | _, _ => none
  | .neg a => vals[a]?.map (Tensor.mapK Neg.neg)
  | .matmul a b =>
    match vals[a]?, vals[b]? with
    | some ta, some tb => matmulOpK ta tb
    | _, _ => none
  | .index a items => vals[a]?.bind (indexOpK · items)
  | .transpose a => vals[a]?.bind transposeOpK
  | .unsqueeze a d => vals[a]?.bind (unsqueezeOp · d)
  | .expand a shape => vals[a]?.bind (expandOpK · shape)
  | .cat args d => (args.mapM (vals[·]?)).bind (catOpK · d)
  | .stack args d => (args.mapM (vals[·]?)).bind (stackOpK · d)
  | .exp a => vals[a]?.map (Tensor.mapK ExpDiv.exp)
  | .softmax a d => vals[a]?.bind (softmaxOpK · d)
  | .zerosLike a => vals[a]?.map fun t => ⟨t.shape, (List.replicate (shapeSize t.shape) 0).toArray⟩
  | op => evalOpK g w x vals op

theorem semOp_eqK (g : Graph) (w : Weights α) (x : Input) (vals : Array (Tensor α)) (op : Op) :
    semOp g w x vals op = semOpK g w x vals op := by
  have hmap : ∀ f : α → α, Tensor.map f = Tensor.mapK f := fun f => funext (Tensor.map_eqK f)
  have htr : (transposeOp : Tensor α → Option (Tensor α)) = transposeOpK := funext transposeOp_eqK
  cases op <;> simp only [semOp, semOpK, evalOp_eqK, broadcastOp_eqK, matmulOp_eqK, indexOp_eqK, htr,
    expandOp_eqK, catOp_eqK, stackOp_eqK, softmaxOp_eqK, hmap, replicate_eqK]
  all_goals rfl

/-- `semOps`, as the kernel computes it best (`semOps_eqK`). -/
def semOpsK (g : Graph) (w : Weights α) (x : Input) :
    List Op → Array (Tensor α) → Option (Array (Tensor α))
  | [], vals => some vals
  | op :: ops, vals =>
    match semOpK g w x vals op with
    | some v => semOpsK g w x ops (vals.push v)
    | none => none

/-- The specification's run of a list of operations is the kernel's. -/
theorem semOps_eqK (g : Graph) (w : Weights α) (x : Input) :
    ∀ (ops : List Op) (vals : Array (Tensor α)), semOps g w x ops vals = semOpsK g w x ops vals
  | [], vals => by simp only [semOps, semOpsK]
  | op :: ops, vals => by
    simp only [semOps, semOpsK, semOp_eqK]
    cases semOpK g w x vals op with
    | none => rfl
    | some v => exact semOps_eqK g w x ops (vals.push v)

/-- `semGraph`, as the kernel computes it best (`semGraph_eqK`). -/
def semGraphK (g : Graph) (w : Weights α) (x : Input) : Option (Tensor α) :=
  match semOpsK g w x g.nodes #[] with
  | some vals => vals[g.output]?
  | none => none

/-- The specification's output of a network is the kernel's. -/
theorem semGraph_eqK (g : Graph) (w : Weights α) (x : Input) : semGraph g w x = semGraphK g w x := by
  simp only [semGraph, semGraphK, semOps_eqK]
  all_goals rfl

end ops

end CompactCheck
