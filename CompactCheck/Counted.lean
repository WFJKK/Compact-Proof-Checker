import CompactCheck.Network
import CompactCheck.Exp

/-!
# The counted language: a monad whose every operation on a number is charged

A scored open-lane proof's checker `D : CostM Nat` is written here. `CostM` holds the weights and
the certificate, and a bill; the only way for `D` to make or use a number of the network is one of the
primitives below, each with a fixed charge from `cost-v3`. Loops, conditionals and arithmetic on `Nat`
and `Bool` are ordinary Lean and free, as the Python checker's bookkeeping is. The acceptance service
checks that `D` uses nothing else (`docs/COUNTED.md`): in `D`, `Q` and `CostM` are sealed; in theorems
about `D`, `Q.val` and `CostM.run` are plain projections.

Nothing here is trusted for soundness: a proof about a checker written in `CostM` is a theorem about
these definitions. What the service trusts is the charge of each primitive, as the number cost-v3 gives
the operation.

This file uses only core Lean.
-/

namespace CompactCheck

/-- A number of the network, sealed inside `D`. -/
structure Q where
  val : Rat
deriving Repr

/-- A certificate: the numbers a proof hands the checker, read once (charged `read`, 1 each). -/
abbrev Cert := Array Rat

/-- What a checker runs against. -/
structure Env where
  weights : Weights Rat
  cert : Cert

/-- The bill: operations by category, as `core/check/cost.py` keeps them. -/
abbrev Cost := List (String × Nat)

namespace Cost

def add (c : Cost) (cat : String) (n : Nat) : Cost :=
  match c with
  | [] => [(cat, n)]
  | (k, m) :: rest => if k == cat then (k, m + n) :: rest else (k, m) :: add rest cat n

def total (c : Cost) : Nat := (c.map (·.2)).sum

def get (c : Cost) (cat : String) : Nat :=
  match c.find? (·.1 == cat) with
  | some (_, n) => n
  | none => 0

end Cost

/-! ## Reading an array in the kernel

In compiled code an `Array` is an array, but the kernel knows `Array` only as a structure around a `List`:
to reduce `a[i]!` it walks `i` cells, and the next read walks again from the start. A checker that reads
every entry of a tensor of `n` entries thus costs the kernel about `n^2 / 2` steps, and, since the kernel
keeps what it computed until the theorem is done, as much memory. `CostM.weight` and `CostM.cert` therefore
read through a `ReadTree` of the array's entries: every read of one array in a theorem asks for the same
tree, which the kernel builds once (one pass over the entries) and keeps, and a read then descends about
`log₂ n` levels. The value read is the array's entry (`ReadTree.get_ofList`, `CostM.weight_run_eq`,
`CostM.cert_run_eq`); only the kernel's work differs. -/

/-- A binary tree with the entries of a list at its leaves, left to right. -/
inductive ReadTree (α : Type) where
  | empty : ReadTree α
  | leaf : α → ReadTree α
  | node : ReadTree α → ReadTree α → ReadTree α

namespace ReadTree

/-- The first `k` elements of `xs` as a balanced tree (the left subtree holds `k / 2` of them), and the
    rest of `xs`, in one pass. `d` bounds the depth; `k ≤ d` is enough (`build_spec`). -/
def build {α : Type} : Nat → Nat → List α → ReadTree α × List α
  | 0, _, xs => (.empty, xs)
  | _ + 1, 0, xs => (.empty, xs)
  | _ + 1, 1, [] => (.empty, [])
  | _ + 1, 1, x :: rest => (.leaf x, rest)
  | d + 1, k + 2, xs =>
    let l := build d (k / 2 + 1) xs
    let r := build d (k - k / 2 + 1) l.2
    (.node l.1 r.1, r.2)

/-- Entry `i` of a tree of `k` entries made by `build`: in the left subtree when `i < k / 2`. -/
def get {α : Type} : ReadTree α → Nat → Nat → Option α
  | .empty, _, _ => none
  | .leaf x, _, i => if i = 0 then some x else none
  | .node l r, k, i => if i < k / 2 then l.get (k / 2) i else r.get (k - k / 2) (i - k / 2)

/-- The tree of all of `xs`. -/
def ofList {α : Type} (xs : List α) : ReadTree α := (build xs.length xs.length xs).1

theorem build_spec {α : Type} : ∀ (d k : Nat) (xs : List α), k ≤ d → k ≤ xs.length →
    (build d k xs).2 = xs.drop k ∧ ∀ i, (build d k xs).1.get k i = (xs.take k)[i]?
  | 0, k, xs, hk, _ => by
    obtain rfl : k = 0 := by omega
    simp [build, get]
  | _ + 1, 0, xs, _, _ => by simp [build, get]
  | _ + 1, 1, [], _, h => by simp at h
  | _ + 1, 1, x :: rest, _, _ => by
    refine ⟨by simp [build], fun i => ?_⟩
    cases i <;> simp [build, get]
  | d + 1, k + 2, xs, hk, hl => by
    have h1 := build_spec d (k / 2 + 1) xs (by omega) (by omega)
    have h2 := build_spec d (k - k / 2 + 1) (build d (k / 2 + 1) xs).2 (by omega)
      (by rw [h1.1, List.length_drop]; omega)
    have e1 : (k + 2) / 2 = k / 2 + 1 := by omega
    have e2 : k + 2 - (k / 2 + 1) = k - k / 2 + 1 := by omega
    refine ⟨?_, fun i => ?_⟩
    · simp only [build]
      rw [h2.1, h1.1, List.drop_drop]
      congr 1
      omega
    · simp only [build, get, e1, e2]
      split
      · rw [h1.2 i, List.getElem?_take, List.getElem?_take, ite_eq_left (by omega), ite_eq_left (by omega)]
      · rw [h2.2 (i - (k / 2 + 1)), h1.1, List.getElem?_take, List.getElem?_drop, List.getElem?_take]
        by_cases hi : i < k + 2
        · rw [ite_eq_left (by omega), ite_eq_left hi]
          congr 1
          omega
        · rw [ite_eq_right (by omega), ite_eq_right hi]

theorem get_ofList {α : Type} (xs : List α) (i : Nat) : (ofList xs).get xs.length i = xs[i]? := by
  have h := (build_spec xs.length xs.length xs (Nat.le_refl _) (Nat.le_refl _)).2 i
  rwa [List.take_length] at h

end ReadTree

/-- A counted computation: from the environment and the bill so far to a result and the new bill, or
    `none` when a primitive is misused (a weight that does not exist, say). A structure, not a function
    type, so that a checker cannot be written as a bare function of the environment: inside `D`, neither
    `CostM.mk` nor `CostM.run` is available. -/
structure CostM (α : Type) where
  run : Env → Cost → Option (α × Cost)

namespace CostM

protected def pure (a : α) : CostM α := ⟨fun _ c => some (a, c)⟩

protected def bind (x : CostM α) (f : α → CostM β) : CostM β := ⟨fun env c =>
  match x.run env c with
  | some (a, c') => (f a).run env c'
  | none => none⟩

instance : Monad CostM where
  pure := CostM.pure
  bind := CostM.bind

/-- Run a checker from an empty bill: the result and the bill, if every primitive was used properly. -/
def exec (x : CostM α) (env : Env) : Option (α × Cost) := x.run env []

/-- The result and the bill's total: what a scored submission's instance theorem states,
    `CostM.billed D ⟨weights, cert⟩ = some (n, L)`. -/
def billed (x : CostM α) (env : Env) : Option (α × Nat) :=
  (x.exec env).map fun p => (p.1, p.2.total)

/-- Fail: the checker certifies nothing. -/
def fail : CostM α := ⟨fun _ _ => none⟩

/-- Two counted computations are equal when they run alike on every environment and bill. -/
protected theorem ext {x y : CostM α} (h : ∀ env c, x.run env c = y.run env c) : x = y := by
  cases x
  cases y
  congr
  funext env c
  exact h env c

/-! ## Primitives, with their charges -/

/-- Add to the bill. A program can only make itself longer. -/
def charge (cat : String) (n : Nat) : CostM Unit := ⟨fun _ c => some ((), c.add cat n)⟩

/-- What compiled code runs for `weight` (`#eval`, the scoring preview): the array's own `a[i]?`, constant
    time outside the kernel, where nothing is shared between calls and a tree would be rebuilt at every read.
    The kernel never runs this: it checks `weight` itself. The two are the same function (`weightImpl_eq`). -/
def weightImpl (name : String) (i : Nat) : CostM Q := ⟨fun env c =>
  match List.lookup name env.weights with
  | some t => match t.data[i]? with
    | some x => some (⟨x⟩, c)
    | none => none
  | none => none⟩

/-- Entry `i` of the weight `name`, in row-major order. Free: the weights are charged once per proof
    (`extract`, E). Read through a `ReadTree`, so that the kernel takes about `log₂ n` steps, not `i`
    (see "Reading an array in the kernel"); the value is `t.data[i]` (`weight_run_eq`). -/
@[implemented_by weightImpl]
def weight (name : String) (i : Nat) : CostM Q := ⟨fun env c =>
  match List.lookup name env.weights with
  | some t => match (ReadTree.ofList t.data.toList).get t.data.size i with
    | some x => some (⟨x⟩, c)
    | none => none
  | none => none⟩

/-- What a read of a weight returns: entry `i` of the tensor, when there is one, and the bill unchanged. -/
theorem weight_run_eq (name : String) (i : Nat) (env : Env) (c : Cost) :
    (weight name i).run env c =
      ((List.lookup name env.weights).bind fun t => t.data[i]?).map fun x => (⟨x⟩, c) := by
  simp only [weight]
  split
  · rename_i t ht
    have h := ReadTree.get_ofList t.data.toList i
    rw [Array.length_toList, Array.getElem?_toList] at h
    rw [h, ht, Option.bind_some]
    cases t.data[i]? <;> rfl
  · rename_i ht
    rw [ht]
    rfl

/-- Compiled code and the kernel compute the same reads. -/
theorem weightImpl_eq : weightImpl = weight := by
  funext name i
  apply CostM.ext
  intro env c
  rw [weight_run_eq]
  simp only [weightImpl]
  cases List.lookup name env.weights with
  | none => rfl
  | some t =>
    simp only [Option.bind_some]
    cases t.data[i]? <;> rfl

theorem weight_spec {name : String} {i : Nat} {env : Env} {c c' : Cost} {v : Q}
    (h : (weight name i).run env c = some (v, c')) :
    ∃ t, List.lookup name env.weights = some t ∧ ∃ hi : i < t.data.size, v.val = t.data[i] ∧ c' = c := by
  rw [weight_run_eq] at h
  cases ht : List.lookup name env.weights with
  | none => simp [ht] at h
  | some t =>
    refine ⟨t, rfl, ?_⟩
    rw [ht] at h
    by_cases hi : i < t.data.size
    · simp only [Option.bind_some, Array.getElem?_eq_getElem hi, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at h
      exact ⟨hi, by rw [← h.1], h.2.symm⟩
    · simp [Array.getElem?_eq_none (Nat.le_of_not_lt hi)] at h

/-- A read of a weight that exists, with an index in range: entry `i`, the bill unchanged. -/
theorem weight_run_of_lookup {name : String} {i : Nat} {env : Env} {t : Tensor Rat} (c : Cost)
    (ht : List.lookup name env.weights = some t) (hi : i < t.data.size) :
    (weight name i).run env c = some (⟨t.data[i]⟩, c) := by
  rw [weight_run_eq, ht]
  simp [Array.getElem?_eq_getElem hi]

/-- The form most proofs about a checker use: the value read is `t.get i`, and the read is free. -/
theorem weight_run_get {name : String} {i : Nat} {env : Env} {t : Tensor Rat} {c c' : Cost} {v : Q}
    (ht : List.lookup name env.weights = some t) (h : (weight name i).run env c = some (v, c')) :
    v.val = t.get i ∧ c' = c := by
  obtain ⟨t', ht', hi, hv, hc⟩ := weight_spec h
  rw [ht] at ht'
  cases ht'
  refine ⟨?_, hc⟩
  rw [hv, Tensor.get, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]

/-- The definition `weight` had before policy v10, as an equation: a proof written against it (one that
    unfolded `CostM.weight` and split on the `if`) goes through after `rw [CostM.weight_run_eq_ite]`. -/
theorem weight_run_eq_ite (name : String) (i : Nat) (env : Env) (c : Cost) :
    (weight name i).run env c =
      match List.lookup name env.weights with
      | some t => if i < t.data.size then some (⟨t.data[i]!⟩, c) else none
      | none => none := by
  rw [weight_run_eq]
  cases ht : List.lookup name env.weights with
  | none => rfl
  | some t =>
    by_cases hi : i < t.data.size
    · simp [hi]
    · simp [hi]

/-- The shape of a weight, for loops. Free. -/
def weightShape (name : String) : CostM (List Nat) := ⟨fun env c =>
  match List.lookup name env.weights with
  | some t => some (t.shape, c)
  | none => none⟩

/-- The number of entries of the weight `name` (its data length, which may differ from the product of its
    shape in an ill-formed network file). Free, like `weightShape`: structural metadata, not a number of
    the network. Before version 4.1 (cost-v4) a checker could bound a tensor's length from above only by
    running a whole forward pass (`single`), which every proof paid once. -/
def weightSize (name : String) : CostM Nat := ⟨fun env c =>
  match List.lookup name env.weights with
  | some t => some (t.data.size, c)
  | none => none⟩

theorem weightSize_spec {name : String} {env : Env} {c c' : Cost} {n : Nat}
    (h : (weightSize name).run env c = some (n, c')) :
    ∃ t, List.lookup name env.weights = some t ∧ t.data.size = n ∧ c' = c := by
  simp only [weightSize] at h
  split at h
  · rename_i t ht
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨t, ht, h.1, h.2.symm⟩
  · cases h

/-- What compiled code runs for `cert`, as `weightImpl` is for `weight` (`certImpl_eq`). -/
def certImpl (i : Nat) : CostM Q := ⟨fun env c =>
  match env.cert[i]? with
  | some x => some (⟨x⟩, c)
  | none => none⟩

/-- Number `i` of the certificate. Free: the certificate is charged once per proof (`read`). Read through
    a `ReadTree`, as `weight` is; the value is `env.cert[i]` (`cert_run_eq`). -/
@[implemented_by certImpl]
def cert (i : Nat) : CostM Q := ⟨fun env c =>
  match (ReadTree.ofList env.cert.toList).get env.cert.size i with
  | some x => some (⟨x⟩, c)
  | none => none⟩

/-- What a read of the certificate returns: number `i`, when there is one, and the bill unchanged. -/
theorem cert_run_eq (i : Nat) (env : Env) (c : Cost) :
    (cert i).run env c = env.cert[i]?.map fun x => (⟨x⟩, c) := by
  simp only [cert]
  have h := ReadTree.get_ofList env.cert.toList i
  rw [Array.length_toList, Array.getElem?_toList] at h
  rw [h]
  cases env.cert[i]? <;> rfl

/-- Compiled code and the kernel compute the same reads. -/
theorem certImpl_eq : certImpl = cert := by
  funext i
  apply CostM.ext
  intro env c
  rw [cert_run_eq]
  simp only [certImpl]
  cases env.cert[i]? <;> rfl

theorem cert_spec {i : Nat} {env : Env} {c c' : Cost} {v : Q} (h : (cert i).run env c = some (v, c')) :
    ∃ hi : i < env.cert.size, v.val = env.cert[i] ∧ c' = c := by
  rw [cert_run_eq] at h
  by_cases hi : i < env.cert.size
  · simp only [Array.getElem?_eq_getElem hi, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨hi, by rw [← h.1], h.2.symm⟩
  · simp [Array.getElem?_eq_none (Nat.le_of_not_lt hi)] at h

/-- A read of the certificate with an index in range: number `i`, the bill unchanged. -/
theorem cert_run_of_lt {i : Nat} {env : Env} (c : Cost) (hi : i < env.cert.size) :
    (cert i).run env c = some (⟨env.cert[i]⟩, c) := by
  rw [cert_run_eq]
  simp [Array.getElem?_eq_getElem hi]

/-- The form most proofs about a checker use: the value read is `env.cert[i]!`, and the read is free. -/
theorem cert_run_get {i : Nat} {env : Env} {c c' : Cost} {v : Q} (h : (cert i).run env c = some (v, c')) :
    v.val = env.cert[i]! ∧ c' = c := by
  obtain ⟨hi, hv, hc⟩ := cert_spec h
  refine ⟨?_, hc⟩
  rw [hv, getElem!_pos env.cert i hi]

/-- The definition `cert` had before policy v10, as an equation (see `weight_run_eq_ite`). -/
theorem cert_run_eq_ite (i : Nat) (env : Env) (c : Cost) :
    (cert i).run env c = if i < env.cert.size then some (⟨env.cert[i]!⟩, c) else none := by
  rw [cert_run_eq]
  by_cases hi : i < env.cert.size
  · simp [hi]
  · simp [hi]

/-- How many numbers the certificate holds. Free. -/
def certSize : CostM Nat := ⟨fun env c => some (env.cert.size, c)⟩

/-- A numeral, as a number read from the proof file: 1. -/
def lit (cat : String) (n : Nat) : CostM Q := ⟨fun _ c => some (⟨(n : Rat)⟩, c.add cat 1)⟩

/-- Zero, free: the Python checker starts its sums at 0 without charge. -/
def zero : CostM Q := ⟨fun _ c => some (⟨0⟩, c)⟩

def qadd (cat : String) (a b : Q) : CostM Q := ⟨fun _ c => some (⟨a.val + b.val⟩, c.add cat 1)⟩
def qsub (cat : String) (a b : Q) : CostM Q := ⟨fun _ c => some (⟨a.val - b.val⟩, c.add cat 1)⟩
/-- A multiply-add, `acc + a * b`: 1. -/
def qmuladd (cat : String) (acc a b : Q) : CostM Q :=
  ⟨fun _ c => some (⟨acc.val + a.val * b.val⟩, c.add cat 1)⟩
def qneg (cat : String) (a : Q) : CostM Q := ⟨fun _ c => some (⟨-a.val⟩, c.add cat 1)⟩
def qmin (cat : String) (a b : Q) : CostM Q := ⟨fun _ c => some (⟨min a.val b.val⟩, c.add cat 1)⟩
def qmax (cat : String) (a b : Q) : CostM Q := ⟨fun _ c => some (⟨max a.val b.val⟩, c.add cat 1)⟩
def qlt (cat : String) (a b : Q) : CostM Bool := ⟨fun _ c => some (decide (a.val < b.val), c.add cat 1)⟩
def qle (cat : String) (a b : Q) : CostM Bool := ⟨fun _ c => some (decide (a.val ≤ b.val), c.add cat 1)⟩
def qeq (cat : String) (a b : Q) : CostM Bool := ⟨fun _ c => some (decide (a.val = b.val), c.add cat 1)⟩

/-- Bounds on `exp a` (`Exp.lean`, as the Python checker computes them), charged 3 as a softmax entry
    of `cost-v3`'s general networks; `none` if the argument is out of the bounds' range. -/
def qexp (cat : String) (a : Q) : CostM (Q × Q) := ⟨fun _ c =>
  match expInterval a.val with
  | some (lo, hi) => some ((⟨lo⟩, ⟨hi⟩), c.add cat 3)
  | none => none⟩

end CostM

end CompactCheck
