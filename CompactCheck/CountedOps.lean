import CompactCheck.CountedCheck
import CompactCheck.CountedGeneral
import CompactCheck.TokensCost

/-!
# The counted language, as an interface: a checker is written for every interpreter

A scored checker is a function of an interpreter `I : Interp`: abstract numbers `I.V`, abstract booleans
`I.B`, abstract counts `I.N`, in an abstract monad `I.M`, with every operation on a number or a truth
value charged by the interpreter. There is no branching on a truth value: it can only become a count, a
choice between two numbers, or another truth value through a charged gate. Because the checker has to
make sense for every `I`, and no operation hands a value of `I.V`, `I.B` or `I.N` back to its own Lean
code in a form it can inspect, nothing the checker learns about the network can change what its own code
does next: whatever it learns stays in the interpreter's hands, and the bill the interpreter keeps is the
whole cost of the computation.

Counts are terminal. The operations that make a count are `nzero`, `nsucc`, `nadd`, `nofNat` (concrete
numbers, free), `countB` and `nscale` (a concrete multiple of one truth value, free); no operation takes a
count together with a truth value or a number, and none takes a count and returns anything but a count.
So every count a checker builds is a sum of concrete numbers and concrete multiples of truth values that
charged operations produced, and the size of a count never encodes a computation on the network: a
product of two truth values exists only through a charged gate. This closes the holes of the three earlier
versions: concrete booleans (bits rebuilt into numbers by free arithmetic), branching into the checker's
own code (a reviewer's `I.ifN bit (k 1) (k 0)`), and a free mask `nmask : B → N → N` on an arbitrary count
(a reviewer's decision tree `nadd (nmask b (k 1)) (nmask nb (k 0))`, a conditional on counts for nothing).

`Interp.counting` is the interpreter the service runs: `CostM` of `Counted.lean`, with `Q`, `Bool` and `Nat`.
A submission's soundness theorem and instance theorem are about `D Interp.counting` (docs/COUNTED.md); the
service checks that the checker's own code never mentions `Interp.counting`, `CostM` or `Q`
(`accept/allowlist.txt`), so that the abstraction is real.

The counted operations `CostM.single` and `CostM.interval` run a rule of the proved checker and charge what
`cost-v3` charges for it, through the formulas of `CountedCheck.lean`; `Interp.counting` offers them as
`single` and `interval`. Every operation of the counting interpreter has its specification lemma, so a
soundness proof never looks inside the monad.

This file uses only core Lean.
-/

namespace CompactCheck

namespace CostM

/-- The single rule on one input: `singleOk`, charged as one exact forward pass and the final comparison
    (`singleCost`). `none` if the forward pass cannot be billed on this graph. -/
def single (g : Graph) (task : Task) (x : Input) : CostM Bool := ⟨fun env c =>
  match singleCost g env.weights with
  | some sc => some (singleOk g env.weights task x, c.add "single" sc)
  | none => none⟩

/-- The interval rule on one box, with no approximation: `intervalLeaf`, charged as `intervalCost`.
    `false` (not an error) if the box has no constant label; `none` if the rule cannot follow the
    network. -/
def interval (g : Graph) (task : Task) (box : Box) : CostM Bool := ⟨fun env c =>
  match task.constantLabel box with
  | none => some (false, c)
  | some l =>
    match intervalCost g env.weights box l none, intervalLeaf g env.weights task box none with
    | some ic, .ok b => some (b, c.add "interval" ic)
    | _, _ => none⟩

/-! ## Specifications of the monad and the operations -/

theorem run_pure (a : α) (env : Env) (c : Cost) : (pure a : CostM α).run env c = some (a, c) := rfl

theorem run_bind (x : CostM α) (f : α → CostM β) (env : Env) (c : Cost) :
    (x >>= f).run env c = match x.run env c with
      | some (a, c') => (f a).run env c'
      | none => none := rfl

theorem single_spec {g : Graph} {task : Task} {x : Input} {env : Env} {c c' : Cost}
    (h : (single g task x).run env c = some (true, c')) : singleOk g env.weights task x = true := by
  simp only [single] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact h.1
  · cases h

/-- From the instance theorem of a scored submission, `billed D env = some (n, L)`, the hypothesis of
    its soundness theorem: `D` ran to `n` with some bill. -/
theorem exec_of_billed {x : CostM α} {env : Env} {a : α} {L : Nat}
    (h : billed x env = some (a, L)) : ∃ c, exec x env = some (a, c) := by
  unfold billed at h
  match hx : exec x env with
  | none => rw [hx] at h; cases h
  | some (a', c) =>
    rw [hx] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨c, by rw [h.1]⟩

theorem interval_spec {g : Graph} {task : Task} {box : Box} {env : Env} {c c' : Cost}
    (h : (interval g task box).run env c = some (true, c')) :
    intervalLeaf g env.weights task box none = .ok true := by
  simp only [interval] at h
  split at h
  · simp at h
  · split at h
    · rename_i ic b hm
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [h.1] at hm
      exact hm
    · cases h

end CostM

/-! ## The interface -/

/-- An interpreter of the counted language. A checker is a function of one of these: it can use the
    operations below and ordinary Lean on lists, `Nat` indices and strings, and nothing else about `M`,
    `V`, `B` or `N`. The charges named are those of `Interp.counting`. -/
structure Interp : Type 1 where
  /-- The monad of the computation. -/
  M : Type → Type
  monad : Monad M
  /-- A number of the network or the certificate, or computed from them. -/
  V : Type
  /-- A truth value computed from numbers. -/
  B : Type
  /-- A count of inputs, computed from truth values. -/
  N : Type
  /-- Entry `i` of the weight `name`, in row-major order. Free: the weights are charged once per
      proof (`extract`, E). -/
  weight : String → Nat → M V
  /-- The shape of a weight, for loops. Free. -/
  weightShape : String → M (List Nat)
  /-- The number of entries of a weight (its data length). Free: structural metadata, like the shape. With
      it a checker establishes that a tensor is well formed (length equals the product of the shape) by a
      concrete comparison, instead of paying a forward pass for it. -/
  weightSize : String → M Nat
  /-- Number `i` of the certificate. Free: the certificate is charged once per proof (`read`). -/
  cert : Nat → M V
  /-- How many numbers the certificate holds. Free. -/
  certSize : M Nat
  /-- A numeral, as a number read from the proof file: 1. -/
  lit : String → Nat → M V
  /-- Zero, free: the Python checker starts its sums at 0 without charge. -/
  zero : V
  /-- Arithmetic, 1 each; `muladd acc a b` is `acc + a * b`. -/
  add : String → V → V → M V
  sub : String → V → V → M V
  muladd : String → V → V → V → M V
  neg : String → V → M V
  min : String → V → V → M V
  max : String → V → V → M V
  /-- Comparisons, 1 each: the only source of truth values about numbers. -/
  lt : String → V → V → M B
  le : String → V → V → M B
  eq : String → V → V → M B
  /-- Bounds on `exp a` (`Exp.lean`), charged 3; the monad fails if the argument is out of range. -/
  exp : String → V → M (V × V)
  /-- Add to the bill. A program can only make itself longer. -/
  charge : String → Nat → M Unit
  /-- Fail: the checker certifies nothing. -/
  fail : {α : Type} → M α
  /-- The two constant truth values, free. -/
  btrue : B
  bfalse : B
  /-- What a truth value can become, and nothing else: a count (`countB`: one if true; `nscale k`: the
      concrete `k` if true, else zero), a choice between two numbers (`selectV`, charged 1 like `min`), or
      another truth value through a gate (charged 1 each). There is no branching: a checker's own code
      never learns a truth value, so what it computes next never depends on the network; and no operation
      takes a count together with a truth value, so a count is only ever a sum of concrete multiples of
      truth values (see the header). -/
  countB : B → N
  nscale : Nat → B → N
  selectV : String → B → V → V → M V
  bnot : String → B → M B
  band : String → B → B → M B
  bor : String → B → B → M B
  /-- Counts. Free, as the Python checker's bookkeeping is. -/
  nzero : N
  nsucc : N → N
  nadd : N → N → N
  nofNat : Nat → N
  /-- The checker's rules, charged as `cost-v3` charges the leaf (`CostM.single`, `CostM.interval`). -/
  single : Graph → Task → Input → M B
  interval : Graph → Task → Box → M B
  /-- The single rule on a general network (attention): the general checker's exact forward pass on one
      input, charged as cost-v3 charges a single leaf of a general network (`CostM.gsingle`,
      `CountedGeneral.lean`; its soundness is `CostM.gsingle_correct`). `single` covers linear networks
      only; on a network with attention it fails. -/
  gsingle : Graph → Task → Input → M B
  /-- The interval rule on a general network: the general checker's interval arithmetic over a box of
      inputs, charged as cost-v3 charges an interval leaf of a general network (`CostM.ginterval`,
      `CountedGeneral.lean`; its soundness is `CostM.ginterval_correct`). Allowed only in the
      maximum-knowledge condition (`accept/allowlist-maximum.txt`): it is one of the fixed rules lane's rules
      for groups of inputs, supplied rather than found. -/
  ginterval : Graph → Task → Box → M B
  /-- The token_interval rule on a general network, for a list of leaves: per leaf, the general checker's
      token_interval leaf (each position's rows kept apart per token for as long as the graph allows),
      charged as cost-v3 charges a proof's token_interval leaves: each leaf's own work to `token_interval`,
      and the rows that depend on their token alone to `tables`, once over the list (`CostM.gtokenIntervals`,
      `TokensCost.lean`; its soundness is `CostM.gtokenIntervals_correct`). One verdict per box, `false` for
      a box without a constant label. One call with all of a proof's token_interval leaves pays cost-v3's
      price; each further call pays for its rows again. Allowed only in the maximum-knowledge condition. -/
  gtokenIntervals : Graph → Task → List Box → M (List B)

instance instMonadInterp (I : Interp) : Monad I.M := I.monad

/-- A scored checker: a computation of a count, for every interpreter. -/
abbrev Checker := (I : Interp) → I.M I.N

/-- The interpreter the service runs: the charges of `cost-v3`, in `CostM`. -/
@[reducible] def Interp.counting : Interp where
  M := CostM
  monad := inferInstance
  V := Q
  B := Bool
  N := Nat
  weight := CostM.weight
  weightShape := CostM.weightShape
  weightSize := CostM.weightSize
  cert := CostM.cert
  certSize := CostM.certSize
  lit := CostM.lit
  zero := ⟨0⟩
  add := CostM.qadd
  sub := CostM.qsub
  muladd := CostM.qmuladd
  neg := CostM.qneg
  min := CostM.qmin
  max := CostM.qmax
  lt := CostM.qlt
  le := CostM.qle
  eq := CostM.qeq
  exp := CostM.qexp
  charge := CostM.charge
  fail := CostM.fail
  btrue := true
  bfalse := false
  countB := fun b => cond b 1 0
  nscale := fun k b => cond b k 0
  selectV := fun cat b x y => ⟨fun _ c => some (cond b x y, c.add cat 1)⟩
  bnot := fun cat b => ⟨fun _ c => some (!b, c.add cat 1)⟩
  band := fun cat a b => ⟨fun _ c => some (a && b, c.add cat 1)⟩
  bor := fun cat a b => ⟨fun _ c => some (a || b, c.add cat 1)⟩
  nzero := 0
  nsucc := Nat.succ
  nadd := Nat.add
  nofNat := id
  single := CostM.single
  interval := CostM.interval
  gsingle := CostM.gsingle
  ginterval := CostM.ginterval
  gtokenIntervals := CostM.gtokenIntervals

/-! ## The counting interpreter, operation by operation (all by `rfl`, for `simp`) -/

namespace Interp

@[simp] theorem counting_M : counting.M = CostM := rfl
@[simp] theorem counting_V : counting.V = Q := rfl
@[simp] theorem counting_B : counting.B = Bool := rfl
@[simp] theorem counting_N : counting.N = Nat := rfl
@[simp] theorem counting_weight : counting.weight = CostM.weight := rfl
@[simp] theorem counting_weightShape : counting.weightShape = CostM.weightShape := rfl
@[simp] theorem counting_weightSize : counting.weightSize = CostM.weightSize := rfl
@[simp] theorem counting_cert : counting.cert = CostM.cert := rfl
@[simp] theorem counting_certSize : counting.certSize = CostM.certSize := rfl
@[simp] theorem counting_lit : counting.lit = CostM.lit := rfl
@[simp] theorem counting_zero : counting.zero = (⟨(0 : Rat)⟩ : Q) := rfl
@[simp] theorem counting_add : counting.add = CostM.qadd := rfl
@[simp] theorem counting_sub : counting.sub = CostM.qsub := rfl
@[simp] theorem counting_muladd : counting.muladd = CostM.qmuladd := rfl
@[simp] theorem counting_neg : counting.neg = CostM.qneg := rfl
@[simp] theorem counting_min : counting.min = CostM.qmin := rfl
@[simp] theorem counting_max : counting.max = CostM.qmax := rfl
@[simp] theorem counting_lt : counting.lt = CostM.qlt := rfl
@[simp] theorem counting_le : counting.le = CostM.qle := rfl
@[simp] theorem counting_eq : counting.eq = CostM.qeq := rfl
@[simp] theorem counting_exp : counting.exp = CostM.qexp := rfl
@[simp] theorem counting_charge : counting.charge = CostM.charge := rfl
@[simp] theorem counting_btrue : counting.btrue = true := rfl
@[simp] theorem counting_bfalse : counting.bfalse = false := rfl
@[simp] theorem counting_countB (b : counting.B) : counting.countB b = cond b 1 0 := rfl
@[simp] theorem counting_nscale (k : Nat) (b : counting.B) : counting.nscale k b = cond b k 0 := rfl
theorem counting_selectV_run (cat : String) (b : Bool) (x y : Q) (env : Env) (c : Cost) :
    (counting.selectV cat b x y).run env c = some (cond b x y, c.add cat 1) := rfl
theorem counting_bnot_run (cat : String) (b : Bool) (env : Env) (c : Cost) :
    (counting.bnot cat b).run env c = some (!b, c.add cat 1) := rfl
theorem counting_band_run (cat : String) (a b : Bool) (env : Env) (c : Cost) :
    (counting.band cat a b).run env c = some (a && b, c.add cat 1) := rfl
theorem counting_bor_run (cat : String) (a b : Bool) (env : Env) (c : Cost) :
    (counting.bor cat a b).run env c = some (a || b, c.add cat 1) := rfl
@[simp] theorem counting_nzero : counting.nzero = (0 : Nat) := rfl
@[simp] theorem counting_nsucc : counting.nsucc = Nat.succ := rfl
@[simp] theorem counting_nadd : counting.nadd = Nat.add := rfl
@[simp] theorem counting_nofNat : counting.nofNat = id := rfl
@[simp] theorem counting_single : counting.single = CostM.single := rfl
@[simp] theorem counting_interval : counting.interval = CostM.interval := rfl
@[simp] theorem counting_gsingle : counting.gsingle = CostM.gsingle := rfl
@[simp] theorem counting_ginterval : counting.ginterval = CostM.ginterval := rfl
@[simp] theorem counting_gtokenIntervals : counting.gtokenIntervals = CostM.gtokenIntervals := rfl

/-- `do` notation in a checker uses the interpreter's monad; for the counting interpreter that is
    `CostM`'s, so `CostM.run_bind` and `CostM.run_pure` apply once these two are rewritten. -/
@[simp] theorem counting_bind {α β : Type} (x : counting.M α) (f : α → counting.M β) :
    (@Bind.bind counting.M (instMonadInterp counting).toBind α β x f) =
      (@Bind.bind CostM CostM.instMonad.toBind α β x f) := rfl

@[simp] theorem counting_pure {α : Type} (a : α) :
    (@Pure.pure counting.M (instMonadInterp counting).toPure α a) =
      (@Pure.pure CostM CostM.instMonad.toPure α a) := rfl

end Interp

end CompactCheck
