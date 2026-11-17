import Protected.N_max2_tiny_v8_s0_c64
import CompactCheck.Soundness
import CompactCheck.CountedOps

/-!
# A checker that leans on a stored weight: what the last-bits test is for

Brute force in the counted language, as `max2_tiny_scored`, with one more condition on every input: the
first entry of the embedding must be exactly the number written into the checker's code. The proof is sound
and the kernel accepts it; it certifies all 64 inputs of this network. It is the smallest case of a checker
whose count rests on a comparison of the weights with numbers it holds, the pattern of a checker that carries
a copy of the weights and computes on its copy for free.

The service's last-bits test (docs/COUNTED.md) runs the same checker on copies of the network whose weights
differ in their last bits. This one certifies nothing there, and is refused scoring. `max2_tiny_scored`,
which computes on the weights it is given, certifies the same 64.
-/

namespace Candidate.StoredWeight

open CompactCheck Protected.N_max2_tiny_v8_s0_c64

/-! ## General layer -/

/-- Whether the first embedding weight is 1505767040 / 2^32, the value this network has. -/
def stored (I : Interp) : I.M I.B := do
  let w ← I.weight "embedding.weight" 0
  let scale ← I.lit "stored" 4294967296
  let scaled ← I.muladd "stored" I.zero w scale
  let m ← I.lit "stored" 1505767040
  I.eq "stored" scaled m

/-- The single-input rule on each input of `xs`, counting an input when it passes and `b` holds. -/
def countBoth (I : Interp) (g : Graph) (task : Task) (b : I.B) : List Input → I.M I.N
  | [] => pure I.nzero
  | x :: xs => do
    let ok ← I.single g task x
    let both ← I.band "stored" b ok
    let n ← countBoth I g task b xs
    pure (I.nadd (I.countB both) n)

/-- The checker: every input of the task's space, each counted only if the stored weight matches. -/
def D : Checker := fun I => do
  let b ← stored I
  countBoth I graph task b (allInputs task.space)

open Classical in
/-- `countBoth` never counts more than the inputs that are correct, for any weights, bill and `b`. -/
theorem countBoth_le (env : Env) (b : Bool) : ∀ (xs : List Input) (c : Cost) (n : Nat) (c' : Cost),
    (countBoth Interp.counting graph task b xs).run env c = some (n, c') →
    n ≤ xs.countP (fun x => decide (Correct graph env.weights task x))
  | [], c, n, c', h => by
    simp only [countBoth, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    omega
  | x :: xs, c, n, c', h => by
    simp only [countBoth, CostM.run_bind] at h
    split at h
    · rename_i ok c1 hs
      split at h
      · rename_i m c2 hm
        have ih := countBoth_le env b xs _ m c2 hm
        rw [List.countP_cons]
        simp only [CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
        cases ok with
        | false =>
          simp only [Bool.and_false, Bool.cond_false, Nat.add_eq] at h
          omega
        | true =>
          have hc : Correct graph env.weights task x := singleOk_correct graph env.weights task x (CostM.single_spec hs)
          simp only [hc, decide_true, ite_true]
          cases b <;> simp only [Bool.and_true, Bool.cond_true, Bool.cond_false, Nat.add_eq] at h <;> omega
      · cases h
    · cases h

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task := by
  intro w c n cost h
  unfold numCorrect
  simp only [D, CostM.exec, CostM.run_bind] at h
  split at h
  · rename_i b c1 hb
    exact countBoth_le ⟨w, c⟩ b (allInputs task.space) c1 n cost h
  · cases h

/-! ## Specific layer -/

/-- The kernel runs the checker on the protected weights: the stored weight matches, all 64 inputs pass. The
    bill is 64 forward passes at 63 operations, 64 conjunctions, and the 4 operations of the comparison. -/
theorem D_instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (64, 64 * 63 + 64 + 4) := by
  decide +kernel

theorem performance : Target := by
  show claimedCount ≤ numCorrect graph weights task
  obtain ⟨cost, h⟩ := CostM.exec_of_billed D_instance
  exact D_sound weights cert 64 cost h

end Candidate.StoredWeight
