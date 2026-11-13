import Protected.N_max2_tiny_v8_s0_c60_p29539ac6c0088c88
import CompactCheck.Soundness
import CompactCheck.CountedOps

/-!
# A planned open-lane proof: the plan chooses the inputs

The scored brute force of `max2_tiny_scored`, steered by a plan: one number per input, in the order of
`allInputs task.space`; the checker runs the single-input rule on the inputs whose number is not 0. A plan is
free (it is Lean data the checker reads, never a number of the network) and not trusted: `D_sound` holds for
every plan, because the chosen inputs are a sublist of all inputs, and only `D_instance` runs the checker on the
protected module's `plan`, which chooses the last 60 of the 64 inputs.
-/

namespace Candidate.Max2TinyPlanned

open CompactCheck Protected.N_max2_tiny_v8_s0_c60_p29539ac6c0088c88

/-! ## General layer -/

/-- The single-input rule on each input of `xs`, counting the passes; each call is billed. -/
def countSingles (I : Interp) (g : Graph) (task : Task) : List Input → I.M I.N
  | [] => pure I.nzero
  | x :: xs => do
    let ok ← I.single g task x
    let n ← countSingles I g task xs
    pure (I.nadd (I.countB ok) n)

/-- The inputs of `xs` whose number in `fs` is not 0; an input past the end of `fs` is not chosen. -/
def pick : List Nat → List Input → List Input
  | [], _ => []
  | _ :: _, [] => []
  | f :: fs, x :: xs => if f = 0 then pick fs xs else x :: pick fs xs

/-- The planned checker: the inputs the plan chooses. -/
def D : List Nat → Checker := fun p I => countSingles I graph task (pick p (allInputs task.space))

open Classical in
/-- `countSingles` never counts more than the inputs that are correct, for any weights and bill. -/
theorem countSingles_le (env : Env) : ∀ (xs : List Input) (c : Cost) (n : Nat) (c' : Cost),
    (countSingles Interp.counting graph task xs).run env c = some (n, c') →
    n ≤ xs.countP (fun x => decide (Correct graph env.weights task x))
  | [], c, n, c', h => by
    simp only [countSingles, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    omega
  | x :: xs, c, n, c', h => by
    simp only [countSingles, CostM.run_bind] at h
    split at h
    · rename_i ok c1 hs
      split at h
      · rename_i m c2 hm
        have ih := countSingles_le env xs c1 m c2 hm
        rw [List.countP_cons]
        simp only [CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
        cases ok with
        | false => simp only [Bool.cond_false, Nat.add_eq] at h; omega
        | true =>
          have hc : Correct graph env.weights task x := singleOk_correct graph env.weights task x (CostM.single_spec hs)
          simp only [Bool.cond_true, Nat.add_eq] at h
          simp only [hc, decide_true, ite_true]
          omega
      · cases h
    · cases h

/-- What the plan chooses is a sublist of the inputs, whatever the plan. -/
theorem pick_sublist : ∀ (fs : List Nat) (xs : List Input), List.Sublist (pick fs xs) xs
  | [], xs => by simp only [pick]; exact List.nil_sublist xs
  | _ :: _, [] => by simp only [pick]; exact List.Sublist.slnil
  | f :: fs, x :: xs => by
    simp only [pick]
    split
    · exact List.Sublist.cons x (pick_sublist fs xs)
    · exact List.Sublist.cons_cons x (pick_sublist fs xs)

/-- Sound for every plan: the soundness shape of a planned checker. -/
theorem D_sound : ∀ (p : List Nat) (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D p Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task := by
  intro p w c n cost h
  unfold numCorrect
  exact Nat.le_trans (countSingles_le ⟨w, c⟩ (pick p (allInputs task.space)) [] n cost h)
    (pick_sublist p (allInputs task.space)).countP_le

/-! ## Specific layer -/

/-- The kernel runs the checker on the protected plan: 60 inputs chosen, all pass, 60 forward passes at 63. -/
theorem D_instance : CostM.billed (D plan Interp.counting) ⟨weights, cert⟩ = some (60, 60 * 63) := by
  decide +kernel

theorem performance : Target := by
  show claimedCount ≤ numCorrect graph weights task
  obtain ⟨cost, h⟩ := CostM.exec_of_billed D_instance
  exact D_sound plan weights cert 60 cost h

end Candidate.Max2TinyPlanned
