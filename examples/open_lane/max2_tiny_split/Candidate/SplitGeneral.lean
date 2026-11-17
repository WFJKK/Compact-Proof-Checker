import Protected.N_max2_tiny_v8_s0
import CompactCheck.Soundness
import CompactCheck.CountedOps

/-!
# The scored brute-force proof, split so that a change of the claim touches one module

`max2_tiny_scored` in three modules, to show what the protected modules allow since 17 November 2026
(scripts/make_protected.py). This one, the general layer, imports the network's module alone,
`Protected.N_max2_tiny_v8_s0`, whose name does not change with the claimed count, the certificate or the plan.
The checker may use its `graph` and `task`, as it may use the claim module's.
-/

namespace Candidate.SplitGeneral

open CompactCheck Protected.N_max2_tiny_v8_s0

/-! ## General layer -/

/-- The single-input rule on each input of `xs`, counting the passes; each call is billed. -/
def countSingles (I : Interp) (g : Graph) (task : Task) : List Input → I.M I.N
  | [] => pure I.nzero
  | x :: xs => do
    let ok ← I.single g task x
    let n ← countSingles I g task xs
    pure (I.nadd (I.countB ok) n)

/-- The checker: every input of the task's space. -/
def D : Checker := fun I => countSingles I graph task (allInputs task.space)

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

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task := by
  intro w c n cost h
  unfold numCorrect
  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h

end Candidate.SplitGeneral
