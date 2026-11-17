import Protected.N_max2_tiny_v8_s0_c64
import Candidate.SplitFacts

/-!
# The claim: the only module that names the claim's module

`Protected.N_max2_tiny_v8_s0_c64` defines the network's constants once more, with the definitions the network's
module has, and adds the certificate, the claimed count and the target. Lean and the kernel find the two
`weights` equal by unfolding both, so the instance in the form the service asks for is the fact of
`SplitFacts`, and the target follows from soundness.
-/

namespace Candidate.SplitTop

open CompactCheck Candidate.SplitGeneral

theorem D_instance : CostM.billed (D Interp.counting)
    ⟨Protected.N_max2_tiny_v8_s0_c64.weights, Protected.N_max2_tiny_v8_s0_c64.cert⟩ = some (64, 64 * 63) :=
  Candidate.SplitFacts.D_run

theorem performance : Protected.N_max2_tiny_v8_s0_c64.Target := by
  show 64 ≤ numCorrect Protected.N_max2_tiny_v8_s0.graph Protected.N_max2_tiny_v8_s0.weights Protected.N_max2_tiny_v8_s0.task
  obtain ⟨cost, h⟩ := CostM.exec_of_billed D_instance
  exact D_sound _ _ 64 cost h

end Candidate.SplitTop
