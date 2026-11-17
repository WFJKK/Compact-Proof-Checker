import Protected.N_max2_tiny_v8_s0
import Candidate.SplitGeneral

/-!
# The decided fact about the network's weights

The kernel's work is here, and it is about the network's module alone: `weights` is
`Protected.N_max2_tiny_v8_s0.weights`, and the certificate (empty) is written out. Raising the claimed count
renames the claim's module and leaves this module as it is: it is neither edited nor compiled again.
-/

namespace Candidate.SplitFacts

open CompactCheck Protected.N_max2_tiny_v8_s0 Candidate.SplitGeneral

/-- The kernel runs the single rule on all 64 inputs of the network's weights: all pass, and the bill is
    64 forward passes at 63 operations each. -/
theorem D_run : CostM.billed (D Interp.counting) ⟨weights, #[]⟩ = some (64, 64 * 63) := by
  decide +kernel

end Candidate.SplitFacts
