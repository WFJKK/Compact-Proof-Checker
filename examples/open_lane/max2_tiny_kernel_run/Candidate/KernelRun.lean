import Protected.N_max2_tiny_v8_s0
import CompactCheck.SemanticsKernel

/-!
# The kernel runs the network's graph

A lemma, not a proof of the target: the specification's `semGraph` on the network's weights and one input,
evaluated by the kernel. `semGraph_eqK` (CompactCheck/SemanticsKernel.lean) turns the statement into one about
`semGraphK`, which computes the same tensor from lists and reads it through a tree.
-/

namespace Candidate.KernelRun

open CompactCheck Protected.N_max2_tiny_v8_s0

/-- The network has no `exp` or `softmax`; the instance only lets `semGraph` be stated over ℚ. -/
local instance : ExpDiv ℚ := ⟨fun x => x, fun a b => a / b⟩

/-- On input [3, 5] the network's output has 8 entries, and entry 5 is above entry 3. -/
theorem run : (semGraph graph weights [3, 5]).map (fun t => (t.data.size, decide (t.get 3 < t.get 5))) =
    some (8, true) := by
  rw [semGraph_eqK]; decide +kernel

end Candidate.KernelRun
