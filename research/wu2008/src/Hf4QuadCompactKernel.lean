import Hf4QuadCompactKernelCore
import Hf4QuadKernel

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
noncomputable section
namespace Hf4Quad
open TerminalE SigmaVariableOuterPayment SigmaVariableFull
theorem compactKernel_eq {t : ℝ} (ht : t ∈ Set.Icc 1 3) : compactKernel t = kernel t := by
  have h0 := suCompact_eq (zeroRatio_ge ht.1)
  have h1 := slCompact_eq (negRatio_ge ht.1)
  have hq := slCompact_eq (quadRatio_ge ht.1)
  have hr := slCompact_eq (radRatio_ge ht.1)
  unfold zeroRatio at h0
  unfold negRatio at h1
  unfold quadRatio at hq
  unfold radRatio at hr
  unfold compactKernel kernel
  rw [h0,h1,hq,hr]

end Hf4Quad
#print axioms Hf4Quad.compactKernel_eq
