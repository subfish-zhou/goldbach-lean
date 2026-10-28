import Hf4QuadCompactKernel
import Hf4QuadIntegral

noncomputable section
namespace Hf4Quad

/-- The shorter rational kernel encloses the unchanged original endpoint mass. -/
theorem endpoint_compact_model {m h : ℝ} {p : Cubic} {e : ℝ}
    (hh : 0 < h) (ha : 1 ≤ m-h) (hb : m+h ≤ 3)
    (hm : Model (fun x => compactKernel (m+h*x)) p e) :
    2*h*(p.a+p.c/3-e) ≤ SigmaActualBlockSeparable.endpointCellMass (m-h) (m+h) ∧
    SigmaActualBlockSeparable.endpointCellMass (m-h) (m+h) ≤ 2*h*(p.a+p.c/3+e) := by
  apply endpoint_model hh ha hb
  intro x hx
  have ht : m+h*x ∈ Set.Icc 1 3 := by
    obtain ⟨hl, hu⟩ := abs_le.mp hx
    constructor <;> nlinarith
  simpa only [compactKernel_eq ht] using hm x hx

end Hf4Quad
#print axioms Hf4Quad.endpoint_compact_model
