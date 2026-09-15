import Hf4TargetConstants

noncomputable section
namespace Hf4Target
open Real Polynomial

/-- Exact evaluation of the existing abstract-root primitive at a linear block. -/
theorem simple_linear_value (u c t : ℝ) :
    SigmaSimpleResiduePrimitive.simplePrimitive (C u) (X+C c) t =
      u*log (t+c) := by
  simp [SigmaSimpleResiduePrimitive.simplePrimitive,
    SigmaSimpleResiduePrimitive.residue, SigmaRationalOuterFTC.rootPrimitive]

end Hf4Target
