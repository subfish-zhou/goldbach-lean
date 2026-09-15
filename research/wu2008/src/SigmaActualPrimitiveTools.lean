import SigmaActualBlockSeparable0
import Mathlib.Tactic.ComputeDegree

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial SigmaHermiteActualFTC

/-- Reduced derivative form retaining the full rational principal-part power. -/
theorem rationalPrimitive_deriv (A B : ℝ[X]) (m : ℕ) (t : ℝ)
    (ht : B.eval t ≠ 0) :
    HasDerivAt (fun x => A.eval x / (B.eval x)^(m+1))
      ((A.derivative.eval t * B.eval t - (m+1:ℕ)*A.eval t*B.derivative.eval t) /
        (B.eval t)^(m+2)) t := by
  have h := SigmaRationalOuterFTC.hermiteTerm_deriv
    (A.hasDerivAt t) (B.hasDerivAt t) ht (m+1)
  convert h using 1
  simp only [Nat.add_sub_cancel, pow_add, pow_one, Nat.cast_add, Nat.cast_one]
  field_simp

end SigmaActualBlockSeparable
