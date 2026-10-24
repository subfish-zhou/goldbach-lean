import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation

namespace NineFeedbackStrength
noncomputable section

/-- Author's unchanged Table 1 numbers at s=2.2,...,3.0, recorded ONLY as targets.
Source: Wu 2008 author TeX, lines 775--950. -/
def originalH : Fin 9 → ℝ :=
  ![0.0223939,0.0217196,0.0202876,0.0181433,0.0158644,
    0.0129923,0.0100686,0.0078162,0.0072943]

end
end NineFeedbackStrength
