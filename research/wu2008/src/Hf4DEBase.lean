import Hf4TargetConstants
import Hf4OuterTerminal
import TerminalESignedCoefficientValues

noncomputable section
namespace Hf4DE
open Real

theorem log_sub_bounds {a b l u : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hl : 1 ≤ l) (hu : 1 ≤ u) (hL : l^16*a ≤ b) (hU : b ≤ u^16*a) :
    16*RemainingHf.basicLower l ≤ log b-log a ∧
    log b-log a ≤ 16*RemainingHf.basicUpper u := by
  have hp : 0 < b/a := div_pos hb ha
  have hlow := log_le_log (by positivity : 0 < l^16) ((le_div_iff₀ ha).mpr hL)
  have hupp := log_le_log hp ((div_le_iff₀ ha).mpr hU)
  rw [log_pow, log_div hb.ne' ha.ne'] at hlow hupp
  have h1 := RemainingHf.basicLower_le hl
  have h2 := RemainingHf.le_basicUpper hu
  norm_num only [Nat.cast_ofNat] at hlow hupp
  constructor <;> linarith only [hlow,hupp,h1,h2]

theorem mul_bounds {c x cl cu xl xu : ℝ}
    (hc : cl ≤ c ∧ c ≤ cu) (hx : xl ≤ x ∧ x ≤ xu)
    (hxl : 0 ≤ xl) (hcl : 0 ≤ cl) : cl*xl ≤ c*x ∧ c*x ≤ cu*xu := by
  constructor
  · exact mul_le_mul hc.1 hx.1 hxl (hcl.trans hc.1)
  · exact mul_le_mul hc.2 hx.2 (hxl.trans hx.1) (hcl.trans (hc.1.trans hc.2))

end Hf4DE
