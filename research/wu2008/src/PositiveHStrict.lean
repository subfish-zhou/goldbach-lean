import PositiveHActual

namespace PositiveH
open Finset Real Wu2008DoubleSieve HighTheta HighBoxRecovery
open scoped Classical
noncomputable section

/-- Half the paid logarithmic gain leaves a uniform positive error budget. -/
def lowerCorrection (s : ℝ) : ℝ := (1/20000)*log (2/(s-1))

theorem lowerCorrection_pos {s : ℝ} (hs : 1 < s) (hs3 : s < 3) :
    0 < lowerCorrection s := by
  apply mul_pos (by norm_num)
  exact log_pos ((one_lt_div (by linarith)).mpr (by linarith))

theorem lowerCorrection_uniform {s : ℝ} (hs : 2 ≤ s) (hsmax : s ≤ 29/10) :
    (1/20000)*log (20/19) ≤ lowerCorrection s := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1/20000)
  apply log_le_log (by norm_num)
  apply (le_div_iff₀ (by linarith : 0 < s-1)).mpr
  linarith


end
end PositiveH
