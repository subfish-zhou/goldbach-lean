import MathlibNt.SieveTheory.LiLiuGoldbachS4RetainedEndpoints
import MathlibNt.SieveTheory.LiLiuGoldbachB10RetainedEndpoints

open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace LiLiuAudit

theorem old_s4_from_retained :
    8 * goldbachB8MainIntegral ≤ (60962 / 100000 : ℝ) :=
  S4Retained.goldbachB8MainIntegral_eight_mul_le_60961168.trans (by norm_num)

theorem old_b10_from_retained :
    8 * goldbachB10I10 ≤ (540996 / 100000 : ℝ) :=
  B10Retained.goldbachB10I10_eight_mul_le_540995781.trans (by norm_num)

#print axioms old_s4_from_retained
#print axioms old_b10_from_retained
end LiLiuAudit
