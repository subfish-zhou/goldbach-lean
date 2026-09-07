import MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorWeightBounds
noncomputable section
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace G12SharpWeight
/-- The original low/high Buchstab bounds, with the junction assigned high. -/
def factor (u : ℝ) : ℝ := if u < (1/10 : ℝ) then 561990/1000000 else 564383/1000000
def weight (u : ℝ) : ℝ := factor u*goldbachG11AuthorWeight u
theorem factor_nonneg (u : ℝ) : 0 ≤ factor u := by unfold factor; split_ifs <;> norm_num
theorem factor_le_one (u : ℝ) : factor u ≤ 1 := by unfold factor; split_ifs <;> norm_num
theorem weight_nonneg (u : ℝ) : 0 ≤ weight u :=
  mul_nonneg (factor_nonneg u) (goldbachG11AuthorWeight_nonneg u)
theorem weight_le_eight (u : ℝ) : weight u ≤ 8 := by
  calc
    weight u ≤ 1*8 := mul_le_mul (factor_le_one u) (goldbachG12AuthorWeight_le_eight u)
      (goldbachG11AuthorWeight_nonneg u) zero_le_one
    _ = 8 := by ring
end G12SharpWeight
