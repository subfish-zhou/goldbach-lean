import MathlibNt.SieveTheory.LiLiuGoldbachG11PrimeKernel

noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The author weight is capped only for the exceptional divisor error. -/
theorem goldbachG12AuthorWeight_le_eight (u : ℝ) :
    goldbachG11AuthorWeight u ≤ 8 := by
  have hm := min_le_right u (1 / 10 : ℝ)
  have hd : 0 < 5 * (1 - min u (1 / 10 : ℝ)) := by linarith
  unfold goldbachG11AuthorWeight
  apply (div_le_iff₀ hd).mpr
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
