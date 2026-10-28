import MathlibNt.SieveTheory.LiLiuGoldbachG11PrimeKernel

noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The author weight is capped only for the exceptional divisor error. -/
theorem goldbachG12AuthorWeight_le_eight (u : ℝ) :
    goldbachG11AuthorWeight u ≤ 8 := by
  exact goldbachG11AuthorWeight_global_upper u

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
