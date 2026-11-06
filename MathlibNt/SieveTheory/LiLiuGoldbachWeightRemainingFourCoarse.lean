module

public import MathlibNt.SieveTheory.LiLiuGoldbachB9LogGridLimit
public import MathlibNt.SieveTheory.LiLiuGoldbachB9NormalizedMainMass
public import MathlibNt.SieveTheory.LiLiuGoldbachB9InnerIntegral
public import MathlibNt.SieveTheory.LiLiuGoldbachWeightRemainingFive


@[expose] public section

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The four literal signed terms; no analytic estimate is part of their definition. -/
noncomputable def goldbachWeightRemainingFour
    (A : Finset ℕ) (N : ℕ) (z b c : ℝ) : ℤ :=
  goldbachWeightG6 A N z b + goldbachWeightG7 A N z b c -
    goldbachWeightG11 A N z b - goldbachWeightG12 A N z b c

theorem goldbachWeightRemainingFive_eq_remainingFour_sub_s5
    (A : Finset ℕ) (N : ℕ) (z b c : ℝ) :
    goldbachWeightRemainingFive A N z b c =
      goldbachWeightRemainingFour A N z b c - goldbachS5Closed A N z ((N : ℝ) ^ ((1 : ℝ) / 3)) := by
  unfold goldbachWeightRemainingFive goldbachWeightRemainingFour
  ring


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig