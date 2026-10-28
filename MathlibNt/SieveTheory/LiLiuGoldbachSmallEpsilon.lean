import MathlibNt.SieveTheory.LiLiuGoldbachWeightRemainingEight

open Filter
open MathlibNt.SieveTheory.SwitchingPrinciple

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable def goldbachS2LogCoefficient (ε : ℝ) : ℝ :=
  8 * Real.log ((1 - ((9 : ℝ) / 19 - ε)) / ((9 : ℝ) / 19 - ε))

noncomputable def goldbachWeightKnownCoefficient (ε : ℝ) : ℝ :=
  (1 - ε) * Real.exp (-Real.eulerMascheroniConstant) *
      ((159 / 2 : ℝ) * dimensionOneLowerLinearSieveFactor 6 +
        (33 / 2 : ℝ) * dimensionOneLowerLinearSieveFactor (33 / 8 : ℝ)) -
    4 * goldbachS2LogCoefficient ε - 8 * (1 - ε) * goldbachB10I10

@[simp] theorem goldbachS2LogCoefficient_zero :
    goldbachS2LogCoefficient 0 = 8 * Real.log (10 / 9 : ℝ) := by
  norm_num [goldbachS2LogCoefficient]

@[simp] theorem goldbachWeightKnownCoefficient_zero :
    goldbachWeightKnownCoefficient 0 =
      Real.exp (-Real.eulerMascheroniConstant) *
        ((159 / 2 : ℝ) * dimensionOneLowerLinearSieveFactor 6 +
          (33 / 2 : ℝ) * dimensionOneLowerLinearSieveFactor (33 / 8 : ℝ)) -
        32 * Real.log (10 / 9 : ℝ) - 8 * goldbachB10I10 := by
  simp only [goldbachWeightKnownCoefficient, goldbachS2LogCoefficient_zero]
  ring


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig