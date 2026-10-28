import MathlibNt.SieveTheory.LiLiuGoldbachS3IntegralScalarMainBound
import MathlibNt.SieveTheory.LiLiuGoldbachS3CorrectionEvaluation
import MathlibNt.SieveTheory.LiLiuGoldbachS2IntegralScalar
import MathlibNt.SieveTheory.LiLiuGoldbachB10IntegralReduction
import MathlibNt.SieveTheory.LiLiuGoldbachB8IntegralReduction
import MathlibNt.SieveTheory.LiLiuGoldbachWeightRemainingFive


open MathlibNt.SieveTheory.SwitchingPrinciple
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The five certified negative scalar entries; the positive lower factors remain literal. -/
noncomputable def goldbachWeightFiveNegativeScalarCoefficient : ℝ :=
  Real.exp (-Real.eulerMascheroniConstant) *
    ((159/2 : ℝ)*dimensionOneLowerLinearSieveFactor 6 +
      (33/2 : ℝ)*dimensionOneLowerLinearSieveFactor (33/8 : ℝ)) -
    (2360636/100000 : ℝ) - (1951976/100000 : ℝ) -
    4*(84289/100000 : ℝ) - (540996/100000 : ℝ) - 2*(60962/100000 : ℝ)


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig