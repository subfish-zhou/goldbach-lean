import MathlibNt.SieveTheory.LiLiuGoldbachB8IntegralReduction

open MeasureTheory Set
open scoped Interval
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

#check goldbachB8InnerIntegral_eq
#check goldbachB8InnerIntegral_eq_reciprocal
#check goldbachB8MainIntegral_eq_singleIntegral
#check continuousOn_goldbachB8SingleIntegrand
#check intervalIntegrable_goldbachB8SingleIntegrand
#check goldbachB8SingleIntegrand_nonneg
#check continuousOn_goldbachB8TransformedIntegrand
#check intervalIntegrable_goldbachB8TransformedIntegrand
#check goldbachB8TransformedIntegrand_nonneg
#check goldbachB8ReductionChange_endpoints
#check goldbachB8ReductionChange_mapsTo
#check hasDerivAt_goldbachB8ReductionChange
#check continuousOn_goldbachB8ReductionChange
#check continuousOn_goldbachB8ReductionJacobian
#check goldbachB8ReductionChange_integrand
#check goldbachB8ReductionChange_oriented
#check goldbachB8MainIntegral_eq_transformedIntegral

#print axioms goldbachB8InnerIntegral_eq
#print axioms goldbachB8InnerIntegral_eq_reciprocal
#print axioms goldbachB8MainIntegral_eq_singleIntegral
#print axioms continuousOn_goldbachB8SingleIntegrand
#print axioms intervalIntegrable_goldbachB8SingleIntegrand
#print axioms goldbachB8SingleIntegrand_nonneg
#print axioms continuousOn_goldbachB8TransformedIntegrand
#print axioms intervalIntegrable_goldbachB8TransformedIntegrand
#print axioms goldbachB8TransformedIntegrand_nonneg
#print axioms goldbachB8ReductionChange_endpoints
#print axioms goldbachB8ReductionChange_mapsTo
#print axioms hasDerivAt_goldbachB8ReductionChange
#print axioms continuousOn_goldbachB8ReductionChange
#print axioms continuousOn_goldbachB8ReductionJacobian
#print axioms goldbachB8ReductionChange_integrand
#print axioms goldbachB8ReductionChange_oriented
#print axioms goldbachB8MainIntegral_eq_transformedIntegral

#print goldbachB8MainIntegral
#print axioms goldbachB8MainIntegral

example : goldbachB8MainIntegral =
    ∫ u in (3 / 11 : ℝ)..(1 / 3),
      ∫ v in u..((1 - u) / 2), 1 / (u * v * (1 - u - v)) := rfl

example (u : ℝ) (hu : u ∈ Icc (3 / 11 : ℝ) (1 / 3)) :
    (∫ v in u..((1 - u) / 2), 1 / (u * v * (1 - u - v))) =
      Real.log ((1 - 2 * u) / u) / (u * (1 - u)) :=
  goldbachB8InnerIntegral_eq hu

example :
    (∫ v in (3 / 11 : ℝ)..((1 - 3 / 11) / 2),
      1 / ((3 / 11) * v * (1 - 3 / 11 - v))) =
      Real.log ((1 - 2 * (3 / 11)) / (3 / 11)) /
        ((3 / 11) * (1 - 3 / 11)) :=
  goldbachB8InnerIntegral_eq (by norm_num)

example :
    (∫ v in (1 / 3 : ℝ)..((1 - 1 / 3) / 2),
      1 / ((1 / 3) * v * (1 - 1 / 3 - v))) = 0 := by
  rw [goldbachB8InnerIntegral_eq (by norm_num)]
  norm_num

example :
    (∫ u in (3 / 11 : ℝ)..(1 / 3),
      ∫ v in u..((1 - u) / 2), 1 / (u * v * (1 - u - v))) =
      ∫ u in (3 / 11 : ℝ)..(1 / 3), Real.log (1 / u - 2) / (u * (1 - u)) :=
  goldbachB8MainIntegral_eq_singleIntegral

example :
    (∫ u in (3 / 11 : ℝ)..(1 / 3),
      ∫ v in u..((1 - u) / 2), 1 / (u * v * (1 - u - v))) =
      ∫ t in (2 : ℝ)..(8 / 3), Real.log (t - 1) / t :=
  goldbachB8MainIntegral_eq_transformedIntegral

example : goldbachB8MainIntegral =
    ∫ u in (3 / 11 : ℝ)..(1 / 3), Real.log (1 / u - 2) / (u * (1 - u)) :=
  goldbachB8MainIntegral_eq_singleIntegral

example : goldbachB8MainIntegral =
    ∫ t in (2 : ℝ)..(8 / 3), Real.log (t - 1) / t :=
  goldbachB8MainIntegral_eq_transformedIntegral

example : HasDerivAt (fun t : ℝ => 1 / (t + 1)) (-1 / ((2 : ℝ) + 1) ^ 2) 2 :=
  hasDerivAt_goldbachB8ReductionChange (by norm_num)

example : HasDerivAt (fun t : ℝ => 1 / (t + 1))
    (-1 / ((8 / 3 : ℝ) + 1) ^ 2) (8 / 3) :=
  hasDerivAt_goldbachB8ReductionChange (by norm_num)

example : (1 / ((2 : ℝ) + 1) = 1 / 3) ∧
    (1 / ((8 / 3 : ℝ) + 1) = 3 / 11) :=
  goldbachB8ReductionChange_endpoints

example : IntervalIntegrable
    (fun u : ℝ => Real.log (1 / u - 2) / (u * (1 - u))) volume (3 / 11) (1 / 3) :=
  intervalIntegrable_goldbachB8SingleIntegrand

example : IntervalIntegrable (fun t : ℝ => Real.log (t - 1) / t) volume 2 (8 / 3) :=
  intervalIntegrable_goldbachB8TransformedIntegrand

example : ContinuousOn (fun u : ℝ => Real.log (1 / u - 2) / (u * (1 - u)))
    (Icc (3 / 11 : ℝ) (1 / 3)) :=
  continuousOn_goldbachB8SingleIntegrand

example : ContinuousOn (fun t : ℝ => Real.log (t - 1) / t) (Icc (2 : ℝ) (8 / 3)) :=
  continuousOn_goldbachB8TransformedIntegrand

example (u : ℝ) (hu : u ∈ Icc (3 / 11 : ℝ) (1 / 3)) :
    0 ≤ Real.log (1 / u - 2) / (u * (1 - u)) :=
  goldbachB8SingleIntegrand_nonneg hu

example (t : ℝ) (ht : t ∈ Icc (2 : ℝ) (8 / 3)) :
    0 ≤ Real.log (t - 1) / t :=
  goldbachB8TransformedIntegrand_nonneg ht

example : Real.log (1 / (3 / 11 : ℝ) - 2) / ((3 / 11) * (1 - 3 / 11)) =
    Real.log (5 / 3) / (24 / 121) := by
  norm_num

example : Real.log (1 / (1 / 3 : ℝ) - 2) / ((1 / 3) * (1 - 1 / 3)) = 0 := by
  norm_num

example : Real.log ((2 : ℝ) - 1) / 2 = 0 := by
  norm_num

example : Real.log ((8 / 3 : ℝ) - 1) / (8 / 3) = Real.log (5 / 3) / (8 / 3) := by
  norm_num