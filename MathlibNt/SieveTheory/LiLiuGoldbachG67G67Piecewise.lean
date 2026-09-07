import MathlibNt.SieveTheory.LiLiuGoldbachG67G67Truncation

open Set MeasureTheory
open scoped Interval
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section
namespace G67SumCoordinate

/-- Integrate the early closed branch on a certified subinterval. -/
theorem integral_weight_first {a b c d l r : ℝ} (φ : ℝ → ℝ)
    (hlr : l ≤ r) (hL : r ≤ a+d) (hU : r ≤ b+c) :
    (∫ s in l..r, φ s * weight a b c d s) =
      ∫ s in l..r, φ s * (Real.log ((s-c)*(s-a)/(a*c))/s) := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hlr] at hs
  dsimp
  rw [weight_first (hs.2.trans hL) (hs.2.trans hU)]

/-- Integrate the middle closed branch on a certified subinterval. -/
theorem integral_weight_middle {a b c d l r : ℝ} (φ : ℝ → ℝ)
    (hlr : l ≤ r) (hL : r ≤ a+d) (hU : b+c ≤ l) :
    (∫ s in l..r, φ s * weight a b c d s) =
      ∫ s in l..r, φ s * (Real.log (b*(s-a)/(a*(s-b)))/s) := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hlr] at hs
  dsimp
  rw [weight_middle (hs.2.trans hL) (hU.trans hs.1)]

/-- Integrate the late closed branch on a certified subinterval. -/
theorem integral_weight_last {a b c d l r : ℝ} (φ : ℝ → ℝ)
    (hlr : l ≤ r) (hL : a+d ≤ l) (hU : b+c ≤ l) :
    (∫ s in l..r, φ s * weight a b c d s) =
      ∫ s in l..r, φ s * (Real.log (b*d/((s-d)*(s-b)))/s) := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hlr] at hs
  dsimp
  rw [weight_last (hL.trans hs.1) (hU.trans hs.1)]

/-- The square has two elementary branches, split at a+b. -/
theorem square_integral_piecewise :
    (∫ s in ((4/53 : ℝ)+(4/53 : ℝ))..((4/33 : ℝ)+(4/33 : ℝ)),
      profile s * weight (4/53) (4/33) (4/53) (4/33) s) =
    (∫ s in ((4/53 : ℝ)+(4/53 : ℝ))..((4/53 : ℝ)+(4/33 : ℝ)),
      profile s * (Real.log ((s-4/53)*(s-4/53)/((4/53)*(4/53)))/s)) +
    (∫ s in ((4/53 : ℝ)+(4/33 : ℝ))..((4/33 : ℝ)+(4/33 : ℝ)),
      profile s * (Real.log (((4/33)*(4/33))/((s-4/33)*(s-4/33)))/s)) := by
  rw [split_integral (m := (4/53 : ℝ)+(4/33 : ℝ)) (by norm_num) (by norm_num)
    square_density_continuousOn]
  rw [integral_weight_first profile (by norm_num) (by norm_num) (by norm_num),
    integral_weight_last profile (by norm_num) (by norm_num) (by norm_num)]

/-- The rectangle has three branches; the last ends at the exact vanishing cutoff. -/
theorem rectangle_integral_piecewise :
    (∫ s in ((4/53 : ℝ)+(4/33 : ℝ))..((1/2 : ℝ)-2*(4/53 : ℝ)),
      profile s * weight (4/53) (4/33) (4/33) (3/11) s) =
    (∫ s in ((4/53 : ℝ)+(4/33 : ℝ))..((4/33 : ℝ)+(4/33 : ℝ)),
      profile s * (Real.log ((s-4/33)*(s-4/53)/((4/53)*(4/33)))/s)) +
    ((∫ s in ((4/33 : ℝ)+(4/33 : ℝ))..((4/53 : ℝ)+(3/11 : ℝ)),
      profile s * (Real.log ((4/33)*(s-4/53)/((4/53)*(s-4/33)))/s)) +
    (∫ s in ((4/53 : ℝ)+(3/11 : ℝ))..((1/2 : ℝ)-2*(4/53 : ℝ)),
      profile s * (Real.log (((4/33)*(3/11))/((s-3/11)*(s-4/33)))/s))) := by
  have hc := rectangle_density_continuousOn.mono
    (Icc_subset_Icc (by norm_num : (4/53 : ℝ)+4/33 ≤ (4/53 : ℝ)+4/33)
      (by norm_num : (1/2 : ℝ)-2*(4/53 : ℝ) ≤ (4/33 : ℝ)+3/11))
  rw [split_integral (m := (4/33 : ℝ)+(4/33 : ℝ)) (by norm_num) (by norm_num) hc]
  rw [split_integral (m := (4/53 : ℝ)+(3/11 : ℝ)) (by norm_num) (by norm_num)
    (hc.mono (Icc_subset_Icc (by norm_num) le_rfl))]
  rw [integral_weight_first profile (by norm_num) (by norm_num) (by norm_num),
    integral_weight_middle profile (by norm_num) (by norm_num) (by norm_num),
    integral_weight_last profile (by norm_num) (by norm_num) (by norm_num)]

/-- Five fixed one-dimensional integrals, free of moving-domain min/max operations. -/
def piecewiseIntegral : ℝ :=
  (1/2 : ℝ) *
    ((∫ s in ((4/53 : ℝ)+(4/53 : ℝ))..((4/53 : ℝ)+(4/33 : ℝ)),
      profile s * (Real.log ((s-4/53)*(s-4/53)/((4/53)*(4/53)))/s)) +
    (∫ s in ((4/53 : ℝ)+(4/33 : ℝ))..((4/33 : ℝ)+(4/33 : ℝ)),
      profile s * (Real.log (((4/33)*(4/33))/((s-4/33)*(s-4/33)))/s))) +
    ((∫ s in ((4/53 : ℝ)+(4/33 : ℝ))..((4/33 : ℝ)+(4/33 : ℝ)),
      profile s * (Real.log ((s-4/33)*(s-4/53)/((4/53)*(4/33)))/s)) +
    ((∫ s in ((4/33 : ℝ)+(4/33 : ℝ))..((4/53 : ℝ)+(3/11 : ℝ)),
      profile s * (Real.log ((4/33)*(s-4/53)/((4/53)*(s-4/33)))/s)) +
    (∫ s in ((4/53 : ℝ)+(3/11 : ℝ))..((1/2 : ℝ)-2*(4/53 : ℝ)),
      profile s * (Real.log (((4/33)*(3/11))/((s-3/11)*(s-4/33)))/s))))

/-- Exact equality of the original elementary integral with all five explicit branches. -/
theorem elementaryIntegral_eq_piecewise :
    G67ElementaryIntegral.elementaryIntegral = piecewiseIntegral := by
  rw [elementaryIntegral_eq_truncated]
  unfold truncatedIntegral piecewiseIntegral
  rw [square_integral_piecewise, rectangle_integral_piecewise]

/-- Final actual-C67 consumer: any future certified estimate can target the five fixed branches. -/
theorem actual_constant_lower_piecewise :
    4 * piecewiseIntegral ≤ goldbachG67IntegralConstant := by
  rw [← elementaryIntegral_eq_piecewise]
  exact G67ElementaryIntegral.actual_constant_lower

end G67SumCoordinate
