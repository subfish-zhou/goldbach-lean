import MathlibNt.SieveTheory.LiLiuGoldbachG67CenteredBranches
open Set hiding center
open MeasureTheory
open scoped Interval
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open G67Centered
noncomputable section
namespace G67CenteredEnvelope
set_option maxHeartbeats 4000000

theorem squareEarly_integral_loss :
    (∫ s in (2*a)..(a+b), densityPolynomial squareEarly s) - ((a+b)-(2*a))/40000 ≤
      ∫ s in (2*a)..(a+b), G67SumCoordinate.profile s*(Real.log (squareEarlyArgument s)/s) := by
  apply integrate_loss (by norm_num [a,b,c,cutoff])
  · apply continuous_densityPolynomial
    have hL : Continuous S3Correction.L :=
      continuous_iff_continuousAt.mpr (fun x => (S3Correction.L_deriv x).continuousAt)
    unfold squareEarly shiftedLogPolynomial
    fun_prop
  · apply ContinuousOn.mul
    · exact G67SumCoordinate.profile_continuousOn.mono
        (Icc_subset_Icc (by norm_num [a,b,c,cutoff]) (by norm_num [a,b,c,cutoff]))
    · intro s hs
      have pa : 0 < s-a := by
        norm_num [a,b,c,cutoff] at hs ⊢
        linarith [hs.1,hs.2]
      have ps : 0 < s := by
        norm_num [a,b,c,cutoff] at hs ⊢
        linarith [hs.1]
      obtain ⟨apos, bpos, cpos, _⟩ := g67CenteredEnvelope_constants_pos
      apply ContinuousAt.continuousWithinAt
      unfold squareEarlyArgument
      fun_prop (disch := positivity)
  · intro s hs
    refine density_bridge ?_ (squareEarly_bounds hs).1 ((squareEarly_bounds hs).2.trans (by norm_num))
    norm_num [a,b,c,cutoff] at hs ⊢
    constructor <;> linarith [hs.1,hs.2]

theorem squareLate_integral_loss :
    (∫ s in (a+b)..(2*b), densityPolynomial squareLate s) - ((2*b)-(a+b))/40000 ≤
      ∫ s in (a+b)..(2*b), G67SumCoordinate.profile s*(Real.log (squareLateArgument s)/s) := by
  apply integrate_loss (by norm_num [a,b,c,cutoff])
  · apply continuous_densityPolynomial
    have hL : Continuous S3Correction.L :=
      continuous_iff_continuousAt.mpr (fun x => (S3Correction.L_deriv x).continuousAt)
    unfold squareLate shiftedLogPolynomial
    fun_prop
  · apply ContinuousOn.mul
    · exact G67SumCoordinate.profile_continuousOn.mono
        (Icc_subset_Icc (by norm_num [a,b,c,cutoff]) (by norm_num [a,b,c,cutoff]))
    · intro s hs
      have pb : 0 < s-b := by
        norm_num [a,b,c,cutoff] at hs ⊢
        linarith [hs.1,hs.2]
      have ps : 0 < s := by
        norm_num [a,b,c,cutoff] at hs ⊢
        linarith [hs.1]
      obtain ⟨apos, bpos, cpos, _⟩ := g67CenteredEnvelope_constants_pos
      apply ContinuousAt.continuousWithinAt
      unfold squareLateArgument
      fun_prop (disch := positivity)
  · intro s hs
    refine density_bridge ?_ (squareLate_bounds hs).1 ((squareLate_bounds hs).2.trans (by norm_num))
    norm_num [a,b,c,cutoff] at hs ⊢
    constructor <;> linarith [hs.1,hs.2]

theorem rectangleEarly_integral_loss :
    (∫ s in (a+b)..(2*b), densityPolynomial rectangleEarly s) - ((2*b)-(a+b))/40000 ≤
      ∫ s in (a+b)..(2*b), G67SumCoordinate.profile s*(Real.log (rectangleEarlyArgument s)/s) := by
  apply integrate_loss (by norm_num [a,b,c,cutoff])
  · apply continuous_densityPolynomial
    have hL : Continuous S3Correction.L :=
      continuous_iff_continuousAt.mpr (fun x => (S3Correction.L_deriv x).continuousAt)
    unfold rectangleEarly shiftedLogPolynomial
    fun_prop
  · apply ContinuousOn.mul
    · exact G67SumCoordinate.profile_continuousOn.mono
        (Icc_subset_Icc (by norm_num [a,b,c,cutoff]) (by norm_num [a,b,c,cutoff]))
    · intro s hs
      have pa : 0 < s-a := by
        norm_num [a,b,c,cutoff] at hs ⊢
        linarith [hs.1,hs.2]
      have pb : 0 < s-b := by
        norm_num [a,b,c,cutoff] at hs ⊢
        linarith [hs.1,hs.2]
      have ps : 0 < s := by
        norm_num [a,b,c,cutoff] at hs ⊢
        linarith [hs.1]
      obtain ⟨apos, bpos, cpos, _⟩ := g67CenteredEnvelope_constants_pos
      apply ContinuousAt.continuousWithinAt
      unfold rectangleEarlyArgument
      fun_prop (disch := positivity)
  · intro s hs
    refine density_bridge ?_ (rectangleEarly_bounds hs).1 ((rectangleEarly_bounds hs).2.trans (by norm_num))
    norm_num [a,b,c,cutoff] at hs ⊢
    constructor <;> linarith [hs.1,hs.2]

theorem rectangleMiddle_integral_loss :
    (∫ s in (2*b)..(a+c), densityPolynomial rectangleMiddle s) - ((a+c)-(2*b))/40000 ≤
      ∫ s in (2*b)..(a+c), G67SumCoordinate.profile s*(Real.log (rectangleMiddleArgument s)/s) := by
  apply integrate_loss (by norm_num [a,b,c,cutoff])
  · apply continuous_densityPolynomial
    have hL : Continuous S3Correction.L :=
      continuous_iff_continuousAt.mpr (fun x => (S3Correction.L_deriv x).continuousAt)
    unfold rectangleMiddle shiftedLogPolynomial
    fun_prop
  · apply ContinuousOn.mul
    · exact G67SumCoordinate.profile_continuousOn.mono
        (Icc_subset_Icc (by norm_num [a,b,c,cutoff]) (by norm_num [a,b,c,cutoff]))
    · intro s hs
      have pa : 0 < s-a := by
        norm_num [a,b,c,cutoff] at hs ⊢
        linarith [hs.1,hs.2]
      have pb : 0 < s-b := by
        norm_num [a,b,c,cutoff] at hs ⊢
        linarith [hs.1,hs.2]
      have ps : 0 < s := by
        norm_num [a,b,c,cutoff] at hs ⊢
        linarith [hs.1]
      obtain ⟨apos, bpos, cpos, _⟩ := g67CenteredEnvelope_constants_pos
      apply ContinuousAt.continuousWithinAt
      unfold rectangleMiddleArgument
      fun_prop (disch := positivity)
  · intro s hs
    refine density_bridge ?_ (rectangleMiddle_bounds hs).1 ((rectangleMiddle_bounds hs).2.trans (by norm_num))
    norm_num [a,b,c,cutoff] at hs ⊢
    constructor <;> linarith [hs.1,hs.2]

theorem rectangleLate_integral_loss :
    (∫ s in (a+c)..(cutoff), densityPolynomial rectangleLate s) - ((cutoff)-(a+c))/40000 ≤
      ∫ s in (a+c)..(cutoff), G67SumCoordinate.profile s*(Real.log (rectangleLateArgument s)/s) := by
  apply integrate_loss (by norm_num [a,b,c,cutoff])
  · apply continuous_densityPolynomial
    have hL : Continuous S3Correction.L :=
      continuous_iff_continuousAt.mpr (fun x => (S3Correction.L_deriv x).continuousAt)
    unfold rectangleLate shiftedLogPolynomial
    fun_prop
  · apply ContinuousOn.mul
    · exact G67SumCoordinate.profile_continuousOn.mono
        (Icc_subset_Icc (by norm_num [a,b,c,cutoff]) (by norm_num [a,b,c,cutoff]))
    · intro s hs
      have pb : 0 < s-b := by
        norm_num [a,b,c,cutoff] at hs ⊢
        linarith [hs.1,hs.2]
      have pc : 0 < s-c := by
        norm_num [a,b,c,cutoff] at hs ⊢
        linarith [hs.1,hs.2]
      have ps : 0 < s := by
        norm_num [a,b,c,cutoff] at hs ⊢
        linarith [hs.1]
      obtain ⟨apos, bpos, cpos, _⟩ := g67CenteredEnvelope_constants_pos
      apply ContinuousAt.continuousWithinAt
      unfold rectangleLateArgument
      fun_prop (disch := positivity)
  · intro s hs
    refine density_bridge ?_ (rectangleLate_bounds hs).1 ((rectangleLate_bounds hs).2.trans (by norm_num))
    norm_num [a,b,c,cutoff] at hs ⊢
    constructor <;> linarith [hs.1,hs.2]

/-- The exact weighted length includes the half-square and all three rectangle branches. -/
theorem weighted_length :
    (1/2 : ℝ)*((a+b-2*a)+(2*b-(a+b))) +
      ((2*b-(a+b))+(a+c-2*b)+(cutoff-(a+c))) = cutoff-2*a := by ring

theorem errorBudget_value : errorBudget = (21/4240000 : ℝ) := by
  norm_num [errorBudget,cutoff,a]

/-- The unconditional real analytic bridge for the unchanged frozen candidate. -/
theorem polynomialIntegral_sub_errorBudget_le_piecewiseIntegral :
    polynomialIntegral - errorBudget ≤ G67SumCoordinate.piecewiseIntegral := by
  have h1 := squareEarly_integral_loss
  have h2 := squareLate_integral_loss
  have h3 := rectangleEarly_integral_loss
  have h4 := rectangleMiddle_integral_loss
  have h5 := rectangleLate_integral_loss
  unfold polynomialIntegral errorBudget G67SumCoordinate.piecewiseIntegral
  simp only [squareEarlyArgument, squareLateArgument, rectangleEarlyArgument,
    rectangleMiddleArgument, rectangleLateArgument] at h1 h2 h3 h4 h5
  norm_num only [a,b,c,cutoff] at h1 h2 h3 h4 h5 ⊢
  linarith only [h1,h2,h3,h4,h5]

end G67CenteredEnvelope
