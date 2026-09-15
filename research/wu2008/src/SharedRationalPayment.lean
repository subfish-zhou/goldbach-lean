import SharedRationalEnvelope

namespace Wu2008DoubleSieve.SharedRationalPayment
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence
open FixedCoefficientUpperEnclosure (a b s reciprocalPrimitive)
open FixedCoefficientHLowerEnclosure (c)
open Phase22 (u pull AP)
open Phase23 (alphaModel gModel affine_joint CP)
open SharedRationalEnvelope (deltaShared fixedGain cubic_joint_gain)
open scoped Interval
noncomputable section

/-- Reassemble the unchanged outer legs with the strengthened shared middle leg. -/
theorem shared_actual_lower :
    24*alphaModel-gModel+deltaShared ≤ 24*wuLowerCoefficient (1/(2*a))-
      (SingleUpperClassicalLimit.Glin (1/3)+SingleUpperClassicalLimit.Glin s) := by
  have h5 : a ≤ c 5 := by norm_num [a,c,truncatedSixthLowerAlpha]
  have h54 : c 5 ≤ c 4 := by norm_num [a,c,truncatedSixthLowerAlpha]
  have h4s : c 4 ≤ s := by norm_num [a,c,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
  have hs3 := truncatedSixthLower_parameters.2.2.2.1.le
  have j5 := affine_joint 0 0 (42823/151875) le_rfl (h54.trans h4s) h5 (fun t ht => by
    have hu : 5 ≤ u t := by
      apply (le_div_iff₀ truncatedSixthLower_parameters.1).2
      have hh : t ≤ 1/2-5*a := ht.2
      linarith
    have hh := SharpSingleBalance.upper_ratio_antitone (by norm_num : (0 : ℝ) < 5) hu
    have h := hh.trans SharpLogRecurrence.upper_five_div
    have hu0 : 0 < u t := by linarith
    have h' := (div_le_iff₀ hu0).1 h
    linarith)
  have j4 := affine_joint 0 GConvexChord.C GConvexChord.m h5 h4s h54 (fun t ht => by
    have h := GConvexChord.upper_chord (GCurvatureChord.segment_domain ht).2.2
    change wuUpperCoefficient (u t) ≤ GConvexChord.m * u t + GConvexChord.C at h
    linarith)
  have jq := cubic_joint_gain
  have i5 := ClassicalSingleBounds.g_integrable le_rfl ((h54.trans h4s).trans hs3) h5
  have i4 := ClassicalSingleBounds.g_integrable h5 (h4s.trans hs3) h54
  have iq := ClassicalSingleBounds.g_integrable (h5.trans h54) hs3 h4s
  have ih := ClassicalSingleBounds.g_integrable (h5.trans (h54.trans h4s)) le_rfl hs3
  have e1 := intervalIntegral.integral_add_adjacent_intervals i5 i4
  have e2 := intervalIntegral.integral_add_adjacent_intervals (i5.trans i4) iq
  have e3 := intervalIntegral.integral_add_adjacent_intervals ((i5.trans i4).trans iq) ih
  have eh := ClassicalSingleBounds.high_integral_eq
  have erec : reciprocalPrimitive (1/3)-reciprocalPrimitive s = 2*log (6*a/s) := by
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := reciprocalPrimitive) (fun t ht => ?_) ih
    · linarith
    rw [uIcc_of_le hs3] at ht
    rw [ClassicalSingleBounds.g_high ht]
    exact GVariableIntegral.reciprocal_derivative
      (truncatedSixthLower_parameters.1.trans_le ((h5.trans (h54.trans h4s)).trans ht.1))
      (by linarith [ht.2])
  have g1 : SingleUpperClassicalLimit.Glin (1/3) = 4*∫ t in a..(1/3 : ℝ), ClassicalSingleBounds.g t := by
    simp only [SingleUpperClassicalLimit.Glin,SingleUpperClassicalLimit.Gdelta,sub_zero,ClassicalSingleBounds.g,ClassicalSingleBounds.a,a]
  have g2 : SingleUpperClassicalLimit.Glin s = 4*∫ t in a..s, ClassicalSingleBounds.g t := by
    simp only [SingleUpperClassicalLimit.Glin,SingleUpperClassicalLimit.Gdelta,sub_zero,ClassicalSingleBounds.g,ClassicalSingleBounds.a,a]
  have pa : pull a = -wuLowerCoefficient (1/(2*a)) := by
    norm_num [pull,u,a,truncatedSixthLowerAlpha]
  have ps : pull s = -log 3 := by
    have hs : u s+1=4 := by norm_num [u,a,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
    rw [pull,hs,BaseRecurrenceLower.lower_four_value]
  have us : u (c 5)=5 ∧ u (c 4)=4 ∧ u a=1127/200 := by
    norm_num [u,a,c,truncatedSixthLowerAlpha]
  rw [us.1,us.2.2] at j5
  rw [us.1,us.2.1] at j4
  rw [pa] at j5
  rw [ps] at jq
  rw [g1,g2]
  have eh5 : AP 0 0 (42823/151875) (c 5)-AP 0 0 (42823/151875) a =
      (42823/151875)/a*log (c 5/a) := by
    rw [log_div (truncatedSixthLower_parameters.1.trans_le h5).ne' truncatedSixthLower_parameters.1.ne']
    unfold AP GVariableIntegral.affinePrimitive
    norm_num [c]
    ring
  have eh4 : AP 0 GConvexChord.C GConvexChord.m (c 4)-AP 0 GConvexChord.C GConvexChord.m (c 5) = GConvexChord.endpoint := by
    rw [← GConvexChord.primitive_endpoint]
    unfold AP GVariableIntegral.affinePrimitive reciprocalPrimitive GConvexChord.primitive
    norm_num [c,VariableGIntegral.c,SharpSingleBalance.c,SharpSingleBalance.a,VariableGIntegral.a]
    ring
  rw [eh5] at j5
  rw [eh4] at j4
  dsimp [BaseRecurrenceLower.P] at j5
  dsimp [alphaModel,gModel]
  norm_num [a,ClassicalSingleBounds.a,ClassicalSingleBounds.s,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma] at j5 j4 jq e1 e2 e3 eh ⊢
  linarith

/-- All old signed payments, including the fifth gain and the old residual, survive. -/
theorem complete_residual_lower :
    FifthShapePayment.kLower + SignedTotalCorrelation.retainedResidual + deltaShared <
      TruncatedElevenClassicalCountLower.classicalCoefficient := by
  have hb := SignedTotalCorrelation.base_residual_lower
  have hg := SignedTotalCorrelation.g_residual_upper
  have hj := SignedTotalCorrelation.weighted_j_residual_upper
  have hs := shared_actual_lower
  have hf := FifthClassicalShape.payment_lt_fifthPairFlin
  have h6 := Phase25.actual_sixth_ge_new
  have hi := Phase24.original_four_upper
  unfold FifthClassicalShape.payment at hf
  unfold FifthShapePayment.kLower SignedTotalCorrelation.kLower
    SignedTotalCorrelation.correlationGain SignedTotalCorrelation.retainedResidual
    TruncatedElevenClassicalCountLower.classicalCoefficient
  nlinarith only [hb,hg,hj,hs,hf,h6,hi]

/-- The fixed rational lower and the full analytic lower are kept separately. -/
def lowerCoefficient : ℝ := FifthShapePayment.lowerCoefficient + fixedGain/4
def residualCoefficient : ℝ := FifthShapePayment.residualCoefficient + deltaShared/4

theorem joint_actual_residual_lower :
    residualCoefficient < JointHMotherPayment.unroundedCoefficient := by
  rw [JointHMotherPayment.unrounded_coefficient_identity]
  have h := complete_residual_lower
  have hp := Phase20.psi_payment_loss_nonneg
  unfold Phase20.psiPaymentLoss at hp
  unfold residualCoefficient FifthShapePayment.residualCoefficient
    FifthShapePayment.lowerCoefficient
  linarith only [h,hp]

theorem retained_gain_lower :
    lowerCoefficient + SignedTotalCorrelation.retainedResidual/4 ≤ residualCoefficient := by
  have h := SharedRationalEnvelope.fixedGain_le_delta
  unfold lowerCoefficient residualCoefficient FifthShapePayment.residualCoefficient
  linarith only [h]

theorem joint_actual_lower :
    lowerCoefficient < JointHMotherPayment.unroundedCoefficient := by
  have h := joint_actual_residual_lower
  have hg := retained_gain_lower
  have hr := SignedTotalCorrelation.retainedResidual_nonneg
  linarith only [h,hg,hr]

/-- The generic accepted payment theorem is reused, not a new counting argument. -/
theorem full_fixed_count : CorrelationPayment.CountBound lowerCoefficient :=
  CorrelationPayment.pay joint_actual_lower

theorem full_residual_count : CorrelationPayment.CountBound residualCoefficient :=
  CorrelationPayment.pay joint_actual_residual_lower

theorem fixed_strict_improvement : FifthShapePayment.lowerCoefficient < lowerCoefficient := by
  have h := SharedRationalEnvelope.fixedGain_pos
  unfold lowerCoefficient
  linarith only [h]

theorem residual_strict_improvement : FifthShapePayment.residualCoefficient < residualCoefficient := by
  have h := SharedRationalEnvelope.deltaShared_pos
  unfold residualCoefficient
  linarith only [h]

end
end Wu2008DoubleSieve.SharedRationalPayment
