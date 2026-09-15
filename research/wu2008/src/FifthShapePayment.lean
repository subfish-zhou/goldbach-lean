import FifthClassicalShape
import CorrelationPayment

namespace Wu2008DoubleSieve.FifthShapePayment
open Real ClassicalAnalyticLeaves
noncomputable section

/-- The whole signed classical lower with the actual fifth-shape gain. -/
def kLower : ℝ := SignedTotalCorrelation.kLower + FifthClassicalShape.gain

/-- Reassemble the original signed producers and retain their full real residual. -/
theorem complete_residual_lower :
    kLower + SignedTotalCorrelation.retainedResidual <
      TruncatedElevenClassicalCountLower.classicalCoefficient := by
  have hb := SignedTotalCorrelation.base_residual_lower
  have hg := SignedTotalCorrelation.g_residual_upper
  have hj := SignedTotalCorrelation.weighted_j_residual_upper
  have hs := Phase23.shared_actual_lower
  have hf := FifthClassicalShape.payment_lt_fifthPairFlin
  have h6 := Phase25.actual_sixth_ge_new
  have hi := Phase24.original_four_upper
  unfold FifthClassicalShape.payment at hf
  unfold kLower SignedTotalCorrelation.kLower SignedTotalCorrelation.correlationGain
    SignedTotalCorrelation.retainedResidual
    TruncatedElevenClassicalCountLower.classicalCoefficient
  nlinarith only [hb,hg,hj,hs,hf,h6,hi]

theorem complete_lower :
    kLower < TruncatedElevenClassicalCountLower.classicalCoefficient := by
  have h := complete_residual_lower
  have hr := SignedTotalCorrelation.retainedResidual_nonneg
  linarith only [h,hr]

/-- All original H and psi payments are unchanged. -/
def lowerCoefficient : ℝ := kLower/4 + Phase20.fixedPsi + Phase18.g18 +
  (2*BaseHGain.originalGain + fifthHGain/4)

def residualCoefficient : ℝ :=
  lowerCoefficient + SignedTotalCorrelation.retainedResidual/4

theorem fixed_improvement_identity :
    lowerCoefficient = SignedTotalCorrelation.lowerCoefficient +
      FifthClassicalShape.gain/4 := by
  unfold lowerCoefficient kLower SignedTotalCorrelation.lowerCoefficient
  ring

theorem residual_improvement_identity :
    residualCoefficient = CorrelationPayment.residualCoefficient +
      FifthClassicalShape.gain/4 := by
  rw [residualCoefficient, fixed_improvement_identity]
  unfold CorrelationPayment.residualCoefficient
  ring

/-- Compare to the same Qjoint, not a strengthened upper carrier. -/
theorem joint_actual_residual_lower :
    residualCoefficient < JointHMotherPayment.unroundedCoefficient := by
  rw [JointHMotherPayment.unrounded_coefficient_identity]
  have h := complete_residual_lower
  have hp := Phase20.psi_payment_loss_nonneg
  unfold Phase20.psiPaymentLoss at hp
  unfold residualCoefficient lowerCoefficient
  linarith only [h,hp]

theorem joint_actual_lower :
    lowerCoefficient < JointHMotherPayment.unroundedCoefficient := by
  have h := joint_actual_residual_lower
  have hr := SignedTotalCorrelation.retainedResidual_nonneg
  unfold residualCoefficient at h
  linarith only [h,hr]

def fixedGap : ℝ := JointHMotherPayment.unroundedCoefficient - lowerCoefficient
def residualGap : ℝ := JointHMotherPayment.unroundedCoefficient - residualCoefficient

theorem fixedGap_pos : 0 < fixedGap := sub_pos.mpr joint_actual_lower
theorem residualGap_pos : 0 < residualGap := sub_pos.mpr joint_actual_residual_lower

/-- Each instance spends its own full positive difference Qjoint - L. -/
theorem full_fixed_count : CorrelationPayment.CountBound lowerCoefficient :=
  CorrelationPayment.pay joint_actual_lower

/-- The real logarithmic residual is paid completely, without a half-gain loss. -/
theorem full_residual_count : CorrelationPayment.CountBound residualCoefficient :=
  CorrelationPayment.pay joint_actual_residual_lower

theorem fixed_gain_gt_one_hundredth :
    SignedTotalCorrelation.lowerCoefficient + 1/100 < lowerCoefficient := by
  rw [fixed_improvement_identity]
  linarith only [FifthClassicalShape.gain_gt]

theorem residual_gain_gt_one_hundredth :
    CorrelationPayment.residualCoefficient + 1/100 < residualCoefficient := by
  rw [residual_improvement_identity]
  linarith only [FifthClassicalShape.gain_gt]

theorem joint_improvement_identity :
    lowerCoefficient = JointHMotherPayment.lowerCoefficient +
      SignedTotalCorrelation.correlationGain/4 + FifthClassicalShape.gain/4 := by
  rw [fixed_improvement_identity, SignedTotalCorrelation.fixed_improvement_identity]

theorem joint_gain_gt_nine_four_hundredths :
    JointHMotherPayment.lowerCoefficient + 9/400 < lowerCoefficient := by
  have hc := SignedTotalCorrelation.fixed_gain_gt_one_eightieth
  have hs := fixed_gain_gt_one_hundredth
  linarith only [hc,hs]

end
end Wu2008DoubleSieve.FifthShapePayment
