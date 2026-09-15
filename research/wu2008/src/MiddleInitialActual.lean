import MiddleInitialPayment

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open SharpLogRecurrence SharpMassBalance FifthLogTotalMagnitude
open JointLogTotalComparison TotalEndpointComparison GlobalSignedActualComparison
open FifthReciprocalAffineUpper (descent repaid_payment paid_descent)
open SixthExactEnvelopeGap (payment sixth_log_loss_enclosure)
namespace MiddleInitialActual

def upperReal : ℝ :=
  (rationalPart+packet log+FifthActualIntegralRecovery.recurrenceCap+
    payment+1/100000+
    Phase24.newFour-FourMovingLogChord.actualLower-descent (log (b/a))-MiddleInitialFTC.gainReal)/4+retainedExtra

theorem actual_upper_real : JointHMotherPayment.unroundedCoefficient < upperReal := by
  have hw := ExactWeightTripleEnclosure.window_payments
  have hm := MiddleInitialFTC.middle_upper
  have hb := BaseGSharedActualRecovery.base_exact
  have hbeta := HighSharedKernelMagnitude.beta_bound
  have hg := BaseGSharedActualRecovery.g_exact
  have he := ExactWeightTripleEnclosure.upper_joint_identity
  have ht : JointSharedTightEnclosure.triple ≤ base log+
      ExactWeightTripleEnclosure.upperEnvelope log log-MiddleInitialFTC.gainReal := by
    unfold JointSharedTightEnclosure.triple
    rw [BaseGSharedActualRecovery.shared_exact]
    unfold base BaseGSharedActualRecovery.baseLogRemainder at *
    linarith only [hw.2.1,hm,hw.2.2.2.2,hb,hbeta,hg,he]
  have hj := JFourRemainingMagnitude.j_remaining_real_interval.2
  unfold JFourRemainingMagnitude.jRemaining JFourRemainingMagnitude.jCapReal at hj
  rw [j_lower_identity] at hj
  have h5 := FifthReciprocalAffineUpper.integral_upper
  have e5 := FifthActualIntegralRecovery.integral_distance.2
  have h6 := sixth_log_loss_enclosure.2
  have e6 := ClassicalLossBottleneck.sixth_recurrence_integral_cap.2
  have h4 := FourMovingLogChord.actual_four_lower
  rw [cancelled_actual_identity]
  unfold upperReal packet mainLogs logTotal D AnalyticTotalThreshold.fourLoss
    AnalyticTotalThreshold.fifthEndpoint FifthLogTotalMagnitude.endpoint descent at *
  rw [← log_div (by norm_num [b,truncatedSixthLowerBeta])
    (by norm_num [a,truncatedSixthLowerAlpha])] at h5
  rw [← log_div (by norm_num [b,truncatedSixthLowerBeta])
    (by norm_num [a,truncatedSixthLowerAlpha])]
  rw [log_two]
  unfold SignedTotalCorrelation.d2 SignedTotalCorrelation.e2 at hj
  rw [log_two] at hj
  linarith only [ht,hj,h5,e5,h6,e6,h4]



def upperRational : ℝ := FifthReciprocalAffineUpper.upperRational-MiddleInitialPayment.gain/4

theorem actual_upper : JointHMotherPayment.unroundedCoefficient < upperRational := by
  have hr := fixedCertificate_exact
  unfold fixedCertificate classicalPayment at hr
  have hp := PsiG18Strength.psi_loss_upper
  have hg := PsiG18Strength.g18_bounds.2
  have hc := repaid_payment
  have hgain := MiddleInitialPayment.payment.1
  have hu := actual_upper_real
  unfold upperReal at hu
  rw [collection] at hu
  rw [paid_descent] at hc
  unfold upperRational FifthReciprocalAffineUpper.upperRational FourMovingLogChord.upperRational SixthExactEnvelopeGap.upperRational FourMovingLogChord.motherGain GlobalLogRelationPayment.upperRational
    BuchstabSeedTightLower.upperRational GlobalLogRelationPayment.logGain
    retainedExtra Phase20.psiPaymentLoss MiddleInitialPayment.gain at *
  linarith only [hr,hp,hg,hc,hu,hgain]

theorem old_upper_bounds : (892228/1000000:ℝ) < upperRational ∧
    upperRational < 892230/1000000 := by
  have ho := FifthReciprocalAffineUpper.upper_bounds
  have hg := MiddleInitialPayment.gain_bounds
  unfold upperRational
  constructor <;> linarith only [ho.1,ho.2,hg.1,hg.2]

/-- Gamma6 and the original small correction are each added once. -/
def upperCoefficient : ℝ := upperRational+
  (CorrectedCoefficientUpper.gammaUpper-47/481250)/4+U8ActualThreshold.gainUpper

theorem corrected_actual_upper : U8CanonicalMother.improvedCoefficient < upperCoefficient := by
  have ho := actual_upper
  have hs := CorrectedCoefficientUpper.sixth_correction_interval.2
  have hg := CorrectedCoefficientUpper.small_correction_interval.2
  rw [U8ActualThreshold.actual_identity]
  unfold upperCoefficient
  linarith only [ho,hs,hg]

theorem matching_upper_identity : upperCoefficient =
    CorrectedCoefficientUpper.upperCoefficient-MiddleInitialPayment.gain/4 := by
  unfold upperCoefficient upperRational CorrectedCoefficientUpper.upperCoefficient
  ring

theorem total_descent : (5874/1000000:ℝ) <
    CorrectedCoefficientUpper.upperCoefficient-upperCoefficient ∧
    CorrectedCoefficientUpper.upperCoefficient-upperCoefficient < 5875/1000000 := by
  rw [matching_upper_identity]
  constructor <;> linarith only [MiddleInitialPayment.gain_bounds.1,MiddleInitialPayment.gain_bounds.2]

theorem upper_coefficient_bounds : (905735/1000000:ℝ) < upperCoefficient ∧
    upperCoefficient < 905738/1000000 := by
  have ho := CorrectedCoefficientUpper.upper_coefficient_bounds
  have hg := MiddleInitialPayment.gain_bounds
  rw [matching_upper_identity]
  constructor <;> linarith only [ho.1,ho.2,hg.1,hg.2]

theorem actual_corridor : (834331/1000000:ℝ) < U8CanonicalMother.improvedCoefficient ∧
    U8CanonicalMother.improvedCoefficient < 905738/1000000 :=
  ⟨JJointPayment.rational_corridor.1,corrected_actual_upper.trans upper_coefficient_bounds.2⟩

theorem old_actual_below_target : JointHMotherPayment.unroundedCoefficient < 8*log (5000/4469) := by
  have ht := log_lower (by norm_num : (1:ℝ) ≤ 5000/4469)
  have hp : (892230/1000000:ℝ) < 8*lowerLog (5000/4469) := by norm_num [lowerLog]
  linarith only [actual_upper,old_upper_bounds.2,ht,hp]

/-- The new complete upper still exceeds the target. This is not the actual sign. -/
theorem certificate_above_target : 8*log (5000/4469) < upperCoefficient := by
  have ht := log_le_V (by norm_num : (1:ℝ) ≤ 5000/4469)
  have hp : 8*V (5000/4469) < (905735/1000000:ℝ) := by norm_num [V,lowerLog,upperLog]
  linarith only [ht,hp,upper_coefficient_bounds.1]

theorem target_inside_corridor : JJointPayment.coefficient < 8*log (5000/4469) ∧
    8*log (5000/4469) < upperCoefficient :=
  ⟨JJointPayment.certificate_below_target,certificate_above_target⟩

/-- The exact unresolved deficit for the same literal corrected coefficient. -/
theorem target_iff_deficit : 8*log (5000/4469) < U8CanonicalMother.improvedCoefficient ↔
    upperCoefficient-U8CanonicalMother.improvedCoefficient < upperCoefficient-8*log (5000/4469) := by
  constructor <;> intro h <;> linarith only [h]

end MiddleInitialActual
