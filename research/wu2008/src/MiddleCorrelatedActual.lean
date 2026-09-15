import MiddleCorrelatedRecovery

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open SharpLogRecurrence SharpMassBalance FifthLogTotalMagnitude
open JointLogTotalComparison TotalEndpointComparison GlobalSignedActualComparison
open FifthReciprocalAffineUpper (descent repaid_payment paid_descent)
open SixthExactEnvelopeGap (payment sixth_log_loss_enclosure)
namespace MiddleCorrelatedActual
open MiddleCorrelatedRecovery (delta mass extra)

def upperReal : ℝ :=
  (rationalPart+packet log+FifthActualIntegralRecovery.recurrenceCap+
    payment+1/100000+
    Phase24.newFour-FourMovingLogChord.actualLower-descent (log (b/a))-MiddleInitialFTC.gainReal-(8/3)*delta*mass)/4+retainedExtra

theorem actual_upper_real : JointHMotherPayment.unroundedCoefficient < upperReal := by
  have hw := ExactWeightTripleEnclosure.window_payments
  have hm := MiddleCorrelatedRecovery.middle_upper
  have hb := BaseGSharedActualRecovery.base_exact
  have hbeta := HighSharedKernelMagnitude.beta_bound
  have hg := BaseGSharedActualRecovery.g_exact
  have he := ExactWeightTripleEnclosure.upper_joint_identity
  have ht : JointSharedTightEnclosure.triple ≤ base log+
      ExactWeightTripleEnclosure.upperEnvelope log log-MiddleInitialFTC.gainReal-(8/3)*delta*mass := by
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



def upperRational : ℝ := MiddleInitialActual.upperRational-extra

theorem actual_upper : JointHMotherPayment.unroundedCoefficient < upperRational := by
  have hr := fixedCertificate_exact
  unfold fixedCertificate classicalPayment at hr
  have hp := PsiG18Strength.psi_loss_upper
  have hg := PsiG18Strength.g18_bounds.2
  have hc := repaid_payment
  have hgain := MiddleCorrelatedRecovery.total_gain_lower
  have hu := actual_upper_real
  unfold upperReal at hu
  rw [collection] at hu
  rw [paid_descent] at hc
  unfold upperRational MiddleInitialActual.upperRational FifthReciprocalAffineUpper.upperRational FourMovingLogChord.upperRational SixthExactEnvelopeGap.upperRational FourMovingLogChord.motherGain GlobalLogRelationPayment.upperRational
    BuchstabSeedTightLower.upperRational GlobalLogRelationPayment.logGain
    retainedExtra Phase20.psiPaymentLoss MiddleInitialPayment.gain at *
  linarith only [hr,hp,hg,hc,hu,hgain]

/-- The original full Gamma correction and the small correction are each consumed once. -/
def upperCoefficient : ℝ := GammaFullActual.upperCoefficient-extra

theorem actual_upper_complete : U8CanonicalMother.improvedCoefficient < upperCoefficient := by
  have ho := actual_upper
  have hg := GammaFullUpper.gamma_upper
  have hs := CorrectedCoefficientUpper.small_correction_interval.2
  rw [U8ActualThreshold.actual_identity]
  unfold upperCoefficient GammaFullActual.upperCoefficient upperRational at *
  linarith only [ho,hg,hs]

theorem complete_rational_upper : U8CanonicalMother.improvedCoefficient <
    GammaFullActual.rationalCap-extra := by
  have ha := actual_upper_complete
  have hc := GammaFullActual.upper_below_cap
  unfold upperCoefficient at ha
  linarith only [ha,hc]

theorem rational_margin : 8*lowerLog (5000/4469)-(GammaFullActual.rationalCap-extra) =
    308839142591574662935596839726417631109254764207188733779948921/
    2958155914247895928960861296042192175005877013907727903737600000000 := by
  rw [GammaFullActual.cap_exact,MiddleCorrelatedRecovery.extra_exact]
  norm_num [lowerLog]

theorem cap_below_lowerLog : GammaFullActual.rationalCap-extra < 8*lowerLog (5000/4469) := by
  have h := rational_margin
  linarith only [h]

/-- A strict upper bound for this fixed complete coefficient, not a counting upper bound. -/
theorem actual_below_target : U8CanonicalMother.improvedCoefficient < 8*log (5000/4469) := by
  have ha := complete_rational_upper.trans cap_below_lowerLog
  have hl := log_lower (by norm_num : (1:ℝ) ≤ 5000/4469)
  linarith only [ha,hl]

theorem not_target_below_actual : ¬ 8*log (5000/4469) < U8CanonicalMother.improvedCoefficient :=
  not_lt.mpr actual_below_target.le

end MiddleCorrelatedActual
