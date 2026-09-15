import SixthReciprocalTightPayment
import GlobalLogRelationPayment

namespace Wu2008DoubleSieve.JointCompliantActualUpper
open Real Set MeasureTheory SharpLogRecurrence JointLogTotalComparison TotalEndpointComparison
open ClassicalLossBottleneck ClassicalAnalyticLeaves SharpMassBalance
open PositiveSixthFTC DynamicSixthEnvelope GlobalSignedActualComparison
open SixthReciprocalTightPayment (payment)
open scoped Interval
noncomputable section

def upperReal : ℝ :=
  (rationalPart+packet log+FifthActualIntegralRecovery.recurrenceCap+
    payment+1/100000+
    Phase24.newFour-BuchstabSeedTightLower.actualLower)/4+retainedExtra

theorem actual_upper_real : JointHMotherPayment.unroundedCoefficient < upperReal := by
  have hw := ExactWeightTripleEnclosure.window_payments
  have hb := BaseGSharedActualRecovery.base_exact
  have hbeta := HighSharedKernelMagnitude.beta_bound
  have hg := BaseGSharedActualRecovery.g_exact
  have he := ExactWeightTripleEnclosure.upper_joint_identity
  have ht : JointSharedTightEnclosure.triple ≤ base log+
      ExactWeightTripleEnclosure.upperEnvelope log log := by
    unfold JointSharedTightEnclosure.triple
    rw [BaseGSharedActualRecovery.shared_exact]
    unfold base BaseGSharedActualRecovery.baseLogRemainder at *
    linarith only [hw.2.1,hw.2.2.2.1,hw.2.2.2.2,hb,hbeta,hg,he]
  have hj := JFourRemainingMagnitude.j_remaining_real_interval.2
  unfold JFourRemainingMagnitude.jRemaining JFourRemainingMagnitude.jCapReal at hj
  rw [j_lower_identity] at hj
  have h5 := FifthLogTotalMagnitude.integral_bounds.2
  have e5 := FifthActualIntegralRecovery.integral_distance.2
  have h6 := SixthReciprocalTightPayment.sixth_log_loss_enclosure.2
  have e6 := ClassicalLossBottleneck.sixth_recurrence_integral_cap.2
  have h4 := BuchstabSeedTightLower.actual_four_lower
  rw [cancelled_actual_identity]
  unfold upperReal packet mainLogs logTotal D AnalyticTotalThreshold.fourLoss
    AnalyticTotalThreshold.fifthEndpoint FifthLogTotalMagnitude.endpoint at *
  rw [← log_div (by norm_num [b,truncatedSixthLowerBeta])
    (by norm_num [a,truncatedSixthLowerAlpha])] at h5
  rw [← log_div (by norm_num [b,truncatedSixthLowerBeta])
    (by norm_num [a,truncatedSixthLowerAlpha])]
  rw [log_two]
  unfold SignedTotalCorrelation.d2 SignedTotalCorrelation.e2 at hj
  rw [log_two] at hj
  linarith only [ht,hj,h5,e5,h6,e6,h4]


/-- Both new producer bounds enter the same original upper packet. -/
def upperRational : ℝ := GlobalLogRelationPayment.upperRational-
  (SixthFullRationalEnclosure.payment-payment)/4

theorem actual_upper : JointHMotherPayment.unroundedCoefficient < upperRational := by
  have hr := fixedCertificate_exact
  unfold fixedCertificate classicalPayment at hr
  have hp := PsiG18Strength.psi_loss_upper
  have hg := PsiG18Strength.g18_bounds.2
  have hc := GlobalLogRelationPayment.repaid_payment
  have hu := actual_upper_real
  unfold upperReal at hu
  rw [collection] at hu
  unfold upperRational GlobalLogRelationPayment.upperRational
    BuchstabSeedTightLower.upperRational GlobalLogRelationPayment.logGain
    retainedExtra Phase20.psiPaymentLoss at *
  linarith only [hr,hp,hg,hc,hu]

def upperRemainder : ℝ := upperRational-8*lowerLog (5000/4469)

theorem remainder_substitution : upperRemainder = GlobalLogRelationPayment.upperRemainder-
    (SixthFullRationalEnclosure.payment-payment)/4 := by
  unfold upperRemainder upperRational GlobalLogRelationPayment.upperRemainder
  ring

theorem upper_bound : upperRational < (904470/1000000:ℝ) := by
  rw [upperRational,GlobalLogRelationPayment.upper_rational_exact,
    SixthFullRationalEnclosure.payment_rational,SixthReciprocalTightPayment.payment_rational]
  norm_num

theorem remainder_bounds : (6285/1000000:ℝ) < upperRemainder ∧
    upperRemainder < 6286/1000000 := by
  rw [remainder_substitution,GlobalLogRelationPayment.upper_remainder_exact,
    SixthFullRationalEnclosure.payment_rational,SixthReciprocalTightPayment.payment_rational]
  norm_num

theorem actual_Q_bounds : (823047/1000000:ℝ) < JointHMotherPayment.unroundedCoefficient ∧
    JointHMotherPayment.unroundedCoefficient < 904470/1000000 :=
  ⟨GlobalLogRelationPayment.improved_actual_Q_bounds.1,actual_upper.trans upper_bound⟩

theorem actual_target_bounds : (-6286/1000000:ℝ) <
    AnalyticTotalThreshold.target-JointHMotherPayment.unroundedCoefficient ∧
    AnalyticTotalThreshold.target-JointHMotherPayment.unroundedCoefficient < 75139/1000000 := by
  have ht := log_lower (by norm_num : (1:ℝ) ≤ 5000/4469)
  have hu := actual_upper
  have hr := remainder_bounds.2
  refine ⟨?_,GlobalLogRelationPayment.improved_actual_target_bounds.2⟩
  unfold upperRemainder AnalyticTotalThreshold.target at *
  linarith only [ht,hu,hr]

/-- No conclusion for the actual target sign follows from these endpoints. -/
theorem rational_endpoints_straddle :
    GlobalLogRelationPayment.lowerRational < 8*lowerLog (5000/4469) ∧
    8*V (5000/4469) < upperRational := by
  refine ⟨GlobalLogRelationPayment.improved_rational_endpoints_straddle.1,?_⟩
  rw [upperRational,GlobalLogRelationPayment.upper_rational_exact,
    SixthFullRationalEnclosure.payment_rational,SixthReciprocalTightPayment.payment_rational]
  norm_num [V,upperLog,lowerLog]

end
end Wu2008DoubleSieve.JointCompliantActualUpper
