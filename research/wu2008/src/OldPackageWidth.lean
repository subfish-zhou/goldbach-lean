import CorrectedCoefficientUpper
import DisjointSlackJoin

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open SharpLogRecurrence JointLogTotalComparison GlobalSignedActualComparison
open FixedCoefficientUpperEnclosure (a b)
namespace OldPackageWidth

/-- Matching endpoints, not estimates for actual unpaid slacks. -/
def shared (f : ℝ → ℝ) : ℝ :=
  (base f+ExactWeightTripleEnclosure.upperEnvelope f f-
    ExactWeightTripleEnclosure.lowerEnvelope f f)/4-BaseSharedSlack.gain

def j (f : ℝ → ℝ) : ℝ :=
  (UnroundedPayments.weightedJUpper-SignedTotalCorrelation.jTwo*
    (upperLog 2-(f (4/3)+f (3/2)))-jLower f-JointJLossStrength.fixedRecovery)/4

def fifth (f : ℝ → ℝ) : ℝ :=
  (2*(FifthLogTotalMagnitude.cap/a)*(f (b/a))^2-
    FifthReciprocalAffineUpper.descent (f (b/a))-
    (2*(FifthLogTotalMagnitude.f0/a)*(f (b/a))^2+
      4*(FifthLogTotalMagnitude.slope/a^2)*(b*(f (b/a))^2-(b-a)*f (b/a)))-
    GlobalLowerSlack.fifthGain)/4

def fifthRec : ℝ := FifthActualIntegralRecovery.recurrenceCap/4
def sixthLog : ℝ := SixthExactEnvelopeGap.payment/4
def sixthRec : ℝ := (1/100000)/4
def four : ℝ := (Phase24.newFour-FourMovingLogChord.actualLower-FourActualCapRecovery.recovery)/4
def retained : ℝ := (328543353599/72210108813375-Phase20.fixedPsi)+354/1000000-
  3/10000-SixthRetainedSlack.gain

def logs : ℝ := (FifthReciprocalAffineUpper.repaid lowerLog V-
  FifthReciprocalAffineUpper.repaid log log+
  lowerCollected log log-GlobalLogRelationPayment.lowerRepaid lowerLog V)/4

def oldLower : ℝ := GlobalLowerSlack.lowerOld+BaseSharedSlack.gain+SixthRetainedSlack.gain

theorem upper_form : FifthReciprocalAffineUpper.upperRational = rationalTotal+
    (packet (fun _ => 0)+FifthReciprocalAffineUpper.repaid lowerLog V-logPayment-
      JointJLossStrength.fixedRecovery+FifthActualIntegralRecovery.recurrenceCap+
      SixthExactEnvelopeGap.payment+1/100000+Phase24.newFour-FourMovingLogChord.actualLower)/4+
    (328543353599/72210108813375-Phase20.fixedPsi)+354/1000000 := by
  rw [FifthReciprocalAffineUpper.paid_descent]
  unfold FifthReciprocalAffineUpper.upperRational FourMovingLogChord.upperRational
    SixthExactEnvelopeGap.upperRational FourMovingLogChord.motherGain
    GlobalLogRelationPayment.upperRational BuchstabSeedTightLower.upperRational
    GlobalLogRelationPayment.logGain
  ring

theorem lower_form : GlobalLogRelationPayment.lowerRational = rationalTotal+
    (lowerPacket (fun _ => 0)+GlobalLogRelationPayment.lowerRepaid lowerLog V-logPayment-
      JointJLossStrength.fixedRecovery)/4+3/10000 := by
  unfold GlobalLogRelationPayment.lowerRational GlobalSignedActualComparison.lowerRational
    GlobalLogRelationPayment.lowerGain
  ring

theorem matching_width_identity : FifthReciprocalAffineUpper.upperRational-oldLower =
    logs+shared log+j log+fifth log+fifthRec+sixthLog+sixthRec+four+retained := by
  rw [upper_form]
  have hc := collection log
  have hl := lower_collection log
  have hr := FifthReciprocalAffineUpper.repaid_log_identity
  unfold oldLower GlobalLowerSlack.lowerOld
  rw [lower_form]
  unfold logs shared j fifth fifthRec sixthLog sixthRec four retained
  rw [hr]
  have he : packet log-lowerPacket log =
      base log+ExactWeightTripleEnclosure.upperEnvelope log log-
      ExactWeightTripleEnclosure.lowerEnvelope log log+
      UnroundedPayments.weightedJUpper-SignedTotalCorrelation.jTwo*
        (upperLog 2-(log (4/3)+log (3/2)))-jLower log-JointJLossStrength.fixedRecovery+
      2*(FifthLogTotalMagnitude.cap/a)*(log (b/a))^2-
      (2*(FifthLogTotalMagnitude.f0/a)*(log (b/a))^2+
        4*(FifthLogTotalMagnitude.slope/a^2)*(b*(log (b/a))^2-(b-a)*log (b/a)))-
      FourActualCapRecovery.recovery := by unfold packet lowerPacket; ring
  linarith only [hc,hl,he]

theorem whole_log_payment_nonnegative : 0 ≤ logs := by
  have hu := FifthReciprocalAffineUpper.repaid_payment
  have hl := GlobalLogRelationPayment.lower_repaid_payment
  rw [← FifthReciprocalAffineUpper.repaid_log_identity] at hu
  unfold logs
  linarith only [hu,hl]

theorem corrected_width_identity : CorrectedCoefficientUpper.upperCoefficient-DisjointSlackJoin.coefficient =
    logs+shared log+j log+fifth log+fifthRec+sixthLog+sixthRec+four+retained+
      CorrectedCoefficientUpper.sixthWidth+CorrectedCoefficientUpper.smallWidth := by
  have h := matching_width_identity
  have hw := CorrectedCoefficientUpper.width_identity
  unfold CorrectedCoefficientUpper.oldWidth oldLower at *
  unfold DisjointSlackJoin.coefficient
  linarith only [h,hw]

end OldPackageWidth
