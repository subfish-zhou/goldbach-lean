import JJointPayment
import Wu08TerminalAlignment

noncomputable section
open Real Wu2008DoubleSieve
open scoped Interval

namespace WuTarget.W12

def weightedDebit : ℝ :=
  2 * Wu08TerminalAlignment.seventhMain +
    Wu08TerminalAlignment.eighthMain + Wu08TerminalAlignment.ninthMain

theorem weightedDebit_eq_J :
    weightedDebit = JFourRemainingMagnitude.actualJ -
      8 * (U8CanonicalMother.L - U8CanonicalMother.I) := by
  unfold weightedDebit Wu08TerminalAlignment.seventhMain
    Wu08TerminalAlignment.eighthMain Wu08TerminalAlignment.ninthMain
    JFourRemainingMagnitude.actualJ
  ring

theorem weightedDebit_original_domains :
    weightedDebit =
      16 * (∫ t in SeventhEighth.sigma..(1/3),
        log ((1-2*t)/t)/(t*(1-t))) +
      8 * (∫ t in SeventhEighth.alpha..(1/3),
        log (2-3*t)/(t*(1-t))) +
      8 * (∫ t in SharpJBalance.b..SharpJBalance.s,
        log ((1-SharpJBalance.s-t)/SharpJBalance.s)/(t*(1-t))) -
      8 * ((∫ t in (100/1327 : ℝ)..(1/10), log (2-3*t)/(t*(1-t))) -
        (9/10 : ℝ) * ∫ t in (100/1327 : ℝ)..(1/10),
          log (2-3*t)/(t*(1-t)^2)) := by
  rw [weightedDebit_eq_J, JFourRemainingMagnitude.original_j_domains,
    U8CanonicalMother.L_literal, U8CanonicalMother.I_literal]

def analyticUpper : ℝ :=
  (3/5) * JJointEnvelope.upperMass +
    (2/5) * JFourRemainingMagnitude.jLowerReal -
    8 * (U8CanonicalMother.L - U8CanonicalMother.I)

def rationalJUpper : ℝ :=
  UnroundedPayments.weightedJUpper -
    SignedTotalCorrelation.jTwo * (SharpLogRecurrence.upperLog 2 -
      (JointLogTotalComparison.V (4/3) + JointLogTotalComparison.V (3/2))) -
    JointJLossStrength.fixedRecovery - 4 * JJointPayment.gain

def rationalUpper : ℝ := rationalJUpper - 4 * U8ActualThreshold.gainLower

theorem weightedDebit_le_analyticUpper : weightedDebit ≤ analyticUpper := by
  rw [weightedDebit_eq_J]
  exact sub_le_sub_right JJointEnvelope.complete_mixture _

theorem mixture_le_rationalJUpper :
    (3/5) * JJointEnvelope.upperMass +
      (2/5) * JFourRemainingMagnitude.jLowerReal ≤ rationalJUpper := by
  have hp : JJointPayment.gain ≤
      (JJointEnvelope.newJLower - JointJLossStrength.fixedRecovery)/4 := by
    rw [JJointEnvelope.gain_packet_identity]
    exact JJointPayment.lower_payment
  have hlog : log 2 ≤
      JointLogTotalComparison.V (4/3) + JointLogTotalComparison.V (3/2) := by
    rw [GlobalSignedActualComparison.log_two]
    exact add_le_add
      (JointLogTotalComparison.log_le_V (by norm_num : (1 : ℝ) ≤ 4/3))
      (JointLogTotalComparison.log_le_V (by norm_num : (1 : ℝ) ≤ 3/2))
  have hj : 0 ≤ SignedTotalCorrelation.jTwo := by
    norm_num [SignedTotalCorrelation.jTwo, SharpJBalance.ninthA,
      SharpJBalance.s, SeventhEighth.sigma, SeventhEighth.alpha]
  have hpay := mul_le_mul_of_nonneg_left hlog hj
  unfold JJointEnvelope.newJLower SignedTotalCorrelation.d2
    SignedTotalCorrelation.e2 at hp
  unfold rationalJUpper
  linarith only [hp, hpay]

theorem weightedJ_le_rationalJUpper :
    16 * SeventhEighth.J7 + 8 * SeventhEighth.J8 + 8 * J9 ≤
      rationalJUpper :=
  JJointEnvelope.complete_mixture.trans mixture_le_rationalJUpper

theorem analyticUpper_le_rationalUpper : analyticUpper ≤ rationalUpper := by
  have hj := mixture_le_rationalJUpper
  have hs := U8ActualThreshold.exact_weight_gain_bounds.1
  unfold analyticUpper rationalUpper
  linarith only [hj, hs]

theorem weightedDebit_le_rationalUpper :
    2 * Wu08TerminalAlignment.seventhMain +
      Wu08TerminalAlignment.eighthMain + Wu08TerminalAlignment.ninthMain ≤
        rationalUpper :=
  weightedDebit_le_analyticUpper.trans analyticUpper_le_rationalUpper

end WuTarget.W12
