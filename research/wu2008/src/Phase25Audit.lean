import ExactSixthOuter
import Phase24Audit

namespace Wu2008DoubleSieve.Phase25
open Real
noncomputable section

/-- All raw signed producers are reassembled; no whole lower plus gain proof. -/
def kLower : ℝ := Phase23.modelBase+UnroundedPayments.fifthRational+newSixth+
  47/481250-GConvexChord.rationalG-UnroundedPayments.weightedJUpper-Phase24.newFour

theorem complete_lower : kLower < TruncatedElevenClassicalCountLower.classicalCoefficient := by
  have hb := Phase23.model_base_lower
  have hg := Phase23.shared_actual_lower
  have hm := Phase23.gModel_upper
  have hj := UnroundedPayments.original_weightedJ_le
  have hi := Phase24.original_four_upper
  have hp := UnroundedPayments.fifthRational_lt_fifthPairFlin
  have hq := actual_sixth_ge_new
  unfold TruncatedElevenClassicalCountLower.classicalCoefficient kLower
  linarith

def delta6 : ℝ := newSixth-(RationalMovingSixth.rationalSixth+
  SixthReciprocalCorrection.deltaSixth+SixthLogCubicCorrection.deltaLog)

theorem delta6_pos : 0 < delta6 := sub_pos.mpr strict_sixth_improvement

def D : ℝ := Phase23.deltaK+Phase24.deltaI+delta6

theorem D_pos : 0 < D := add_pos (add_pos Phase23.deltaK_pos Phase24.deltaI_pos) delta6_pos

theorem classical_identity : kLower = Phase24.kLower+delta6 := by
  unfold kLower Phase24.kLower delta6
  ring

theorem improvement_identity : kLower = GCurvatureChord.newBalance+D := by
  rw [classical_identity,Phase24.improvement_identity]
  unfold D Phase24.D
  ring

theorem classical_strict_improvement : Phase24.kLower < kLower := by
  rw [classical_identity]
  linarith only [delta6_pos]

theorem literal_complete_lower : kLower <
    24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha))+
      8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta))+fifthPairFlin+
      truncatedSixthLowerF6lin+47/481250-
      SingleUpperClassicalLimit.Glin (1/3)-
      SingleUpperClassicalLimit.Glin truncatedSixthLowerSigma-8*J9-
      16*SeventhEighth.J7-8*SeventhEighth.J8-
      8*FourRoughClosedMass.I10-8*FourRoughClosedMass.I11 := complete_lower

def lowerCoefficient : ℝ := kLower/4+Phase20.fixedPsi+Phase18.g18

theorem lower_coefficient_lt_actual : lowerCoefficient < Phase20.unroundedCoefficient := by
  rw [Phase20.unrounded_coefficient_identity]
  have hp := Phase20.psi_payment_loss_nonneg
  unfold Phase20.psiPaymentLoss at hp
  unfold lowerCoefficient
  linarith only [complete_lower,hp]

theorem lower_coefficient_identity : lowerCoefficient = Phase20.paidCoefficient+D/4 := by
  unfold lowerCoefficient Phase20.paidCoefficient
  rw [← GCurvatureChord.quarter_eq_exact,improvement_identity]
  ring

theorem full_fixed_improvement : Phase24.lowerCoefficient < lowerCoefficient := by
  unfold lowerCoefficient Phase24.lowerCoefficient
  linarith only [classical_strict_improvement]

/-- Positive actual slack, not zero loss, and not a new superior Q-family. -/
def paymentEta : ℝ := Phase20.unroundedCoefficient-lowerCoefficient

theorem paymentEta_pos : 0 < paymentEta := sub_pos.mpr lower_coefficient_lt_actual

theorem payment_identity : Phase20.unroundedCoefficient-paymentEta = lowerCoefficient := by
  unfold paymentEta
  ring

/-- Consumes the genuine P20 producer at eta=Q-L25, paying the FULL fixed coefficient.
The same delta precedes a single threshold and both literal unrestricted ordinary P2 counts. -/
theorem full_ordinary_P2_same_threshold :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (lowerCoefficient*wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ)) ∧
        (lowerCoefficient*wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ)) := by
  simpa only [payment_identity] using
    Phase20.unrounded_ordinary_P2_same_threshold paymentEta paymentEta_pos

end
end Wu2008DoubleSieve.Phase25
