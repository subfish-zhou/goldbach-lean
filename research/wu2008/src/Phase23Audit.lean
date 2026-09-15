import SharedClassicalLower
import UnroundedSameMother

namespace Wu2008DoubleSieve.Phase23
open Real
noncomputable section

/-- Literal signed expression: every original positive and negative term is retained. -/
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

theorem lower_coefficient_identity :
    lowerCoefficient = Phase20.paidCoefficient+deltaK/4 := by
  unfold lowerCoefficient Phase20.paidCoefficient
  rw [← GCurvatureChord.quarter_eq_exact,improvement_identity]
  ring

/-- Arbitrary positive loss is paid to the actual same-mother producer, then weakened.
The delta is chosen before the one common threshold for ALL even N. -/
theorem ordinary_P2_lower_family (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        ((lowerCoefficient-η)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ)) ∧
        ((lowerCoefficient-η)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ)) := by
  obtain ⟨δ,hδ,hδhi,T,hT,h⟩ := Phase20.unrounded_ordinary_P2_same_threshold η hη
  refine ⟨δ,hδ,hδhi,T,hT,?_⟩
  intro N hN he
  have hs := (HighSixPhase6.original_scale_positive (show 512 ≤ N by omega)).le
  have hb := mul_le_mul_of_nonneg_right
    (sub_le_sub_right lower_coefficient_lt_actual.le η) hs
  have hb' : (lowerCoefficient-η)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
      (Phase20.unroundedCoefficient-η)*wuSingularSeries N*N/log N^(2 : ℕ) := by
    calc
      _ = (lowerCoefficient-η)*(wuSingularSeries N*N/log N^(2 : ℕ)) := by ring
      _ ≤ (Phase20.unroundedCoefficient-η)*(wuSingularSeries N*N/log N^(2 : ℕ)) := hb
      _ = _ := by ring
  exact ⟨hb'.trans (h N hN he).1,hb'.trans (h N hN he).2⟩

def paidGain : ℝ := deltaK/8

theorem paidGain_pos : 0 < paidGain := div_pos deltaK_pos (by norm_num)

theorem payment_identity : lowerCoefficient-paidGain = Phase20.paidCoefficient+paidGain := by
  rw [lower_coefficient_identity]
  unfold paidGain
  ring

/-- Concrete nonzero half-gain payment, actually supplied to P20, not an unspent coefficient. -/
theorem improved_ordinary_P2_same_threshold :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        ((Phase20.paidCoefficient+paidGain)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ)) ∧
        ((Phase20.paidCoefficient+paidGain)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ)) := by
  simpa only [payment_identity] using ordinary_P2_lower_family paidGain paidGain_pos

theorem paid_strictly_improved : Phase20.paidCoefficient < Phase20.paidCoefficient+paidGain := by
  linarith only [paidGain_pos]

end
end Wu2008DoubleSieve.Phase23
