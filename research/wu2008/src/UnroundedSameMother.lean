import CoupledKernelCount

namespace Wu2008DoubleSieve.Phase20
open Real
noncomputable section

/-- The same mother coefficient in ordinary P2 units, before rational payments. -/
def unroundedCoefficient : ℝ := HighSixDeltaLimit.limitCoefficient/4 + Phase18.g18

/-- Only the existing fixed HighSix window; not a full Psi contribution. -/
def rawPsi : ℝ :=
  firstFunctionalGainPsiOne HighSix.s HighSix.S * HighSix.primeIntegral 0

def fixedPsi : ℝ := 3629895479136046171/11308652260919376406875

/-- Literally the coefficient used in P18's rational ordinary-count endpoint. -/
def paidCoefficient : ℝ := GCurvatureChord.exactQuarter + fixedPsi + Phase18.g18

def classicalPaymentLoss : ℝ :=
  (TruncatedElevenClassicalCountLower.classicalCoefficient-GCurvatureChord.newBalance)/4

def psiPaymentLoss : ℝ := rawPsi-fixedPsi

theorem unrounded_coefficient_identity :
    unroundedCoefficient =
      TruncatedElevenClassicalCountLower.classicalCoefficient/4 + rawPsi + Phase18.g18 := by
  unfold unroundedCoefficient HighSixDeltaLimit.limitCoefficient
    HighSixDeltaLimit.localGainOne rawPsi
  ring

theorem classical_payment_loss_pos : 0 < classicalPaymentLoss :=
  div_pos (sub_pos.mpr GCurvatureChord.complete_coefficient_gt_newBalance) (by norm_num)

theorem psi_payment_loss_nonneg : 0 ≤ psiPaymentLoss :=
  sub_nonneg.mpr HighSixPhase6.exact_local_gain_lower

theorem payment_loss_decomposition :
    unroundedCoefficient-paidCoefficient = classicalPaymentLoss+psiPaymentLoss := by
  rw [unrounded_coefficient_identity]
  unfold paidCoefficient classicalPaymentLoss psiPaymentLoss
  rw [← GCurvatureChord.quarter_eq_exact]
  ring

theorem payment_loss_pos : 0 < unroundedCoefficient-paidCoefficient := by
  rw [payment_loss_decomposition]
  exact add_pos_of_pos_of_nonneg classical_payment_loss_pos psi_payment_loss_nonneg

theorem paid_coefficient_lt_unrounded : paidCoefficient < unroundedCoefficient :=
  sub_pos.mp payment_loss_pos

/-- Supply the actual P18 raw H producer once at the same mother, with epsilon = 4 eta.
Delta is selected before the common arithmetic threshold. No two count bounds are added. -/
theorem unrounded_ordinary_P2_same_threshold (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        ((unroundedCoefficient-η)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ)) ∧
        ((unroundedCoefficient-η)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ)) := by
  obtain ⟨δ,hδ,hδhi,T,hT,h⟩ :=
    Phase10.same_mother_delta_payment Phase18.g18 Phase18.B18 Phase18.B18_pos
      (fun _ ha hb => Phase18.gain18_linear_error ha hb)
      (show 0 < 4*η by positivity)
  refine ⟨δ,hδ,hδhi,T,hT,?_⟩
  intro N hN he
  have hn := h N hN he
  have hp : (unroundedCoefficient-η)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
      ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
    have hid : (unroundedCoefficient-η)*wuSingularSeries N*N/log N^(2 : ℕ) =
        ((HighSixDeltaLimit.limitCoefficient+4*Phase18.g18-4*η)*
          wuSingularSeries N*N/log N^(2 : ℕ))/4 := by
      unfold unroundedCoefficient
      ring
    rw [hid]
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2 (by linarith only [hn])
  exact ⟨hp,hp⟩

end
end Wu2008DoubleSieve.Phase20
