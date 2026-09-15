import WE08DebitRoot
import WE01CurrentTotal

noncomputable section
namespace WuTarget.EveningDebitTotal
open Wu2008DoubleSieve

/-- Replace the former rational debit bound, not the full symbolic debit slack. -/
def base : ℝ := EveningTotal.base + E08Debit.netGain

def coefficient : ℝ := EveningTotal.coefficient + E08Debit.netGain

theorem base_le_residual : base ≤ EveningJointMainAccepted.otherRemaining := by
  have hd := E08Debit.certifiedSlack_le_debitSlack
  rw [E08Debit.certifiedSlack_identity] at hd
  unfold E08Debit.oldSlack at hd
  rw [E01Baseline.debit_exact] at hd
  rw [EveningTotal.residual_exact, E01Baseline.payment_exact, E01Baseline.four_exact]
  unfold base EveningTotal.base
  linarith only [E01Baseline.sixth_lower, hd]

theorem coefficient_identity : coefficient =
    base+EveningJointMainAccepted.tableGain+EveningTotal.credits-122417/800000 := by
  unfold coefficient base
  rw [EveningTotal.coefficient_exact]
  ring

theorem coefficient_lt_actual : coefficient < E04Continuous.replacementCoefficient := by
  rw [coefficient_identity]
  exact (EveningJointMainAccepted.scalar_paid_le base_le_residual).trans_lt
    EveningJointMainAccepted.paid_lt_actual

theorem net_upper : E08Debit.netGain < (435/1000000 : ℝ) := by
  unfold E08Debit.netGain
  rw [W12.paymentEndpoint_exact, E08Debit.tightenedCap_exact]
  norm_num

theorem coefficient_bounds : (796962/1000000 : ℝ) < coefficient ∧
    coefficient < 796965/1000000 := by
  unfold coefficient
  constructor <;> linarith only [EveningTotal.coefficient_bounds.1,
    EveningTotal.coefficient_bounds.2, E08Debit.netGain_gt, net_upper]

theorem certificate_gap_bounds :
    (101235/1000000 : ℝ) < 4491/5000-coefficient ∧
      4491/5000-coefficient < 101238/1000000 := by
  constructor <;> linarith only [coefficient_bounds.1, coefficient_bounds.2]

theorem ordinary_P2 : ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
    coefficient*U8CanonicalMother.M N ≤
      ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
        ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨_,_,_,_,_,_,T,hT,hc⟩ := E04Continuous.enhanced_continuous_ordinary_P2
    (sub_pos.mpr coefficient_lt_actual) (by norm_num : (0 : ℝ) < 1)
  refine ⟨T,hT,?_⟩
  intro N hN he
  have heq : E04Continuous.replacementCoefficient -
      (E04Continuous.replacementCoefficient-coefficient) = coefficient := by ring
  simpa only [heq] using hc N hN he

theorem ordinary_P2_display : ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
    (796962/1000000 : ℝ)*U8CanonicalMother.M N ≤
      ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
        ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨T,hT,hc⟩ := ordinary_P2
  refine ⟨T,hT,?_⟩
  intro N hN he
  have hM : 0 ≤ U8CanonicalMother.M N :=
    (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  exact (mul_le_mul_of_nonneg_right coefficient_bounds.1.le hM).trans (hc N hN he)

end WuTarget.EveningDebitTotal
