import WE01BaselineRoot
import WE09AcceptedBudget

noncomputable section
namespace WuTarget.EveningTotal
open Wu2008DoubleSieve
open scoped BigOperators

def base : ℝ := E01Baseline.sixthLower/4 + E01Baseline.debitLower +
  E01Baseline.paymentLower + E01Baseline.fourLower

abbrev credits : ℝ := EveningJointMainAccepted.certifiedCredits

def coefficient : ℝ := E01Baseline.exactPaid + credits

theorem residual_exact : EveningJointMainAccepted.otherRemaining =
    Wu08TerminalAlignment.sixthMain/4 + W12Accepted.debitSlack +
      W11CreditAccepted.paymentSlack + W13TightAccepted.fourSlack := by
  unfold EveningJointMainAccepted.otherRemaining EveningContinuousAccepted.otherRemaining
    EveningRankOneAccepted.otherRemaining EveningSecondAccepted.otherRemaining
    EveningAccepted.otherRemaining W17Accepted.remainingCoefficient
    W13TightAccepted.remainingCoefficient W14Accepted.retainedSlack E07Accepted.fifthBalance
  ring

theorem base_lt_residual : base < EveningJointMainAccepted.otherRemaining := by
  rw [residual_exact, E01Baseline.payment_exact, E01Baseline.four_exact]
  unfold base
  linarith only [E01Baseline.sixth_lower, E01Baseline.debit_strict]

theorem table_exact : EveningJointMainAccepted.tableGain = E01Baseline.gammaLower/4 := by
  change (∑ j : Fin 21, W03.paidWeights j * (W02.lowerVector j : ℝ))/4 = _
  rw [E01Baseline.gamma_exact]

theorem coefficient_exact : coefficient =
    base+EveningJointMainAccepted.tableGain+credits-122417/800000 := by
  unfold coefficient E01Baseline.exactPaid
  rw [← E01Baseline.total_exact, table_exact]
  unfold base
  ring

theorem credits_exact : credits =
    (24859/250000000 : ℝ) + 87760644803325371/14970763715034960000000 +
      3/36517 + 91/500000 + 8039587/22000000000000 + 5000/15848361 := by
  unfold credits EveningJointMainAccepted.certifiedCredits
    EveningContinuousAccepted.certifiedCredits EveningRankOneAccepted.certifiedCredits
    E03Sigma.ordinaryCredit E07Fifth.netCredit E02JointCredit.rankOneAmount
    E04Continuous.certifiedAmount
  rw [E09JointMain.netGain_exact]

theorem coefficient_bounds : (796528/1000000 : ℝ) < coefficient ∧
    coefficient < 796530/1000000 := by
  unfold coefficient
  rw [credits_exact]
  constructor <;> linarith only [E01Baseline.paid_rational_bounds.1,
    E01Baseline.paid_rational_bounds.2]

theorem certificate_gap_bounds :
    (101670/1000000 : ℝ) < 4491/5000-coefficient ∧
      4491/5000-coefficient < 101672/1000000 := by
  constructor <;> linarith only [coefficient_bounds.1, coefficient_bounds.2]

theorem ordinary_P2 : ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
    coefficient*U8CanonicalMother.M N ≤
      ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
        ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨_,_,_,_,T,hT,hc⟩ := EveningJointMainAccepted.ordinary_P2
    (b := EveningJointMainAccepted.otherRemaining) le_rfl
    (sub_pos.mpr base_lt_residual) (by norm_num : (0 : ℝ) < 1)
  refine ⟨T,hT,?_⟩
  intro N hN he
  have heq : EveningJointMainAccepted.otherRemaining + EveningJointMainAccepted.tableGain +
      EveningJointMainAccepted.certifiedCredits-122417/800000-
      (EveningJointMainAccepted.otherRemaining-base) = coefficient := by
    rw [coefficient_exact]
    dsimp only [credits]
    ring
  simpa only [heq] using hc N hN he

theorem ordinary_P2_display : ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
    (796528/1000000 : ℝ)*U8CanonicalMother.M N ≤
      ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
        ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨T,hT,hc⟩ := ordinary_P2
  refine ⟨T,hT,?_⟩
  intro N hN he
  have hM : 0 ≤ U8CanonicalMother.M N :=
    (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  exact (mul_le_mul_of_nonneg_right coefficient_bounds.1.le hM).trans (hc N hN he)

end WuTarget.EveningTotal
