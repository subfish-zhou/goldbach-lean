import WE05SixthMajorRoot
import WE08AcceptedTotal

noncomputable section
namespace WuTarget.EveningSixthTotal
open Wu2008DoubleSieve
open Wu2008DoubleSieve.SharpMassBalance

/-- Both E05 rounds replace the old sixth bound; neither was paid before this module. -/
def netGain : ℝ := E05Sixth.ordinaryCredit + E05SixthMajor.netOrdinaryCredit

def base : ℝ := EveningDebitTotal.base + netGain

def coefficient : ℝ := EveningDebitTotal.coefficient + netGain

theorem net_gain_identity : netGain =
    (E05SixthMajor.majorLower-E01Baseline.sixthLower)/4 := by
  unfold netGain
  rw [E05Sixth.ordinaryCredit_eq]
  unfold E05SixthMajor.netOrdinaryCredit E05SixthMajor.majorLower E05Sixth.sixthLower
  rw [E01Baseline.sixth_exact]
  ring

theorem base_le_residual : base ≤ EveningJointMainAccepted.otherRemaining := by
  have hd := E08Debit.certifiedSlack_le_debitSlack
  rw [E08Debit.certifiedSlack_identity] at hd
  unfold E08Debit.oldSlack at hd
  rw [E01Baseline.debit_exact] at hd
  rw [EveningTotal.residual_exact, E01Baseline.payment_exact, E01Baseline.four_exact]
  unfold base EveningDebitTotal.base EveningTotal.base
  linarith only [E05SixthMajor.majorLower_le_actual, net_gain_identity, hd]

theorem coefficient_identity : coefficient =
    base+EveningJointMainAccepted.tableGain+EveningTotal.credits-122417/800000 := by
  unfold coefficient base
  rw [EveningDebitTotal.coefficient_identity]
  ring

theorem coefficient_lt_actual : coefficient < E04Continuous.replacementCoefficient := by
  rw [coefficient_identity]
  exact (EveningJointMainAccepted.scalar_paid_le base_le_residual).trans_lt
    EveningJointMainAccepted.paid_lt_actual

theorem netGain_bounds : (9273/1000000 : ℝ) < netGain ∧ netGain < 9274/1000000 := by
  norm_num [netGain,E05Sixth.ordinaryCredit,E05SixthMajor.netOrdinaryCredit,
    E05SixthMajor.newCredit,E05SixthMajor.innerCredit,E05SixthMajor.innerRate,
    E05SixthMajor.innerDenom1,E05SixthMajor.innerDenom2,
    E05SixthMajor.fifthExtraCredit,E05SixthMajor.seventhCredit,
    E05SixthMajor.outerCredit,E05Sixth.denominatorCap,E05Sixth.fifthLogTerm,
    E05SixthMajor.z0,Phase25.kx,a,b,lam,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

theorem coefficient_bounds : (806235/1000000 : ℝ) < coefficient ∧
    coefficient < 806239/1000000 := by
  unfold coefficient
  constructor <;> linarith only [EveningDebitTotal.coefficient_bounds.1,
    EveningDebitTotal.coefficient_bounds.2, netGain_bounds.1, netGain_bounds.2]

theorem certificate_gap_bounds :
    (91961/1000000 : ℝ) < 4491/5000-coefficient ∧
      4491/5000-coefficient < 91965/1000000 := by
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
    (806235/1000000 : ℝ)*U8CanonicalMother.M N ≤
      ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
        ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨T,hT,hc⟩ := ordinary_P2
  refine ⟨T,hT,?_⟩
  intro N hN he
  have hM : 0 ≤ U8CanonicalMother.M N :=
    (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  exact (mul_le_mul_of_nonneg_right coefficient_bounds.1.le hM).trans (hc N hN he)

end WuTarget.EveningSixthTotal
