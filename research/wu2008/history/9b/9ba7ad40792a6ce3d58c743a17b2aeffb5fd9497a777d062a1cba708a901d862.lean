import WE10FourMajorRoot
import WE05MajorAcceptedTotal

noncomputable section
namespace WuTarget.EveningFourTotal
open Wu2008DoubleSieve Wu08OriginalFourWeights
open FourRoughClosedMass

/-- Use the full proved rational cap; the first E10 rebate was not separately paid. -/
def netGain : ℝ := (W13Tight.pairUpper-E10FourMajor.pairCap)/4

def paidCoefficient : ℝ := EveningJointMainAccepted.paidCoefficient+netGain

def coefficient : ℝ := EveningSixthTotal.coefficient+netGain

theorem no_double_payment : netGain =
    E10Four.netCredit+(E10Four.pairUpper-E10FourMajor.pairCap)/4 := by
  unfold netGain E10Four.netCredit E10Four.pairUpper
  ring

theorem full_cap_improves_display : E10FourMajor.totalCredit < netGain := by
  unfold netGain E10FourMajor.totalCredit E10FourMajor.replacementCap
  linarith only [E10FourMajor.pairCap_lt_target]

/-- Recombine distinct signed slots; do not add two unrelated bounds on one coefficient. -/
theorem joint_pair_payment_le_core :
    W13TightAccepted.paidCoefficient+E09JointMain.netGain+netGain ≤
      W14Accepted.paidCoefficient W04Accepted.enhanced := by
  have hp : W13TightAccepted.paidCoefficient+E09JointMain.netGain+netGain ≤
      W11CreditAccepted.paidCoefficient+E09JointMain.netGain := by
    rw [W13TightAccepted.paid_exact]
    unfold netGain
    linarith only [E10FourMajor.original_pair_upper]
  exact hp.trans E09JointMain.shifted_w11_le_actual_core

theorem raw_paid_lt_actual : E09JointMain.paidCoefficient+netGain <
    W01.ordinaryCoefficient W17Accepted.enhanced := by
  have h := joint_pair_payment_le_core.trans_lt
    (W14Accepted.paid_lt_actual W04Accepted.enhanced)
  unfold E09JointMain.paidCoefficient W17Accepted.paidCoefficient W17Accepted.jointCredit
  linarith only [h]

theorem paid_lt_actual : paidCoefficient < E04Continuous.replacementCoefficient := by
  have hp := raw_paid_lt_actual
  have hc := E04Continuous.certifiedAmount_le_netCredit
  rw [E04Continuous.netCredit_identity] at hc
  unfold paidCoefficient EveningJointMainAccepted.paidCoefficient
  linarith only [hp,hc]

theorem coefficient_le_paid : coefficient ≤ paidCoefficient := by
  have h : EveningSixthTotal.coefficient ≤ EveningJointMainAccepted.paidCoefficient := by
    rw [EveningSixthTotal.coefficient_identity]
    exact EveningJointMainAccepted.scalar_paid_le EveningSixthTotal.base_le_residual
  exact add_le_add_right h netGain

theorem coefficient_lt_actual : coefficient < E04Continuous.replacementCoefficient :=
  coefficient_le_paid.trans_lt paid_lt_actual

theorem netGain_bounds : (41539/1000000 : ℝ) < netGain ∧ netGain < 41540/1000000 := by
  unfold netGain
  rw [W13Tight.pairUpper_exact]
  norm_num [E10FourMajor.pairCap,E10FourMajor.capTerm,Fin.sum_univ_succ,
    E10FourMajor.recipCoeff,E10FourMajor.crossCap,E10FourMajor.slope,E10FourMajor.z0,
    W13Tight.momentUpper,W13Tight.discount,W13Tight.primitive,
    W13.h,W13.d,W13.k,W13.cut,FourLogAffine.u,
    SharpLogRecurrence.upperLog,SharpLogRecurrence.lowerLog,
    alpha,beta,lam,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerLambda]

theorem coefficient_bounds : (847774/1000000 : ℝ) < coefficient ∧
    coefficient < 847779/1000000 := by
  unfold coefficient
  constructor <;> linarith only [EveningSixthTotal.coefficient_bounds.1,
    EveningSixthTotal.coefficient_bounds.2,netGain_bounds.1,netGain_bounds.2]

theorem certificate_gap_bounds :
    (50421/1000000 : ℝ) < 4491/5000-coefficient ∧
      4491/5000-coefficient < 50426/1000000 := by
  constructor <;> linarith only [coefficient_bounds.1,coefficient_bounds.2]

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
    (847774/1000000 : ℝ)*U8CanonicalMother.M N ≤
      ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
        ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨T,hT,hc⟩ := ordinary_P2
  refine ⟨T,hT,?_⟩
  intro N hN he
  have hM : 0 ≤ U8CanonicalMother.M N :=
    (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  exact (mul_le_mul_of_nonneg_right coefficient_bounds.1.le hM).trans (hc N hN he)

end WuTarget.EveningFourTotal
