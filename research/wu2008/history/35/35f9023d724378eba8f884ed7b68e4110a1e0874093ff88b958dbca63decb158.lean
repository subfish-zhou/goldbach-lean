import WE09JointMainRoot
import WE04AcceptedBudget

noncomputable section
namespace WuTarget.EveningJointMainAccepted
open Wu2008DoubleSieve

abbrev tableGain : ℝ := EveningContinuousAccepted.tableGain
abbrev otherRemaining : ℝ := EveningContinuousAccepted.otherRemaining

def certifiedCredits : ℝ :=
  EveningContinuousAccepted.certifiedCredits + E09JointMain.netGain

def paidCoefficient : ℝ :=
  E09JointMain.paidCoefficient + E04Continuous.certifiedAmount

/-- Combine a newly proved classical-block payment with the separate profile gain. -/
theorem paid_lt_actual : paidCoefficient < E04Continuous.replacementCoefficient := by
  have hp := E09JointMain.paid_lt_actual
  have hc := E04Continuous.certifiedAmount_le_netCredit
  rw [E04Continuous.netCredit_identity] at hc
  unfold paidCoefficient
  linarith only [hp, hc]

theorem scalar_paid_le {b : ℝ} (hb : b ≤ otherRemaining) :
    b+tableGain+certifiedCredits-122417/800000 ≤ paidCoefficient := by
  have h := EveningContinuousAccepted.scalar_paid_le hb
  unfold E04Continuous.replacementPaidCoefficient at h
  unfold certifiedCredits paidCoefficient E09JointMain.paidCoefficient
  change b+EveningContinuousAccepted.tableGain+
    (EveningContinuousAccepted.certifiedCredits+E09JointMain.netGain)-122417/800000 ≤ _
  linarith only [h]

theorem ordinary_P2 {b ε dmax : ℝ} (hb : b ≤ otherRemaining)
    (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (b+tableGain+certifiedCredits-122417/800000-ε)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨δ,hd,hm,hs,_,_,T,hT,hc⟩ :=
    E04Continuous.enhanced_continuous_ordinary_P2 hε hdmax
  refine ⟨δ,hd,hm,hs,T,hT,?_⟩
  intro N hN he
  have hM : 0 ≤ U8CanonicalMother.M N :=
    (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  exact (mul_le_mul_of_nonneg_right
    (sub_le_sub_right ((scalar_paid_le hb).trans paid_lt_actual.le) ε) hM).trans
      (hc N hN he)

theorem refined_target {b : ℝ} (hb : b ≤ otherRemaining)
    (h : (840977/800000 : ℝ) ≤ b+tableGain+certifiedCredits) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      RefinedExit.margin/2*U8CanonicalMother.M N ≤
        ((Wu2004MeanValue.refinedGood N (9469/5000)).card : ℝ) ∧
      ∃ p r q : ℕ, p.Prime ∧ (r=1 ∨ r.Prime) ∧ q.Prime ∧
        N=p+r*q ∧ (r : ℝ) ≤ (q : ℝ)^(4469/5000 : ℝ) := by
  have hc : (4491/5000 : ℝ) ≤ b+tableGain+certifiedCredits-122417/800000 := by
    linarith only [h]
  apply RefinedExit.from_actual_count hc
  intro ε hε
  obtain ⟨_,_,_,_,T,hT,hcount⟩ := ordinary_P2 hb hε (by norm_num : (0 : ℝ) < 1)
  exact ⟨T,hT,hcount⟩

end WuTarget.EveningJointMainAccepted
