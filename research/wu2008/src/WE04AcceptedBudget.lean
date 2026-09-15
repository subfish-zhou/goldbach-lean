import WE04ContinuousRoot
import WE02RankOneAcceptedBudget

noncomputable section
namespace WuTarget.EveningContinuousAccepted
open Wu2008DoubleSieve

abbrev tableGain : ℝ := EveningRankOneAccepted.tableGain
abbrev otherRemaining : ℝ := EveningRankOneAccepted.otherRemaining

def certifiedCredits : ℝ :=
  EveningRankOneAccepted.certifiedCredits + E04Continuous.certifiedAmount

theorem scalar_paid_le {b : ℝ} (hb : b ≤ otherRemaining) :
    b+tableGain+certifiedCredits-122417/800000 ≤
      E04Continuous.replacementPaidCoefficient := by
  have h := EveningRankOneAccepted.scalar_paid_le hb
  unfold certifiedCredits E04Continuous.replacementPaidCoefficient
  change b+EveningRankOneAccepted.tableGain+
    (EveningRankOneAccepted.certifiedCredits+E04Continuous.certifiedAmount)-122417/800000 ≤ _
  linarith only [h]

theorem ordinary_P2 {b ε dmax : ℝ} (hb : b ≤ otherRemaining)
    (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (b+tableGain+certifiedCredits-122417/800000-ε)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨δ,hd,hm,hs,T,hT,hc⟩ := E04Continuous.replacement_paid_ordinary_P2 hε hdmax
  refine ⟨δ,hd,hm,hs,T,hT,?_⟩
  intro N hN he
  have hM : 0 ≤ U8CanonicalMother.M N :=
    (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right (scalar_paid_le hb) ε) hM).trans
    (hc N hN he)

theorem refined_target {b : ℝ} (hb : b ≤ otherRemaining)
    (h : (840977/800000 : ℝ) ≤ b+tableGain+certifiedCredits) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      RefinedExit.margin/2*U8CanonicalMother.M N ≤
        ((Wu2004MeanValue.refinedGood N (9469/5000)).card : ℝ) ∧
      ∃ p r q : ℕ, p.Prime ∧ (r=1 ∨ r.Prime) ∧ q.Prime ∧
        N=p+r*q ∧ (r : ℝ) ≤ (q : ℝ)^(4469/5000 : ℝ) := by
  apply E04Continuous.replacement_refined_target
  have hp := scalar_paid_le hb
  unfold E04Continuous.replacementPaidCoefficient at hp
  linarith only [h, hp]

end WuTarget.EveningContinuousAccepted
