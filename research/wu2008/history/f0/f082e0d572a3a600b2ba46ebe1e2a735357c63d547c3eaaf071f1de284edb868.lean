import WE02JointCreditRankOneRoot
import WE06AcceptedBudget

noncomputable section
namespace WuTarget.EveningRankOneAccepted
open Wu2008DoubleSieve

abbrev tableGain : ℝ := EveningSecondAccepted.tableGain
abbrev otherRemaining : ℝ := EveningSecondAccepted.otherRemaining

def certifiedCredits : ℝ :=
  E03Sigma.ordinaryCredit + E07Fifth.netCredit + 3/36517 + E02JointCredit.rankOneAmount

theorem upgrade_identity : certifiedCredits =
    EveningSecondAccepted.certifiedCredits + E02JointCredit.rankOneUpgrade := by
  unfold certifiedCredits EveningSecondAccepted.certifiedCredits
    EveningAccepted.certifiedCredits E02JointCredit.rankOneUpgrade
  ring

theorem remaining_lower {b : ℝ} (hb : b ≤ otherRemaining) :
    b+tableGain+certifiedCredits ≤ W17Accepted.remainingCoefficient := by
  have hs := E03Sigma.table_weighted_plus_credit
  have hf := E07Accepted.fifth_paid
  have hc := E06Second.second_slack_lower
  have hj := E02JointCredit.rankOneAmount_le_jointCredit
  change tableGain+E03Sigma.ordinaryCredit ≤ W02Accepted.nodeGain/4 at hs
  unfold otherRemaining EveningSecondAccepted.otherRemaining
    EveningAccepted.otherRemaining at hb
  unfold certifiedCredits
  linarith only [hb, hs, hf, hc, hj]

theorem scalar_paid_le {b : ℝ} (hb : b ≤ otherRemaining) :
    b+tableGain+certifiedCredits-122417/800000 ≤ W17Accepted.paidCoefficient := by
  have h := remaining_lower hb
  unfold W17Accepted.paidCoefficient W17Accepted.remainingCoefficient
    W13TightAccepted.paidCoefficient at *
  linarith only [h]

theorem ordinary_P2 {b ε dmax : ℝ} (hb : b ≤ otherRemaining)
    (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (b+tableGain+certifiedCredits-122417/800000-ε)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨δ,hd,hm,hs,T,hT,hc⟩ := W17Accepted.ordinary_P2_paid hε hdmax
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
        N=p+r*q ∧ (r : ℝ) ≤ (q : ℝ)^(4469/5000 : ℝ) :=
  W17Accepted.refined_target (h.trans (remaining_lower hb))

end WuTarget.EveningRankOneAccepted
