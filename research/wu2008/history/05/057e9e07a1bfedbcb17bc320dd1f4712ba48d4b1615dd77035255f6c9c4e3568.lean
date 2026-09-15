import WE07FifthRoot
import W17AcceptedBudget

noncomputable section
namespace WuTarget.E07Accepted
open Wu2008DoubleSieve

def fifthBalance : ℝ :=
  (PositiveCoreResume.fifthGain-W14.fifthGainLower)/4

def otherRemaining : ℝ := W17Accepted.remainingCoefficient-fifthBalance

theorem fifth_paid : E07Fifth.netCredit ≤ fifthBalance := E07Fifth.fifth_balance_lower

theorem display_paid : (5862/1000000000 : ℝ) ≤ fifthBalance := by
  apply le_trans _ fifth_paid
  norm_num [E07Fifth.netCredit]

/-- Replace the previously unquantified balance; do not add it a second time. -/
theorem remaining_lower {b : ℝ} (hb : b ≤ otherRemaining) :
    b+E07Fifth.netCredit ≤ W17Accepted.remainingCoefficient := by
  have h := fifth_paid
  unfold otherRemaining at hb
  linarith only [hb, h]

theorem scalar_paid_le {b : ℝ} (hb : b ≤ otherRemaining) :
    b+E07Fifth.netCredit-122417/800000 ≤ W17Accepted.paidCoefficient := by
  have h := remaining_lower hb
  unfold W17Accepted.paidCoefficient W17Accepted.remainingCoefficient
    W13TightAccepted.paidCoefficient at *
  linarith only [h]

theorem scalar_ordinary_P2 {b ε dmax : ℝ} (hb : b ≤ otherRemaining)
    (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (b+E07Fifth.netCredit-122417/800000-ε)*U8CanonicalMother.M N ≤
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
    (h : (840977/800000 : ℝ) ≤ b+E07Fifth.netCredit) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      RefinedExit.margin/2*U8CanonicalMother.M N ≤
        ((Wu2004MeanValue.refinedGood N (9469/5000)).card : ℝ) ∧
      ∃ p r q : ℕ, p.Prime ∧ (r=1 ∨ r.Prime) ∧ q.Prime ∧
        N=p+r*q ∧ (r : ℝ) ≤ (q : ℝ)^(4469/5000 : ℝ) :=
  W17Accepted.refined_target (h.trans (remaining_lower hb))

end WuTarget.E07Accepted
