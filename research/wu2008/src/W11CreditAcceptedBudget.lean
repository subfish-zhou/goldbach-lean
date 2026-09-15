import W11CreditRoot
import W12AcceptedCount
import WRefinedCountBridge

noncomputable section
namespace WuTarget.W11CreditAccepted
open Wu2008DoubleSieve Wu08TerminalAlignment Wu08OriginalFourWeights

/-- The surplus of the exact rational payment over its shorter display bound. -/
def paymentSlack : ℝ := (W11Credit.payment-1357218/1000000)/4

theorem paymentSlack_pos : 0 < paymentSlack :=
  div_pos (sub_pos.mpr W11Credit.payment_bounds.1) (by norm_num)

def remainingCoefficient : ℝ :=
  (sixthMain-original10-original11+W02Accepted.nodeGain)/4 +
    W14Accepted.retainedSlack + W12Accepted.debitSlack + paymentSlack

def paidCoefficient : ℝ := remainingCoefficient + 50659/800000

theorem paid_exact : paidCoefficient =
    (W11Credit.payment+sixthMain-original10-original11+W02Accepted.nodeGain)/4 +
      W14Accepted.retainedSlack + W12Accepted.debitSlack +
      535927/200000+2493/4000000-2956239/1000000 := by
  unfold paidCoefficient remainingCoefficient paymentSlack
  ring

theorem payment_le_selected : W11Credit.payment ≤ W11Accepted.selectedCredit :=
  W11Credit.payment_le_credit.trans W11Accepted.correlated_credit_le

theorem paid_le_previous : paidCoefficient ≤ W12Accepted.paidCoefficient W04Accepted.enhanced := by
  rw [paid_exact]
  unfold W12Accepted.paidCoefficient W12Accepted.remainingCoefficient W12Accepted.otherCoefficient
  linarith only [payment_le_selected, W02Accepted.nodeGain_le_full]

theorem paid_lt_actual : paidCoefficient < W01.ordinaryCoefficient W04Accepted.enhanced :=
  paid_le_previous.trans_lt (W12Accepted.paid_lt_actual W04Accepted.enhanced)

theorem ordinary_P2_paid {ε dmax : ℝ} (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (paidCoefficient-ε)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) :=
  ParentScalarCount.from_enhanced paid_lt_actual.le hε hdmax

theorem paid_threshold_iff : (4491/5000 : ℝ) ≤ paidCoefficient ↔
    (667901/800000 : ℝ) ≤ remainingCoefficient := by
  unfold paidCoefficient
  constructor <;> intro h <;> linarith

/-- The sole remaining hypothesis is the displayed actual scalar budget. -/
theorem refined_target (h : (667901/800000 : ℝ) ≤ remainingCoefficient) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      RefinedExit.margin/2*U8CanonicalMother.M N ≤
        ((Wu2004MeanValue.refinedGood N (9469/5000)).card : ℝ) ∧
      ∃ p r q : ℕ, p.Prime ∧ (r=1 ∨ r.Prime) ∧ q.Prime ∧
        N=p+r*q ∧ (r : ℝ) ≤ (q : ℝ)^(4469/5000 : ℝ) := by
  apply RefinedExit.from_actual_count (paid_threshold_iff.mpr h)
  intro ε hε
  obtain ⟨_,_,_,_,T,hT,hcount⟩ := ordinary_P2_paid hε (by norm_num : (0 : ℝ) < 1)
  exact ⟨T,hT,hcount⟩

end WuTarget.W11CreditAccepted
