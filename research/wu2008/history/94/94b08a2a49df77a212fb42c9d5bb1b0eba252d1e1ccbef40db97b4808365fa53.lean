import W11CreditAcceptedBudget
import W13TightRoot

noncomputable section
namespace WuTarget.W13TightAccepted
open Wu2008DoubleSieve Wu08TerminalAlignment Wu08OriginalFourWeights

/-- Keep the gap between the exact upper certificate and its short display. -/
def fourSlack : ℝ := (865380/1000000-W13Tight.pairUpper)/4

theorem fourSlack_pos : 0 < fourSlack :=
  div_pos (sub_pos.mpr W13Tight.pairUpper_lt_display) (by norm_num)

def remainingCoefficient : ℝ :=
  (sixthMain+W02Accepted.nodeGain)/4 +
    W14Accepted.retainedSlack + W12Accepted.debitSlack +
    W11CreditAccepted.paymentSlack + fourSlack

def paidCoefficient : ℝ := remainingCoefficient-122417/800000

def oldCapCoefficient : ℝ := W11CreditAccepted.paidCoefficient +
  (original10+original11-W13.pairUpper)/4

theorem paid_exact : paidCoefficient = W11CreditAccepted.paidCoefficient +
    (original10+original11-W13Tight.pairUpper)/4 := by
  unfold paidCoefficient remainingCoefficient fourSlack W11CreditAccepted.paidCoefficient
    W11CreditAccepted.remainingCoefficient
  ring

theorem paid_le_previous : paidCoefficient ≤ W11CreditAccepted.paidCoefficient := by
  rw [paid_exact]
  linarith only [W13Tight.original_pair_upper]

theorem paid_gain_over_old_cap : oldCapCoefficient+2457/1000000 < paidCoefficient := by
  rw [paid_exact]
  unfold oldCapCoefficient
  linarith only [W13Tight.recovery_lower]

theorem paid_lt_actual : paidCoefficient < W01.ordinaryCoefficient W04Accepted.enhanced :=
  paid_le_previous.trans_lt W11CreditAccepted.paid_lt_actual

theorem ordinary_P2_paid {ε dmax : ℝ} (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (paidCoefficient-ε)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) :=
  ParentScalarCount.from_enhanced paid_lt_actual.le hε hdmax

theorem paid_threshold_iff : (4491/5000 : ℝ) ≤ paidCoefficient ↔
    (840977/800000 : ℝ) ≤ remainingCoefficient := by
  unfold paidCoefficient
  constructor <;> intro h <;> linarith

theorem refined_target (h : (840977/800000 : ℝ) ≤ remainingCoefficient) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      RefinedExit.margin/2*U8CanonicalMother.M N ≤
        ((Wu2004MeanValue.refinedGood N (9469/5000)).card : ℝ) ∧
      ∃ p r q : ℕ, p.Prime ∧ (r=1 ∨ r.Prime) ∧ q.Prime ∧
        N=p+r*q ∧ (r : ℝ) ≤ (q : ℝ)^(4469/5000 : ℝ) := by
  apply RefinedExit.from_actual_count (paid_threshold_iff.mpr h)
  intro ε hε
  obtain ⟨_,_,_,_,T,hT,hcount⟩ := ordinary_P2_paid hε (by norm_num : (0 : ℝ) < 1)
  exact ⟨T,hT,hcount⟩

end WuTarget.W13TightAccepted
