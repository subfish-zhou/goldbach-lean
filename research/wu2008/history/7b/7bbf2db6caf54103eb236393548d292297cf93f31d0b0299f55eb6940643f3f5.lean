import W14AcceptedCount
import W11Root

noncomputable section
namespace WuTarget.W11Accepted
open Wu2008DoubleSieve Wu08TerminalAlignment Wu08OriginalFourWeights

/-- Alternative certificates for the SAME signed block, never additive credits. -/
def selectedCredit : ℝ :=
  max (3*firstMain-W11.pairUpper) W11.correlatedCredit

theorem selectedCredit_le_actual : selectedCredit ≤ 3*firstMain-thirdMain-fourthMain := by
  unfold selectedCredit
  apply max_le
  · linarith only [W11.actual_pair_upper]
  · exact W11.actual_correlated_lower

theorem separate_credit_le : 3*firstMain-W11.pairUpper ≤ selectedCredit :=
  le_max_left _ _

theorem correlated_credit_le : W11.correlatedCredit ≤ selectedCredit :=
  le_max_right _ _

/-- A later F1 payment can strengthen the separate branch, not add to the other branch. -/
theorem first_lower_transport {f : ℝ} (hf : f ≤ firstMain) :
    max (3*f-W11.pairUpper) W11.correlatedCredit ≤ selectedCredit := by
  apply max_le_max _ le_rfl
  linarith only [hf]

def outsideCoefficient (x : Fin 9 → ℝ) : ℝ :=
  (sixthMain-2*seventhMain-eighthMain-ninthMain-original10-original11+W01.lowGain x)/4 +
    W14Accepted.retainedSlack

def remainingCoefficient (x : Fin 9 → ℝ) : ℝ := selectedCredit/4 + outsideCoefficient x

def paidCoefficient (x : Fin 9 → ℝ) : ℝ :=
  remainingCoefficient x + 535927/200000 + 2493/4000000

theorem previous_split (x : Fin 9 → ℝ) :
    W14Accepted.remainingCoefficient x =
      (3*firstMain-thirdMain-fourthMain)/4 + outsideCoefficient x := by
  unfold W14Accepted.remainingCoefficient W14Accepted.signedCore outsideCoefficient
  ring

theorem paid_le_previous (x : Fin 9 → ℝ) :
    paidCoefficient x ≤ W14Accepted.paidCoefficient x := by
  unfold paidCoefficient remainingCoefficient W14Accepted.paidCoefficient
  rw [previous_split]
  linarith only [selectedCredit_le_actual]

theorem paid_lt_actual (x : Fin 9 → ℝ) :
    paidCoefficient x < W01.ordinaryCoefficient x :=
  (paid_le_previous x).trans_lt (W14Accepted.paid_lt_actual x)

theorem enhanced_P2_paid {ε dmax : ℝ} (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (paidCoefficient W04Accepted.enhanced-ε)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) :=
  ParentScalarCount.from_enhanced (paid_lt_actual W04Accepted.enhanced).le hε hdmax

theorem paid_threshold_iff (x : Fin 9 → ℝ) :
    (4491/5000 : ℝ) ≤ paidCoefficient x ↔
      (-7128233/4000000 : ℝ) ≤ remainingCoefficient x := by
  unfold paidCoefficient
  constructor <;> intro h <;> linarith

end WuTarget.W11Accepted
