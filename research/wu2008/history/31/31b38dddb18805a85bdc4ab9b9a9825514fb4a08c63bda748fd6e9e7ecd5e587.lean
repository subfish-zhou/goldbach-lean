import W11AcceptedCount
import W12FinalRoot

noncomputable section
namespace WuTarget.W12Accepted
open Wu2008DoubleSieve Wu08TerminalAlignment Wu08OriginalFourWeights

/-- Retain the entire analytic advantage over the rounded display cap. -/
def debitSlack : ℝ := (W12.debitCeiling-W12.analyticUpper)/4

theorem debitSlack_pos : 0 < debitSlack := by
  have h := W12.analyticUpper_le_rationalUpper.trans_lt W12.rationalUpper_lt_debitCeiling
  exact div_pos (sub_pos.mpr h) (by norm_num)

def otherCoefficient (x : Fin 9 → ℝ) : ℝ :=
  (W11Accepted.selectedCredit+sixthMain-original10-original11+W01.lowGain x)/4 +
    W14Accepted.retainedSlack

def remainingCoefficient (x : Fin 9 → ℝ) : ℝ := otherCoefficient x + debitSlack

def paidCoefficient (x : Fin 9 → ℝ) : ℝ :=
  remainingCoefficient x + 535927/200000 + 2493/4000000 - 2956239/1000000

theorem paid_eq_unrounded (x : Fin 9 → ℝ) :
    paidCoefficient x = otherCoefficient x-W12.analyticUpper/4+
      535927/200000+2493/4000000 := by
  unfold paidCoefficient remainingCoefficient debitSlack W12.debitCeiling
  ring

theorem paid_le_previous (x : Fin 9 → ℝ) :
    paidCoefficient x ≤ W11Accepted.paidCoefficient x := by
  have h := W12.weightedDebit_le_analyticUpper
  unfold W12.weightedDebit at h
  rw [paid_eq_unrounded]
  unfold otherCoefficient W11Accepted.paidCoefficient W11Accepted.remainingCoefficient
    W11Accepted.outsideCoefficient
  linarith only [h]

theorem paid_lt_actual (x : Fin 9 → ℝ) :
    paidCoefficient x < W01.ordinaryCoefficient x :=
  (paid_le_previous x).trans_lt (W11Accepted.paid_lt_actual x)

theorem enhanced_P2_paid {ε dmax : ℝ} (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (paidCoefficient W04Accepted.enhanced-ε)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) :=
  ParentScalarCount.from_enhanced (paid_lt_actual W04Accepted.enhanced).le hε hdmax

theorem paid_threshold_iff (x : Fin 9 → ℝ) :
    (4491/5000 : ℝ) ≤ paidCoefficient x ↔
      (4696723/4000000 : ℝ) ≤ remainingCoefficient x := by
  unfold paidCoefficient
  constructor <;> intro h <;> linarith

end WuTarget.W12Accepted
