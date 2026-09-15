import WParentScalarCount
import W15AcceptedCount
import W14Root

noncomputable section
namespace WuTarget.W14Accepted
open Wu2008DoubleSieve Wu08TerminalAlignment Wu08OriginalFourWeights

/-- The original signed terms outside the W14 and W15 blocks. -/
def signedCore (x : Fin 9 → ℝ) : ℝ :=
  (3*firstMain-thirdMain-fourthMain+sixthMain-
    2*seventhMain-eighthMain-ninthMain-original10-original11+W01.lowGain x)/4

/-- Keep the proved recurrence term and the unspent fifth-gain slack. -/
def retainedSlack : ℝ :=
  2*Wu08OriginalFirstSteps.C (103/25) +
    (PositiveCoreResume.fifthGain-W14.fifthGainLower)/4

def remainingCoefficient (x : Fin 9 → ℝ) : ℝ := signedCore x + retainedSlack

def paidCoefficient (x : Fin 9 → ℝ) : ℝ :=
  remainingCoefficient x + 535927/200000 + 2493/4000000

theorem retainedSlack_nonneg : 0 ≤ retainedSlack := by
  have hC := Wu08OriginalFirstSteps.C_nonneg (by norm_num : (4 : ℝ) ≤ 103/25)
  unfold retainedSlack
  linarith only [hC, W14.fifth_gain_lower]

theorem previous_split (x : Fin 9 → ℝ) :
    W15Accepted.remainingCoefficient x = signedCore x + W14.block/4 := by
  unfold W15Accepted.remainingCoefficient signedCore W14.block
  ring

theorem block_with_retained_slack :
    (535927/200000 : ℝ) + retainedSlack < W14.block/4 := by
  have h := W14.block_lower_retained
  have he := W14.exact_lower_gt
  unfold W14.exactLower at he
  unfold retainedSlack
  linarith only [h, he]

theorem paid_lt_previous (x : Fin 9 → ℝ) :
    paidCoefficient x < W15Accepted.paidCoefficient x := by
  unfold paidCoefficient remainingCoefficient W15Accepted.paidCoefficient
  rw [previous_split]
  linarith only [block_with_retained_slack]

theorem paid_lt_actual (x : Fin 9 → ℝ) :
    paidCoefficient x < W01.ordinaryCoefficient x :=
  (paid_lt_previous x).trans (W15Accepted.paidCoefficient_lt x)

/-- No old limit-payment theorem: this consumes the concrete enhanced vector. -/
theorem enhanced_P2_paid {ε dmax : ℝ} (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (paidCoefficient W04Accepted.enhanced-ε)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) :=
  ParentScalarCount.from_enhanced (paid_lt_actual W04Accepted.enhanced).le hε hdmax

end WuTarget.W14Accepted
