import W10Collected
import Wu08FourMotherTerminal

noncomputable section
open Real Wu2008DoubleSieve

namespace WuTarget.W10

def paidFirst : ℝ := 8 * TailWholeCommonLog.collected

def firstLower : ℝ := 372494984143099449 / 25000000000000000

def firstUpper : ℝ := 1862645559843461681 / 125000000000000000

theorem paidFirst_bounds : firstLower ≤ paidFirst ∧ paidFirst ≤ firstUpper := by
  dsimp [firstLower, firstUpper, paidFirst]
  constructor <;> linarith only [collected_bounds.1, collected_bounds.2]

theorem complete_max_preserved :
    8 * CliF1AffinePaymentParent.finite ≤ paidFirst := by
  dsimp [paidFirst]
  linarith only [CliF1AffinePaymentParent.finite_le_collected]

theorem guaranteed_preserved :
    8 * (F1SignedUpperWhole.finite + F1NextLedger.guaranteed) ≤ paidFirst := by
  linarith only [complete_max_preserved, F1NextLedger.original_finite_plus_guaranteed]

theorem old_first_strictly_improved :
    8 * F1SignedUpperWhole.finite < paidFirst := by
  linarith only [guaranteed_preserved, F1NextLedger.guaranteed_pos]

theorem paidFirst_exact :
    Wu08TerminalAlignment.firstMain =
      paidFirst + 8 * (TailEndpointPayment.tailRemainder + FreshCommonLog.eLoss) := by
  rw [TailWholeCommonLog.firstMain_exact]
  unfold paidFirst
  ring

theorem paidFirst_le_actual : paidFirst ≤ Wu08TerminalAlignment.firstMain :=
  TailWholeCommonLog.collected_le_actual

theorem firstMain_lower : firstLower ≤ Wu08TerminalAlignment.firstMain :=
  paidFirst_bounds.1.trans paidFirst_le_actual

theorem first_actual_paid_count {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (paidFirst - ε) * wuSingularSeries N * N / log N ^ (2 : ℕ) ≤
        (sieveCount N 1 N ((N : ℝ) ^ truncatedSixthLowerAlpha) : ℝ) := by
  have he : 0 < Wu08TerminalAlignment.firstMain - paidFirst + ε := by
    linarith only [paidFirst_le_actual, hε]
  obtain ⟨T, hT, hcount⟩ := Wu08TerminalAlignment.first_actual_count he
  refine ⟨T, hT, ?_⟩
  intro N hN hEven
  convert hcount N hN hEven using 1
  ring

theorem first_actual_numeric_count {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (firstLower - ε) * wuSingularSeries N * N / log N ^ (2 : ℕ) ≤
        (sieveCount N 1 N ((N : ℝ) ^ truncatedSixthLowerAlpha) : ℝ) := by
  have he : 0 < Wu08TerminalAlignment.firstMain - firstLower + ε := by
    linarith only [firstMain_lower, hε]
  obtain ⟨T, hT, hcount⟩ := Wu08TerminalAlignment.first_actual_count he
  refine ⟨T, hT, ?_⟩
  intro N hN hEven
  convert hcount N hN hEven using 1
  ring

theorem first_weighted_count {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (3 * firstLower - ε) * wuSingularSeries N * N / log N ^ (2 : ℕ) ≤
        3 * (sieveCount N 1 N ((N : ℝ) ^ truncatedSixthLowerAlpha) : ℝ) := by
  obtain ⟨T, hT, hcount⟩ := first_actual_numeric_count (show 0 < ε / 3 by positivity)
  refine ⟨T, hT, ?_⟩
  intro N hN hEven
  have h := mul_le_mul_of_nonneg_left (hcount N hN hEven) (by norm_num : (0 : ℝ) ≤ 3)
  convert h using 1
  ring

theorem mother_first_lower :
    (1117484952429298347 : ℝ) / 25000000000000000 ≤
      3 * Wu08TerminalAlignment.firstMain := by
  have h := firstMain_lower
  dsimp [firstLower] at h
  linarith only [h]

open Wu08TerminalAlignment PositiveTwoPayment PositiveCoreResume PositiveSecondPayment

def otherNumerator : ℝ :=
  secondMain - thirdMain - fourthMain + fifthMain + sixthMain -
    2 * seventhMain - eighthMain - ninthMain - Wu08OriginalFourWeights.original10 -
    Wu08OriginalFourWeights.original11 + 8 * secondGain + fifthGain + FeedbackLimit.Cinf +
    4 * Phase20.rawPsi + 4 * Phase18.g18

def qFirstLower : ℝ := (3 * firstLower + otherNumerator) / 4

theorem original_mother_exact :
    Wu08FourMother.Qoriginal = (3 * firstMain + otherNumerator) / 4 := by
  unfold Wu08FourMother.Qoriginal otherNumerator
  ring

theorem original_mother_lower : qFirstLower ≤ Wu08FourMother.Qoriginal := by
  rw [original_mother_exact]
  unfold qFirstLower
  linarith only [firstMain_lower]

theorem original_mother_first_contribution :
    qFirstLower = (1117484952429298347 : ℝ) / 100000000000000000 +
      otherNumerator / 4 := by
  unfold qFirstLower firstLower
  ring

theorem printed_comparison :
    firstLower < (14900897 : ℝ) / 1000000 ∧
      (14900897 : ℝ) / 1000000 < firstUpper := by
  norm_num [firstLower, firstUpper]

end WuTarget.W10
