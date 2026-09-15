import WE07FifthClassicalPayment
import W14AcceptedCount

namespace WuTarget.FifthClassicalClosure
open Real Wu2008DoubleSieve
noncomputable section

def netCredit : ℝ := (33/20-W14.fifthLower)/4
def creditedCoefficient (x : Fin 9 → ℝ) : ℝ := W14Accepted.paidCoefficient x+netCredit

theorem net_credit_exact :
    netCredit = ((33/20 : ℝ)-
      434461939561019874125799419294056644337159802853296197124/
      268438702578293960879080582261444586162642656112408018625)/4 := by
  rw [netCredit, W14.fifth_lower_exact]

theorem net_credit_pos : 0 < netCredit := by
  rw [net_credit_exact]
  norm_num

theorem net_credit_lower :
    netCredit ≤ (Wu08TerminalAlignment.fifthMain-W14.fifthLower)/4 := by
  unfold netCredit
  linarith only [fifth_main_lower]

theorem net_accounting_identity :
    (Wu08TerminalAlignment.fifthMain-W14.fifthLower)/4 =
      netCredit+(Wu08TerminalAlignment.fifthMain-33/20)/4 := by
  unfold netCredit
  ring

theorem exact_block_replacement :
    W14.exactLower+4*netCredit =
      W14.secondLower+33/20+8*PositiveSecondPayment.secondGain+W14.fifthGainLower := by
  unfold W14.exactLower netCredit
  ring

theorem block_lower_replaced_retained :
    W14.secondLower+33/20+8*PositiveSecondPayment.secondGain+
      PositiveCoreResume.fifthGain+8*Wu08OriginalFirstSteps.C (103/25) ≤ W14.block := by
  unfold W14.block
  linarith only [W14.second_lower_with_recurrence, fifth_main_lower]

theorem block_lower_replaced :
    W14.exactLower+4*netCredit ≤ W14.block := by
  have hc := Wu08OriginalFirstSteps.C_nonneg (by norm_num : (4 : ℝ) ≤ 103/25)
  rw [exact_block_replacement]
  linarith only [block_lower_replaced_retained, W14.fifth_gain_lower, hc]

theorem block_with_retained_slack :
    (535927/200000 : ℝ)+W14Accepted.retainedSlack+netCredit < W14.block/4 := by
  have hp := W14.exact_lower_gt
  unfold W14.exactLower at hp
  unfold W14Accepted.retainedSlack netCredit
  linarith only [block_lower_replaced_retained, hp]

theorem credited_lt_previous (x : Fin 9 → ℝ) :
    creditedCoefficient x < W15Accepted.paidCoefficient x := by
  unfold creditedCoefficient W14Accepted.paidCoefficient W14Accepted.remainingCoefficient
    W15Accepted.paidCoefficient
  rw [W14Accepted.previous_split]
  linarith only [block_with_retained_slack]

theorem credited_lt_actual (x : Fin 9 → ℝ) :
    creditedCoefficient x < W01.ordinaryCoefficient x :=
  (credited_lt_previous x).trans (W15Accepted.paidCoefficient_lt x)

theorem credited_identity (x : Fin 9 → ℝ) :
    creditedCoefficient x-W14Accepted.paidCoefficient x =
      (33/20-W14.fifthLower)/4 := by
  unfold creditedCoefficient netCredit
  ring

theorem enhanced_P2_paid {ε dmax : ℝ} (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (creditedCoefficient W04Accepted.enhanced-ε)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) :=
  ParentScalarCount.from_enhanced (credited_lt_actual W04Accepted.enhanced).le hε hdmax

end
end WuTarget.FifthClassicalClosure
