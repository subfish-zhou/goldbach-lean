import WE09JointMainMajorRoot
import WE07FifthClassicalRoot
import WE05SixthMajorRoot
import WE08DebitRoot

noncomputable section
namespace WuTarget.SourceClosureBudget
open Wu2008DoubleSieve Wu08TerminalAlignment Wu08OriginalFourWeights

/-- The source-shaped scalar only. A source-gain-to-count theorem must be supplied separately. -/
def coefficient (g234 g5 g6 : ℝ) : ℝ :=
  (3*firstMain+secondMain-thirdMain-fourthMain+fifthMain+sixthMain-
    2*seventhMain-eighthMain-ninthMain-original10-original11+g234+g5+g6)/4

/-- Reuse existing classical estimates. These two hypotheses are NOT claimed to be proved. -/
theorem sufficient_source_budget {g234 g5 g6 : ℝ}
    (hG : (11/100 : ℝ) ≤ g234+g5+g6)
    (hFour : original10+original11 ≤ (13/20 : ℝ)) :
    (8991/10000 : ℝ) ≤ coefficient g234 g5 g6 := by
  have h134 := E09JointMainMajor.target_lower
  have h5 := FifthClassicalClosure.final_target
  have h6 := E05SixthMajor.actual_sixth_target
  have h789 := E08Debit.weightedDebit_lt
  have h2 := W14.second_lower_with_recurrence
  have hc := Wu08OriginalFirstSteps.C_nonneg (by norm_num : (4 : ℝ) ≤ 103/25)
  rw [W14.second_lower_exact] at h2
  unfold coefficient
  linarith only [h134,h5,h6,h789,h2,hc,hG,hFour]

theorem above_original_theorem {g234 g5 g6 : ℝ}
    (hG : (11/100 : ℝ) ≤ g234+g5+g6)
    (hFour : original10+original11 ≤ (13/20 : ℝ)) :
    (899/1000 : ℝ) < coefficient g234 g5 g6 := by
  linarith only [sufficient_source_budget hG hFour]

#check @sufficient_source_budget
#print axioms sufficient_source_budget
#check @above_original_theorem
#print axioms above_original_theorem
end WuTarget.SourceClosureBudget
