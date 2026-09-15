import WSourceClosureBudget
import WSrcFourEnclosureAccepted

noncomputable section
namespace WuTarget.SourceRevisedClosureBudget
open Wu2008DoubleSieve Wu08TerminalAlignment Wu08OriginalFourWeights

/-- Only the source-gain amount and its count interpretation remain inputs here.
The original integral-pair upper bound is now supplied by an actual theorem. -/
theorem sufficient_source_budget {g234 g5 g6 : ℝ}
    (hG : (88/625 : ℝ) ≤ g234+g5+g6) :
    (8991/10000 : ℝ) ≤ SourceClosureBudget.coefficient g234 g5 g6 := by
  have h134 := E09JointMainMajor.target_lower
  have h5 := FifthClassicalClosure.final_target
  have h6 := E05SixthMajor.actual_sixth_target
  have h789 := E08Debit.weightedDebit_lt
  have h2 := W14.second_lower_with_recurrence
  have hc := Wu08OriginalFirstSteps.C_nonneg (by norm_num : (4 : ℝ) ≤ 103/25)
  have hFour := SourceFourAccepted.original_pair_enclosure.2
  rw [W14.second_lower_exact] at h2
  unfold SourceClosureBudget.coefficient
  linarith only [h134,h5,h6,h789,h2,hc,hG,hFour]

/-- A smaller sufficient scalar gain for the 1.8938 budget; not yet a gain producer. -/
theorem sufficient_weaker_budget {g234 g5 g6 : ℝ}
    (hG : (343/2500 : ℝ) ≤ g234+g5+g6) :
    (4491/5000 : ℝ) ≤ SourceClosureBudget.coefficient g234 g5 g6 := by
  have h := sufficient_source_budget
    (g234 := g234) (g5 := g5) (g6 := g6+9/2500) (by linarith only [hG])
  unfold SourceClosureBudget.coefficient at h ⊢
  linarith only [h]

end WuTarget.SourceRevisedClosureBudget

#check @WuTarget.SourceRevisedClosureBudget.sufficient_source_budget
#check @WuTarget.SourceRevisedClosureBudget.sufficient_weaker_budget
#print axioms WuTarget.SourceRevisedClosureBudget.sufficient_source_budget
#print axioms WuTarget.SourceRevisedClosureBudget.sufficient_weaker_budget
