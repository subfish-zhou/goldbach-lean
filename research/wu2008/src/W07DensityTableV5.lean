import W07DensityData
import W07TableProbe

noncomputable section
namespace WuTarget.W07
open NodeExtension ActualNineFeedback Wu2008DoubleSieve MotherPair
open FiniteEndpointPayment GatedDensityPayment
open scoped BigOperators

theorem paidTable_row0 (k : Fin 9) :
    paidTable 0 k = rationalEntry (coupledRow 0) k := by
  change paidTable 0 k = rationalEntry SecondFunctionalParameters.row1 k
  fin_cases k <;>
    norm_num [paidTable, rationalEntry, rationalInterval, firstSplit, secondSplit,
      upperSwitch, lowerSwitch, left, right, clip, upperLeft, upperNode,
      SecondFunctionalParameters.row1] <;>
    norm_num [rationalDensity, rationalKernel, feedbackLower, feedbackUpper,
      feedbackPole, upperP, upperQ, lowerQ, ratio]

theorem paidTable_row1 (k : Fin 9) :
    paidTable 1 k = rationalEntry (coupledRow 1) k := by
  change paidTable 1 k = rationalEntry SecondFunctionalParameters.row2 k
  fin_cases k <;>
    norm_num [paidTable, rationalEntry, rationalInterval, firstSplit, secondSplit,
      upperSwitch, lowerSwitch, left, right, clip, upperLeft, upperNode,
      SecondFunctionalParameters.row2] <;>
    norm_num [rationalDensity, rationalKernel, feedbackLower, feedbackUpper,
      feedbackPole, upperP, upperQ, lowerQ, ratio]

theorem paidTable_row2_rest (k : Fin 9) (hk : k ≠ 0) :
    paidTable 2 k = rationalEntry (coupledRow 2) k := by
  change paidTable 2 k = rationalEntry SecondFunctionalParameters.row3 k
  fin_cases k
  · exact (hk rfl).elim
  all_goals
    norm_num [paidTable, rationalEntry, rationalInterval, firstSplit, secondSplit,
      upperSwitch, lowerSwitch, left, right, clip, upperLeft, upperNode,
      SecondFunctionalParameters.row3]
  all_goals
    norm_num [rationalDensity, rationalKernel, feedbackLower, feedbackUpper,
      feedbackPole, upperP, upperQ, lowerQ, ratio]
  all_goals rfl

theorem paidTable_row3_first :
    paidTable 3 0 = rationalEntry (coupledRow 3) 0 := by
  change paidTable 3 0 = rationalEntry SecondFunctionalParameters.row4 0
  norm_num [paidTable, rationalEntry, rationalInterval, firstSplit, secondSplit,
    upperSwitch, lowerSwitch, left, right, clip, upperLeft, upperNode,
    SecondFunctionalParameters.row4]
  norm_num [rationalDensity, rationalKernel, feedbackLower, feedbackUpper,
    feedbackPole, upperP, upperQ, lowerQ, ratio]
  rfl

theorem paidTable_row3_rest (k : Fin 9) (hk : k ≠ 0) :
    paidTable 3 k = rationalEntry (coupledRow 3) k := by
  change paidTable 3 k = rationalEntry SecondFunctionalParameters.row4 k
  fin_cases k
  · exact (hk rfl).elim
  all_goals
    norm_num [paidTable, rationalEntry, rationalInterval, firstSplit, secondSplit,
      upperSwitch, lowerSwitch, left, right, clip, upperLeft, upperNode,
      SecondFunctionalParameters.row4]
  all_goals
    norm_num [rationalDensity, rationalKernel, feedbackLower, feedbackUpper,
      feedbackPole, upperP, upperQ, lowerQ, ratio]
  all_goals rfl

theorem paidTable_eq_rationalEntry (i : Fin 4) (k : Fin 9) :
    paidTable i k = rationalEntry (coupledRow i) k := by
  fin_cases i
  · exact paidTable_row0 k
  · exact paidTable_row1 k
  · by_cases hk : k = 0
    · subst k; exact table_probe.symm
    · exact paidTable_row2_rest k hk
  · by_cases hk : k = 0
    · subst k; exact paidTable_row3_first
    · exact paidTable_row3_rest k hk

theorem paidTable_nonneg (i : Fin 4) (k : Fin 9) : 0 ≤ paidTable i k := by
  rw [paidTable_eq_rationalEntry]
  exact (rationalEntry_bounds _ (coupledRow_geometry i).1 k).1

theorem paidTable_le_logEntry (i : Fin 4) (k : Fin 9) :
    paidTable i k ≤ logEntry (coupledRow i) k := by
  rw [paidTable_eq_rationalEntry]
  exact (rationalEntry_bounds _ (coupledRow_geometry i).1 k).2

theorem paidTable_le_densityEntry (i : Fin 4) (k : Fin 9) :
    paidTable i k ≤ densityEntry (coupledRow i) k :=
  (paidTable_le_logEntry i k).trans (logEntry_le_densityEntry _ (coupledRow_geometry i).1 k)

theorem paidTable_sum_le (i : Fin 4) (z : Fin 9 → ℝ) (hz : ∀ k, 0 ≤ z k) :
    (∑ k : Fin 9, paidTable i k * z k) ≤ densityMoment (coupledRow i) z / 5 := by
  simp_rw [paidTable_eq_rationalEntry]
  exact rationalEntry_sum_le _ (coupledRow_geometry i).1 z hz

end WuTarget.W07
