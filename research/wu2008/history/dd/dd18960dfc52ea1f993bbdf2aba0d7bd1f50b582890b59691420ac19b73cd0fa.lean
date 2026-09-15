import W07DensityRationalV2

noncomputable section
namespace WuTarget.W07
open NodeExtension ActualNineFeedback Wu2008DoubleSieve MotherPair
open FiniteEndpointPayment GatedDensityPayment
open scoped BigOperators

def paidTable : Fin 4 → Fin 9 → ℝ :=
  ![![698561489 / 119083178500, 476373 / 172592000, 511 / 265360,
      11 / 19125, 0, 0, 0, 0, 0],
    ![1837269 / 321310000, 65829 / 26312000, 43 / 30240, 0, 0, 0, 0, 0, 0],
    ![542740475649 / 102225917255000, 1357673 / 625968000, 211 / 238960,
      0, 0, 0, 0, 0, 0],
    ![438776565232799 / 129858357964800000, 0, 0, 0, 0, 0, 0, 0, 0]]

theorem paidTable_row0 (k : Fin 9) :
    paidTable 0 k = rationalEntry (coupledRow 0) k := by
  fin_cases k <;>
    norm_num [paidTable, rationalEntry, rationalInterval, firstSplit, secondSplit,
      upperSwitch, lowerSwitch, left, right, clip, upperLeft, upperNode, coupledRow,
      SecondFunctionalPositive.parameters, SecondFunctionalParameters.row1] <;>
    norm_num [rationalDensity, rationalKernel, feedbackLower, feedbackUpper,
      feedbackPole, upperP, upperQ, lowerQ, ratio]

theorem paidTable_row1 (k : Fin 9) :
    paidTable 1 k = rationalEntry (coupledRow 1) k := by
  fin_cases k <;>
    norm_num [paidTable, rationalEntry, rationalInterval, firstSplit, secondSplit,
      upperSwitch, lowerSwitch, left, right, clip, upperLeft, upperNode, coupledRow,
      SecondFunctionalPositive.parameters, SecondFunctionalParameters.row2] <;>
    norm_num [rationalDensity, rationalKernel, feedbackLower, feedbackUpper,
      feedbackPole, upperP, upperQ, lowerQ, ratio]

theorem paidTable_row2 (k : Fin 9) :
    paidTable 2 k = rationalEntry (coupledRow 2) k := by
  fin_cases k <;>
    norm_num [paidTable, rationalEntry, rationalInterval, firstSplit, secondSplit,
      upperSwitch, lowerSwitch, left, right, clip, upperLeft, upperNode, coupledRow,
      SecondFunctionalPositive.parameters, SecondFunctionalParameters.row3] <;>
    norm_num [rationalDensity, rationalKernel, feedbackLower, feedbackUpper,
      feedbackPole, upperP, upperQ, lowerQ, ratio]

theorem paidTable_row3 (k : Fin 9) :
    paidTable 3 k = rationalEntry (coupledRow 3) k := by
  fin_cases k <;>
    norm_num [paidTable, rationalEntry, rationalInterval, firstSplit, secondSplit,
      upperSwitch, lowerSwitch, left, right, clip, upperLeft, upperNode, coupledRow,
      SecondFunctionalPositive.parameters, SecondFunctionalParameters.row4] <;>
    norm_num [rationalDensity, rationalKernel, feedbackLower, feedbackUpper,
      feedbackPole, upperP, upperQ, lowerQ, ratio]

theorem paidTable_eq_rationalEntry (i : Fin 4) (k : Fin 9) :
    paidTable i k = rationalEntry (coupledRow i) k := by
  fin_cases i
  · exact paidTable_row0 k
  · exact paidTable_row1 k
  · exact paidTable_row2 k
  · exact paidTable_row3 k

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
