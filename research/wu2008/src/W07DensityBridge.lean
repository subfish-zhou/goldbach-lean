import GatedDensityFinite

noncomputable section
namespace WuTarget.W07
open Real Set MeasureTheory NodeExtension ActualNineFeedback Wu2008DoubleSieve
open FiniteEndpointPayment GatedDensityPayment
open scoped Interval BigOperators

#check GatedDensityPayment.densityFinite_le
#check Real.one_sub_inv_le_log_of_pos
#check SecondFunctionalPositive.matrix

def densityEntry (p : SecondFunctionalParameters) (k : Fin 9) : ℝ :=
  (∫ v in left 1 3 k..right 1 3 k, SecondFunctionalCoupledFeedback.density p v) / 5

theorem densityMoment_eq_sum (p : SecondFunctionalParameters)
    (hp : MotherPair.AnalyticParameters p) (z : Fin 9 → ℝ) :
    densityMoment p z / 5 = ∑ k : Fin 9, densityEntry p k * z k := by
  rw [densityMoment, integral_cells z (by norm_num) (by norm_num) le_rfl
    (density_profile_integrable p hp z), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  unfold densityEntry
  ring

theorem densityEntry_eq_basis (p : SecondFunctionalParameters)
    (hp : MotherPair.AnalyticParameters p) (k : Fin 9) :
    densityEntry p k = densityMoment p (nodeBasis k) / 5 := by
  classical
  rw [densityMoment_eq_sum p hp]
  simp [nodeBasis]

theorem densityEntry_nonneg (p : SecondFunctionalParameters)
    (hp : MotherPair.AnalyticParameters p) (k : Fin 9) : 0 ≤ densityEntry p k := by
  rw [densityEntry_eq_basis p hp]
  exact div_nonneg (densityMoment_nonneg p hp (nodeBasis_nonneg k)) (by norm_num)

def embedFour (j : Fin 4) : Fin 9 := ⟨j.val, by omega⟩

theorem legacy_cell (j : Fin 4) :
    left 1 3 (embedFour j) = SecondFunctionalPositive.grid j.val ∧
      right 1 3 (embedFour j) = SecondFunctionalPositive.grid (j.val + 1) := by
  fin_cases j <;>
    norm_num [left, right, clip, embedFour, upperLeft, upperNode,
      SecondFunctionalPositive.grid]

theorem densityEntry_eq_legacy (p : SecondFunctionalParameters) (j : Fin 4) :
    densityEntry p (embedFour j) = SecondFunctionalPositive.rowEntry p j := by
  unfold densityEntry SecondFunctionalPositive.rowEntry
  rw [(legacy_cell j).1, (legacy_cell j).2]

theorem legacy_matrix_eq_density (i j : Fin 4) :
    SecondFunctionalPositive.matrix i j = densityEntry (coupledRow i) (embedFour j) :=
  (densityEntry_eq_legacy _ j).symm

def logEntry (p : SecondFunctionalParameters) (k : Fin 9) : ℝ :=
  intervalPayment p (left 1 3 k) (right 1 3 k) / 5

theorem logEntry_le_densityEntry (p : SecondFunctionalParameters)
    (hp : MotherPair.AnalyticParameters p) (k : Fin 9) :
    logEntry p k ≤ densityEntry p k :=
  div_le_div_of_nonneg_right
    (intervalPayment_le hp (clip_bounds (by norm_num : (1 : ℝ) ≤ 3)).1
      (cell_order 1 3 k) (clip_bounds (by norm_num : (1 : ℝ) ≤ 3)).2)
    (by norm_num)

theorem logEntry_sum_le (p : SecondFunctionalParameters)
    (hp : MotherPair.AnalyticParameters p) (z : Fin 9 → ℝ) (hz : ∀ k, 0 ≤ z k) :
    (∑ k : Fin 9, logEntry p k * z k) ≤ densityMoment p z / 5 := by
  rw [densityMoment_eq_sum p hp]
  exact Finset.sum_le_sum (fun k _ =>
    mul_le_mul_of_nonneg_right (logEntry_le_densityEntry p hp k) (hz k))

end WuTarget.W07
