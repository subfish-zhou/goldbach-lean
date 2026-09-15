import W07DensityTableV5

noncomputable section
namespace WuTarget.W07
open NodeExtension ActualNineFeedback Wu2008DoubleSieve
open scoped BigOperators

def densityMatrix (i k : Fin 9) : ℝ :=
  if h : i.val < 4 then densityEntry (coupledRow ⟨i.val, h⟩) k else 0

def paidMatrix (i k : Fin 9) : ℝ :=
  if h : i.val < 4 then paidTable ⟨i.val, h⟩ k else 0

def logMatrix (i k : Fin 9) : ℝ :=
  if h : i.val < 4 then logEntry (coupledRow ⟨i.val, h⟩) k else 0

def retainedCoupled (p : SecondFunctionalParameters) (z : Fin 9 → ℝ) : ℝ :=
  (4 * eProfile (nineProfile z) p.S + eProfile (nineProfile z) p.kappa1 +
    profileJ z p.s p.S + profileJ z p.kappa2 p.S + profileJ z p.kappa3 p.S) / 5

theorem coupledFeedback_split (p : SecondFunctionalParameters) (z : Fin 9 → ℝ) :
    coupledFeedback p z = retainedCoupled p z + densityMoment p z / 5 := by
  unfold coupledFeedback retainedCoupled
  ring

def retainedFeedback (z : Fin 9 → ℝ) (i : Fin 9) : ℝ :=
  if h : i.val < 4 then retainedCoupled (coupledRow ⟨i.val, h⟩) z
  else firstFeedback z (firstNode ⟨i.val - 4, by omega⟩) (firstS ⟨i.val - 4, by omega⟩)

def retainedMatrix (i k : Fin 9) : ℝ := retainedFeedback (nodeBasis k) i

theorem feedbackMatrix_split (i k : Fin 9) :
    feedbackMatrix i k = retainedMatrix i k + densityMatrix i k := by
  unfold feedbackMatrix feedback retainedMatrix retainedFeedback densityMatrix
  split_ifs with h
  · rw [densityEntry_eq_basis _ (coupledRow_geometry _).1]
    exact coupledFeedback_split _ _
  · exact (add_zero _).symm

theorem legacy_matrix_eq_principal (i j : Fin 4) :
    SecondFunctionalPositive.matrix i j = densityMatrix (embedFour i) (embedFour j) := by
  rw [densityMatrix, dif_pos (show (embedFour i).val < 4 from i.isLt)]
  exact legacy_matrix_eq_density i j

theorem paidMatrix_nonneg (i k : Fin 9) : 0 ≤ paidMatrix i k := by
  unfold paidMatrix
  split_ifs with h
  · exact paidTable_nonneg _ _
  · exact le_rfl

theorem paidMatrix_le_logMatrix (i k : Fin 9) : paidMatrix i k ≤ logMatrix i k := by
  unfold paidMatrix logMatrix
  split_ifs with h
  · exact paidTable_le_logEntry _ _
  · exact le_rfl

theorem logMatrix_le_densityMatrix (i k : Fin 9) : logMatrix i k ≤ densityMatrix i k := by
  unfold logMatrix densityMatrix
  split_ifs with h
  · exact logEntry_le_densityEntry _ (coupledRow_geometry _).1 _
  · exact le_rfl

theorem paidMatrix_le_densityMatrix (i k : Fin 9) : paidMatrix i k ≤ densityMatrix i k :=
  (paidMatrix_le_logMatrix i k).trans (logMatrix_le_densityMatrix i k)

theorem first_rows_zero (i k : Fin 9) (hi : 4 ≤ i.val) :
    paidMatrix i k = 0 ∧ logMatrix i k = 0 ∧ densityMatrix i k = 0 := by
  simp [paidMatrix, logMatrix, densityMatrix, not_lt.mpr hi]

theorem coupled_paid_le (i : Fin 4) (z : Fin 9 → ℝ) (hz : ∀ k, 0 ≤ z k) :
    retainedCoupled (coupledRow i) z + (∑ k : Fin 9, paidTable i k * z k) ≤
      coupledFeedback (coupledRow i) z := by
  rw [coupledFeedback_split]
  exact add_le_add le_rfl (paidTable_sum_le i z hz)

theorem coupled_log_le (i : Fin 4) (z : Fin 9 → ℝ) (hz : ∀ k, 0 ≤ z k) :
    retainedCoupled (coupledRow i) z + (∑ k : Fin 9, logEntry (coupledRow i) k * z k) ≤
      coupledFeedback (coupledRow i) z := by
  rw [coupledFeedback_split]
  exact add_le_add le_rfl (logEntry_sum_le _ (coupledRow_geometry i).1 z hz)

end WuTarget.W07
