import W07DensityTableV5
import Wu04BypassActual

noncomputable section
namespace WuTarget.W07
open NodeExtension ActualNineFeedback Wu2008DoubleSieve Wu04Bypass
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
  simpa only [densityMatrix, embedFour, dif_pos i.isLt] using legacy_matrix_eq_density i j

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
  exact add_le_add_left (paidTable_sum_le i z hz) _

theorem coupled_log_le (i : Fin 4) (z : Fin 9 → ℝ) (hz : ∀ k, 0 ≤ z k) :
    retainedCoupled (coupledRow i) z + (∑ k : Fin 9, logEntry (coupledRow i) k * z k) ≤
      coupledFeedback (coupledRow i) z := by
  rw [coupledFeedback_split]
  exact add_le_add_left (logEntry_sum_le _ (coupledRow_geometry i).1 z hz) _

theorem cells_add_density_le_coupled {p : SecondFunctionalParameters}
    (hp : CoupledGeometry p) (hc : p.kappa1 - 2 ≤ upperNode 0)
    {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) :
    cells z p.kappa1 / 5 + densityMoment p z / 5 ≤ coupledFeedback p z := by
  have hg := coupled_geometry_bounds hp
  have h0 := (profiles_nonneg (fun t _ => nineProfile_nonneg hz t)).2.2
    p.S ⟨hp.1.three_le_S, hp.1.S_le_five⟩
  have h1 := cells_le_eProfile hz hp.2.1 hc
  have hj0 := profileJ_nonneg hz hg.1 hp.1.three_le_S hp.1.S_le_five hg.2.1 hp.2.2.1
  have hj2 := profileJ_nonneg hz hg.2.2.1 hp.1.three_le_S hp.1.S_le_five
    hg.2.2.2.1 hp.2.2.2.1
  have hj3 := profileJ_nonneg hz hg.2.2.2.2.1 hp.1.three_le_S hp.1.S_le_five
    hg.2.2.2.2.2.1 hp.2.2.2.2
  unfold coupledFeedback
  linarith only [h0, h1, hj0, hj2, hj3]

theorem elementary_add_density_le (i k : Fin 9) :
    elementaryMatrix i k + densityMatrix i k ≤ feedbackMatrix i k := by
  unfold elementaryMatrix densityMatrix feedbackMatrix feedback
  split_ifs with h
  · rw [densityEntry_eq_basis _ (coupledRow_geometry _).1]
    simpa only [cells_basis] using cells_add_density_le_coupled
      (coupledRow_geometry ⟨i.val, h⟩) (coupled_kappa_cell ⟨i.val, h⟩) (nodeBasis_nonneg k)
  · let j : Fin 5 := ⟨i.val - 4, by omega⟩
    have hg := first_geometry j
    simpa only [cells_basis, add_zero] using
      cells_le_first (nodeBasis_nonneg k) hg.1 hg.2.2.1 hg.2.2.2.1
        (hg.2.1.trans hg.2.2.1) hg.2.2.2.2 (first_cell j)

theorem elementary_add_log_le (i k : Fin 9) :
    elementaryMatrix i k + logMatrix i k ≤ feedbackMatrix i k :=
  (add_le_add_left (logMatrix_le_densityMatrix i k) _).trans (elementary_add_density_le i k)

theorem elementary_add_paid_le (i k : Fin 9) :
    elementaryMatrix i k + paidMatrix i k ≤ feedbackMatrix i k :=
  (add_le_add_left (paidMatrix_le_densityMatrix i k) _).trans (elementary_add_density_le i k)

theorem baseline_le_elementary (i k : Fin 9) : M i k ≤ elementaryMatrix i k := by
  fin_cases i
  · exact matrix_row0 k
  · exact matrix_row1 k
  · exact matrix_row2 k
  · exact matrix_row3 k
  · exact matrix_row4 k
  · exact matrix_row5 k
  · exact matrix_row6 k
  · exact matrix_row7 k
  · exact matrix_row8 k

theorem baseline_add_paid_le (i k : Fin 9) :
    M i k + paidMatrix i k ≤ feedbackMatrix i k :=
  (add_le_add_right (baseline_le_elementary i k) _).trans (elementary_add_paid_le i k)

theorem baseline_add_log_le (i k : Fin 9) :
    M i k + logMatrix i k ≤ feedbackMatrix i k :=
  (add_le_add_right (baseline_le_elementary i k) _).trans (elementary_add_log_le i k)

theorem paid_actual {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 10)
    (z : Fin 9 → ℝ) (hz : ∀ k, 0 ≤ z k) (hza : ∀ k, z k ≤ actualNine δ k)
    (i : Fin 9) :
    base i - deltaLoss δ * loss i +
      (∑ k : Fin 9, (M i k + paidMatrix i k) * z k) ≤ actualNine δ i := by
  have hpaid := Finset.sum_le_sum (s := Finset.univ) (fun k _ =>
    mul_le_mul_of_nonneg_right (baseline_add_paid_le i k) (hz k))
  have hmono := matrixApply_mono feedbackMatrix_nonneg hza i
  have hsrc := actual_feedback hd hh i
  rw [feedback_expansion] at hsrc
  exact (add_le_add_left (hpaid.trans hmono) _).trans hsrc

theorem paid_v8_actual :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 10 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d → ∀ i : Fin 9,
        base i - deltaLoss δ * loss i +
          (∑ k : Fin 9, (M i k + paidMatrix i k) * v8 k) ≤ actualNine δ i := by
  obtain ⟨d, hd, hcap, hv⟩ := new_nine_actual
  exact ⟨d, hd, hcap, fun δ hδ hsmall i =>
    paid_actual hδ (hsmall.trans hcap) v8 v8_nonneg (hv δ hδ hsmall) i⟩

theorem coupled_paid_actual {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 10) (i : Fin 4) :
    coupledBase (coupledRow i) - deltaLoss δ * coupledLoss (coupledRow i) +
      (retainedCoupled (coupledRow i) (actualNine δ) +
        ∑ k : Fin 9, paidTable i k * actualNine δ k) ≤
      wuImprovementLimit true δ (coupledRow i).s :=
  (add_le_add_left (coupled_paid_le i _ (actualNine_nonneg hd hh)) _).trans
    (coupled_actual (coupledRow_geometry i) hd hh)

end WuTarget.W07
