import Wu04BypassMatrix

noncomputable section
namespace WuTarget.W08
open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension ActualNineFeedback
open FirstFeedbackIntegrals
open scoped Interval BigOperators

theorem paidCells_le_kernel {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) {S : ℝ}
    (hS : 3 ≤ S) (hcell : S - 2 ≤ upperNode 0) :
    RemainingHf.paidCells z S ≤
      ∫ t in (S - 2)..3, nineProfile z t * (log ((t + 1) / (S - 1)) / t) := by
  have hS5 : S ≤ 5 := by have h := (upperNode_bounds 0).2; linarith
  have hw : ContinuousOn (fun t => log ((t + 1) / (S - 1)) / t)
      (uIcc (S - 2) 3) := by
    apply ContinuousOn.div (log_weight_continuous hS hS5) continuousOn_id
    intro t ht
    rw [uIcc_of_le (by linarith : S - 2 ≤ 3)] at ht
    dsimp
    linarith [ht.1]
  rw [profile_integral_cells z (by linarith : 1 ≤ S - 2) hcell hw]
  exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left
    (RemainingHf.paidCell_paid hS (cell_bounds (by linarith) hcell k).1
      (cell_bounds (by linarith) hcell k).2.1) (hz k))

theorem paidCells_le_eProfile {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) {S : ℝ}
    (hS : 3 ≤ S) (hcell : S - 2 ≤ upperNode 0) :
    RemainingHf.paidCells z S ≤ eProfile (nineProfile z) S := by
  have hS5 : S ≤ 5 := by have h := (upperNode_bounds 0).2; linarith
  have hp := (profiles_nonneg (fun t _ => nineProfile_nonneg hz t)).1
  have hl : 0 ≤ log (4 / (S - 1)) :=
    log_nonneg ((one_le_div (by linarith : 0 < S - 1)).mpr (by linarith))
  exact (le_add_of_nonneg_left (mul_nonneg hp hl)).trans
    (RemainingHf.paidCells_le hz hS hcell)

theorem paidCells_basis (S : ℝ) (k : Fin 9) :
    RemainingHf.paidCells (nodeBasis k) S =
      RemainingHf.paidCell S (cellLeft (S - 2) k) (upperNode k) := by
  classical
  simp [RemainingHf.paidCells, nodeBasis]

theorem paidCells_le_first {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) {s S : ℝ}
    (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5) (hsS : s ≤ S)
    (hr : 2 ≤ S - S / s) (hcell : S - 2 ≤ upperNode 0) :
    RemainingHf.paidCells z S ≤ firstFeedback z s S := by
  have he := paidCells_le_eProfile hz hS hcell
  have hj := profileJ_nonneg hz hs hS hS5 hsS hr
  unfold firstFeedback
  linarith only [he, hj]

theorem paidCells_le_coupled {p : SecondFunctionalParameters} (hp : CoupledGeometry p)
    (hc : p.kappa1 - 2 ≤ upperNode 0) {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) :
    RemainingHf.paidCells z p.kappa1 / 5 ≤ coupledFeedback p z := by
  have hg := coupled_geometry_bounds hp
  have he := (profiles_nonneg (fun t _ => nineProfile_nonneg hz t)).2.2
  have h0 := he p.S ⟨hp.1.three_le_S, hp.1.S_le_five⟩
  have h1 := paidCells_le_eProfile hz hp.2.1 hc
  have hj0 := profileJ_nonneg hz hg.1 hp.1.three_le_S hp.1.S_le_five
    hg.2.1 hp.2.2.1
  have hj2 := profileJ_nonneg hz hg.2.2.1 hp.1.three_le_S hp.1.S_le_five
    hg.2.2.2.1 hp.2.2.2.1
  have hj3 := profileJ_nonneg hz hg.2.2.2.2.1 hp.1.three_le_S hp.1.S_le_five
    hg.2.2.2.2.2.1 hp.2.2.2.2
  have hd := densityMoment_nonneg p hp.1 hz
  unfold coupledFeedback
  linarith only [h0, h1, hj0, hj2, hj3, hd]

/-- Only the E-kernel already retained by elementaryMatrix is replaced. -/
def paidMatrix (i k : Fin 9) : ℝ :=
  if h : i.val < 4 then
    RemainingHf.paidCell (coupledRow ⟨i.val, h⟩).kappa1
      (cellLeft ((coupledRow ⟨i.val, h⟩).kappa1 - 2) k) (upperNode k) / 5
  else
    RemainingHf.paidCell (firstS ⟨i.val - 4, by omega⟩)
      (cellLeft (firstS ⟨i.val - 4, by omega⟩ - 2) k) (upperNode k)

theorem paidMatrix_le (i k : Fin 9) : paidMatrix i k ≤ feedbackMatrix i k := by
  unfold paidMatrix feedbackMatrix feedback
  split_ifs with h
  · have hh := paidCells_le_coupled (coupledRow_geometry ⟨i.val, h⟩)
      (Wu04Bypass.coupled_kappa_cell ⟨i.val, h⟩) (nodeBasis_nonneg k)
    simpa only [paidCells_basis] using hh
  · let j : Fin 5 := ⟨i.val - 4, by omega⟩
    have hg := first_geometry j
    have hh := paidCells_le_first (nodeBasis_nonneg k) hg.1 hg.2.2.1 hg.2.2.2.1
      (hg.2.1.trans hg.2.2.1) hg.2.2.2.2 (Wu04Bypass.first_cell j)
    simpa only [paidCells_basis] using hh

theorem paidMatrix_apply_eq (z : Fin 9 → ℝ) (i : Fin 9) :
    (∑ k : Fin 9, paidMatrix i k * z k) =
      if h : i.val < 4 then RemainingHf.paidCells z (coupledRow ⟨i.val, h⟩).kappa1 / 5
      else RemainingHf.paidCells z (firstS ⟨i.val - 4, by omega⟩) := by
  unfold paidMatrix
  split_ifs with h
  · rw [RemainingHf.paidCells, Finset.sum_div]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  · rw [RemainingHf.paidCells]
    exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

theorem paidMatrix_apply_le_feedback {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k)
    (i : Fin 9) : (∑ k : Fin 9, paidMatrix i k * z k) ≤ feedback z i := by
  rw [feedback_expansion]
  exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (paidMatrix_le i k) (hz k))

theorem paidMatrix_apply_le_actual {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 10)
    {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) (hza : ∀ k, z k ≤ actualNine δ k)
    (i : Fin 9) :
    base i - deltaLoss δ * loss i + (∑ k : Fin 9, paidMatrix i k * z k) ≤
      actualNine δ i := by
  have hm : (∑ k : Fin 9, paidMatrix i k * z k) ≤ feedback (actualNine δ) i := by
    rw [feedback_expansion]
    apply Finset.sum_le_sum
    intro k _
    exact (mul_le_mul_of_nonneg_right (paidMatrix_le i k) (hz k)).trans
      (mul_le_mul_of_nonneg_left (hza k) (feedbackMatrix_nonneg i k))
  linarith only [hm, actual_feedback hd hh i]

end WuTarget.W08
