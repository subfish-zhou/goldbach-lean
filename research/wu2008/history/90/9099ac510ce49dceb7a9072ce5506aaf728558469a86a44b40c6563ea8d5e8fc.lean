import Wu04BypassCells

noncomputable section
namespace Wu04Bypass
open ActualNineFeedback NodeExtension Wu2008DoubleSieve FirstFeedbackIntegrals
open scoped BigOperators

theorem cells_le_first {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) {s S : ℝ}
    (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5) (hsS : s ≤ S)
    (hr : 2 ≤ S - S / s) (hcell : S - 2 ≤ upperNode 0) :
    cells z S ≤ firstFeedback z s S := by
  have he := cells_le_eProfile hz hS hcell
  have hj := profileJ_nonneg hz hs hS hS5 hsS hr
  unfold firstFeedback
  linarith only [he, hj]

theorem cells_le_coupled {p : SecondFunctionalParameters} (hp : CoupledGeometry p)
    (hc : p.kappa1 - 2 ≤ upperNode 0) {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) :
    cells z p.kappa1 / 5 ≤ coupledFeedback p z := by
  have hg := coupled_geometry_bounds hp
  have he := (profiles_nonneg (fun t _ => nineProfile_nonneg hz t)).2.2
  have h0 := he p.S ⟨hp.1.three_le_S, hp.1.S_le_five⟩
  have h1 := cells_le_eProfile hz hp.2.1 hc
  have hj0 := profileJ_nonneg hz hg.1 hp.1.three_le_S hp.1.S_le_five hg.2.1 hp.2.2.1
  have hj2 := profileJ_nonneg hz hg.2.2.1 hp.1.three_le_S hp.1.S_le_five hg.2.2.2.1 hp.2.2.2.1
  have hj3 := profileJ_nonneg hz hg.2.2.2.2.1 hp.1.three_le_S hp.1.S_le_five
    hg.2.2.2.2.2.1 hp.2.2.2.2
  have hd := densityMoment_nonneg p hp.1 hz
  unfold coupledFeedback
  linarith only [h0, h1, hj0, hj2, hj3, hd]

theorem coupled_kappa_cell (i : Fin 4) : (coupledRow i).kappa1 - 2 ≤ upperNode 0 := by
  fin_cases i <;>
    norm_num [coupledRow, SecondFunctionalPositive.parameters, SecondFunctionalParameters.row1,
      SecondFunctionalParameters.row2, SecondFunctionalParameters.row3,
      SecondFunctionalParameters.row4, upperNode]

theorem first_cell (i : Fin 5) : firstS i - 2 ≤ upperNode 0 := by
  fin_cases i <;> norm_num [firstS, upperNode]

def elementaryMatrix (i k : Fin 9) : ℝ :=
  if h : i.val < 4 then
    cell (coupledRow ⟨i.val, h⟩).kappa1
      (cellLeft ((coupledRow ⟨i.val, h⟩).kappa1 - 2) k) (upperNode k) / 5
  else
    cell (firstS ⟨i.val - 4, by omega⟩)
      (cellLeft (firstS ⟨i.val - 4, by omega⟩ - 2) k) (upperNode k)

/-- All 81 genuine entries are lower bounded, with no printed-matrix identification. -/
theorem elementaryMatrix_le (i k : Fin 9) : elementaryMatrix i k ≤ feedbackMatrix i k := by
  unfold elementaryMatrix feedbackMatrix feedback
  split_ifs with h
  · have hh := cells_le_coupled (coupledRow_geometry ⟨i.val, h⟩)
      (coupled_kappa_cell ⟨i.val, h⟩) (nodeBasis_nonneg k)
    simpa only [cells_basis] using hh
  · let j : Fin 5 := ⟨i.val - 4, by omega⟩
    have hg := first_geometry j
    have hh := cells_le_first (nodeBasis_nonneg k) hg.1 hg.2.2.1 hg.2.2.2.1
      (hg.2.1.trans hg.2.2.1) hg.2.2.2.2 (first_cell j)
    simpa only [cells_basis] using hh

end Wu04Bypass
