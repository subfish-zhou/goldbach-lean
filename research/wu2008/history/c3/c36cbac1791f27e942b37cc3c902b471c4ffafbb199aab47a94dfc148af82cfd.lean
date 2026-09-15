import W04ClippedCells
import Wu04BypassActual

noncomputable section
namespace WuTarget.W04
open Real Set MeasureTheory NodeExtension ActualNineFeedback Wu2008DoubleSieve
open scoped Interval BigOperators

def coupledExtra (i : Fin 4) (k : Fin 9) : ℝ :=
  4 * clippedCell (coupledRow i).S k / 5

def extraMatrix (i k : Fin 9) : ℝ :=
  if h : i.val < 4 then coupledExtra ⟨i.val, h⟩ k else 0

def augmentedMatrix (i k : Fin 9) : ℝ :=
  Wu04Bypass.M i k + extraMatrix i k

theorem coupledExtra_nonneg (i : Fin 4) (k : Fin 9) : 0 ≤ coupledExtra i k := by
  unfold coupledExtra
  exact div_nonneg (mul_nonneg (by norm_num) (clippedCell_nonneg _ k)) (by norm_num)

theorem extraMatrix_nonneg (i k : Fin 9) : 0 ≤ extraMatrix i k := by
  unfold extraMatrix
  split_ifs
  · exact coupledExtra_nonneg _ k
  · exact le_rfl

theorem coupledExtra_le_kernel (i : Fin 4) (k : Fin 9) :
    coupledExtra i k ≤ 4 * eKernel (coupledRow i).S k / 5 := by
  have h := clippedCell_le_eKernel (coupledRow_geometry i).1.three_le_S
    (coupledRow_geometry i).1.S_le_five k
  unfold coupledExtra
  linarith only [h]

theorem old_cells_add_extra_le_coupled {p : SecondFunctionalParameters}
    (hp : CoupledGeometry p) (hc : p.kappa1 - 2 ≤ upperNode 0) (k : Fin 9) :
    Wu04Bypass.cells (nodeBasis k) p.kappa1 / 5 + 4 * clippedCell p.S k / 5 ≤
      coupledFeedback p (nodeBasis k) := by
  have hg := coupled_geometry_bounds hp
  have h0 := clippedCell_le_eProfile hp.1.three_le_S hp.1.S_le_five k
  have h1 := Wu04Bypass.cells_le_eProfile (nodeBasis_nonneg k) hp.2.1 hc
  have hj0 := profileJ_nonneg (nodeBasis_nonneg k) hg.1 hp.1.three_le_S
    hp.1.S_le_five hg.2.1 hp.2.2.1
  have hj2 := profileJ_nonneg (nodeBasis_nonneg k) hg.2.2.1 hp.1.three_le_S
    hp.1.S_le_five hg.2.2.2.1 hp.2.2.2.1
  have hj3 := profileJ_nonneg (nodeBasis_nonneg k) hg.2.2.2.2.1 hp.1.three_le_S
    hp.1.S_le_five hg.2.2.2.2.2.1 hp.2.2.2.2
  have hd := densityMoment_nonneg p hp.1 (nodeBasis_nonneg k)
  unfold coupledFeedback
  linarith only [h0, h1, hj0, hj2, hj3, hd]

theorem elementary_add_extra_le_feedbackMatrix (i k : Fin 9) :
    Wu04Bypass.elementaryMatrix i k + extraMatrix i k ≤ feedbackMatrix i k := by
  by_cases h : i.val < 4
  · have hp := old_cells_add_extra_le_coupled (coupledRow_geometry ⟨i.val, h⟩)
      (Wu04Bypass.coupled_kappa_cell ⟨i.val, h⟩) k
    simpa only [Wu04Bypass.elementaryMatrix, extraMatrix, coupledExtra,
      feedbackMatrix, feedback, dif_pos h, Wu04Bypass.cells_basis] using hp
  · simpa only [extraMatrix, dif_neg h, add_zero] using
      (Wu04Bypass.elementaryMatrix_le i k)

theorem oldMatrix_le_elementary (i k : Fin 9) :
    Wu04Bypass.M i k ≤ Wu04Bypass.elementaryMatrix i k := by
  fin_cases i
  · exact Wu04Bypass.matrix_row0 k
  · exact Wu04Bypass.matrix_row1 k
  · exact Wu04Bypass.matrix_row2 k
  · exact Wu04Bypass.matrix_row3 k
  · exact Wu04Bypass.matrix_row4 k
  · exact Wu04Bypass.matrix_row5 k
  · exact Wu04Bypass.matrix_row6 k
  · exact Wu04Bypass.matrix_row7 k
  · exact Wu04Bypass.matrix_row8 k

theorem augmentedMatrix_le_feedbackMatrix (i k : Fin 9) :
    augmentedMatrix i k ≤ feedbackMatrix i k :=
  (add_le_add_right (oldMatrix_le_elementary i k) (extraMatrix i k)).trans
    (elementary_add_extra_le_feedbackMatrix i k)

theorem oldMatrix_le_augmentedMatrix (i k : Fin 9) :
    Wu04Bypass.M i k ≤ augmentedMatrix i k :=
  le_add_of_nonneg_right (extraMatrix_nonneg i k)

theorem augmentedMatrix_eq_old_of_first (i k : Fin 9) (hi : 4 ≤ i.val) :
    augmentedMatrix i k = Wu04Bypass.M i k := by
  simp [augmentedMatrix, extraMatrix, show ¬i.val < 4 by omega]

theorem augmented_apply_le_feedback {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k)
    (i : Fin 9) :
    matrixApply augmentedMatrix z i ≤ matrixApply feedbackMatrix z i :=
  Finset.sum_le_sum (fun k _ =>
    mul_le_mul_of_nonneg_right (augmentedMatrix_le_feedbackMatrix i k) (hz k))

theorem actual_augmented_system {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 10)
    (i : Fin 9) :
    base i - deltaLoss δ * loss i +
      matrixApply augmentedMatrix (actualNine δ) i ≤ actualNine δ i := by
  have hm := augmented_apply_le_feedback (actualNine_nonneg hd hh) i
  have ha := actual_feedback hd hh i
  rw [feedback_expansion] at ha
  exact (add_le_add_left hm _).trans ha

theorem augmented_same_delta :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 10 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d → ∀ i : Fin 9,
        Wu04Bypass.v0 i + matrixApply augmentedMatrix (actualNine δ) i ≤
          actualNine δ i := by
  obtain ⟨d, hd, hcap, hs⟩ := NineFeedbackStrength.actual_same_delta
  refine ⟨d, hd, hcap, ?_⟩
  intro δ hδ hr i
  rw [Wu04Bypass.v0_eq_publication]
  exact (add_le_add_left
    (augmented_apply_le_feedback (actualNine_nonneg hδ (hr.trans hcap)) i) _).trans
      (hs δ hδ hr i)

theorem augmented_paid_update {δ : ℝ}
    (hs : ∀ i, NineFeedbackStrength.publication i +
      matrixApply feedbackMatrix (actualNine δ) i ≤ actualNine δ i)
    {x y : Fin 9 → ℝ} (hx : ∀ k, x k ≤ actualNine δ k)
    (hn : ∀ k, 0 ≤ x k)
    (hy : ∀ i, y i ≤ Wu04Bypass.v0 i + matrixApply augmentedMatrix x i) :
    ∀ i, y i ≤ actualNine δ i := by
  intro i
  have hm := augmented_apply_le_feedback hn i
  have ha := matrixApply_mono feedbackMatrix_nonneg hx i
  have hh := hs i
  rw [← Wu04Bypass.v0_eq_publication] at hh
  linarith only [hy i, hm, ha, hh]

end WuTarget.W04
