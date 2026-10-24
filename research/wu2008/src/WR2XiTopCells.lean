import WR2XiPieceRegularity
import WR2XiSigmaBudget
import WR2XiProductUniform

/-! All original cells above S-2 share one product-log integral formula. -/
noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory Wu2008DoubleSieve MotherPair SecondFunctionalParameters NodeExtension
open WuPaper.RMapMMatrix
open scoped Interval BigOperators

private theorem original_other_right (r : Fin 4) (j : Fin 9) (hj : j ≠ 0) :
    (xi2PieceInterval (gamma5OriginalRow r) j).2 ≤ (gamma5OriginalRow r).S - 2 := by
  fin_cases r <;> fin_cases j <;>
    norm_num [xi2PieceInterval, gamma5OriginalRow, row1, row2, row3, row4,
      alpha1, alpha2, alpha3, alpha5, alpha6, alpha7, alpha8, alpha9] at *

theorem original_top_cell_kernel (r : Fin 4) {t : ℝ}
    (hl : (gamma5OriginalRow r).S - 2 < t) (hu : t ≤ 3) :
    Xi2 (gamma5OriginalRow r) t = xi2SigmaKernel (gamma5OriginalRow r) t +
      xi2PieceKernel (gamma5OriginalRow r) t 0 := by
  rw [Xi2_eq_pieces]
  have hs : (∑ j : Fin 9, xi2Piece (gamma5OriginalRow r) j t) =
      xi2Piece (gamma5OriginalRow r) 0 t := by
    apply Finset.sum_eq_single 0
    · intro j _ hj
      have hr := original_other_right r j hj
      apply indicator_of_notMem
      intro hm
      linarith [hm.2]
    · simp
  rw [hs, xi2Piece, indicator_of_mem]
  change t ∈ Icc ((gamma5OriginalRow r).S - 2) 3
  exact ⟨hl.le, hu⟩

private theorem node_cell_bounds (k : Fin 9) :
    1 ≤ upperLeft k ∧ upperLeft k ≤ upperNode k ∧ upperNode k ≤ 3 := by
  fin_cases k <;> norm_num [upperLeft, upperNode]

theorem top_cell_piece_integrable (r : Fin 4) (k : Fin 9)
    (hcell : (gamma5OriginalRow r).S - 2 ≤ upperLeft k) :
    IntervalIntegrable (fun t => xi2PieceKernel (gamma5OriginalRow r) t 0)
      volume (upperLeft k) (upperNode k) := by
  have hb := node_cell_bounds k
  apply ((original_piece_integrable r 0).intervalIntegrable
    (a := upperLeft k) (b := upperNode k)).congr
  intro t ht
  have ht' : t ∈ Ioc (upperLeft k) (upperNode k) := by
    simpa only [uIoc_of_le hb.2.1] using ht
  rw [xi2Piece, indicator_of_mem]
  change t ∈ Icc ((gamma5OriginalRow r).S - 2) 3
  exact ⟨hcell.trans ht'.1.le, ht'.2.trans hb.2.2⟩

theorem top_cell_coefficient_integral (r : Fin 4) (k : Fin 9)
    (hcell : (gamma5OriginalRow r).S - 2 ≤ upperLeft k) :
    Xi2Coefficient (gamma5OriginalRow r) k =
      (∫ t in upperLeft k..upperNode k, xi2SigmaKernel (gamma5OriginalRow r) t) +
      ∫ t in upperLeft k..upperNode k, xi2PieceKernel (gamma5OriginalRow r) t 0 := by
  have hb := node_cell_bounds k
  rw [Xi2Coefficient_eq_cell, ← intervalIntegral.integral_add
    (xi2Sigma_cell_integrable _ _) (top_cell_piece_integrable r k hcell)]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with t ht
  have ht' : t ∈ Ioc (upperLeft k) (upperNode k) := by
    simpa only [uIoc_of_le hb.2.1] using ht
  exact original_top_cell_kernel r (hcell.trans_lt ht'.1) (ht'.2.trans hb.2.2)

end WuPaper.R2Xi
#print axioms WuPaper.R2Xi.top_cell_coefficient_integral
