import WR2XiPieces

/-! The tight second-row sixth-cell certificate lies entirely in the top logarithmic piece. -/
noncomputable section
namespace WuPaper.R2Xi
open Real Set Wu2008DoubleSieve SecondFunctionalParameters
open WuPaper.RMapMMatrix
open scoped BigOperators

private theorem second_row_other_right (j : Fin 9) (hj : j ≠ 0) :
    (xi2PieceInterval row2 j).2 ≤ 5/2 := by
  fin_cases j <;> norm_num [xi2PieceInterval, row2, alpha1, alpha2, alpha3,
    alpha5, alpha6, alpha7, alpha8, alpha9] at *

theorem second_row_tight_cell_kernel {t : ℝ} (ht : t ∈ Icc (13/5) (27/10)) :
    Xi2 row2 t = xi2SigmaKernel row2 t +
      log ((t + 1)^5 / xi2ParameterProduct row2) / (5*t) := by
  rw [Xi2_eq_pieces]
  have hs : (∑ j : Fin 9, xi2Piece row2 j t) = xi2Piece row2 0 t := by
    apply Finset.sum_eq_single 0
    · intro j _ hj
      have hr := second_row_other_right j hj
      apply indicator_of_notMem
      intro hm
      have hb := hm.2
      linarith [ht.1]
    · simp
  rw [hs]
  have hmem : t ∈ Icc (xi2PieceInterval row2 0).1 (xi2PieceInterval row2 0).2 := by
    norm_num [xi2PieceInterval, row2, alpha2]
    constructor <;> linarith [ht.1, ht.2]
  rw [xi2Piece, indicator_of_mem hmem]
  rfl

end WuPaper.R2Xi
#print axioms WuPaper.R2Xi.second_row_tight_cell_kernel
