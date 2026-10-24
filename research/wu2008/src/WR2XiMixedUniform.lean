import WR2XiOriginalPanelAssembly
import WR2XiOriginalCellAssembly

/-! The complete original coefficient lower bound from finite clipped panel sums. -/
noncomputable section
namespace WuPaper.R2Xi
open Real Wu2008DoubleSieve MotherPair NodeExtension
open scoped BigOperators

theorem original_cell_uniform_lower (r : Fin 4) (k : Fin 9) {N : ℕ} (hN : 0 < N)
    {A : ℝ} (hA : 0 ≤ A) (hbound : A ≤ aProfile (nineProfile (nodeBasis k))) :
    xi2SigmaScalarLower (gamma5OriginalRow r) * A +
      ∑ j : Fin 9, originalPieceLower r k j N ≤ Xi2Coefficient (gamma5OriginalRow r) k := by
  rw [original_Xi2Coefficient_eq_clipped]
  apply add_le_add
  · have h := xi2Sigma_cell_lower r k hA hbound
    rwa [xi2Sigma_cell_eq] at h
  · exact Finset.sum_le_sum (fun j _ => original_piece_lower r k j hN)

end WuPaper.R2Xi
#print axioms WuPaper.R2Xi.original_cell_uniform_lower
