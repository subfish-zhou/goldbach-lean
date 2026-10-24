import WR2XiPieceRegularity
import WR2XiSigmaCell

/-! Unconditional original four-row cell decomposition, ready for numerical panel bounds. -/
noncomputable section
namespace WuPaper.R2Xi
open Real MeasureTheory Wu2008DoubleSieve MotherPair NodeExtension
open scoped Interval BigOperators

theorem original_Xi2Coefficient_eq_clipped (r : Fin 4) (k : Fin 9) :
    Xi2Coefficient (gamma5OriginalRow r) k =
      (log (1024 / xi2ParameterProduct (gamma5OriginalRow r)) / 5) *
        aProfile (nineProfile (nodeBasis k)) +
      ∑ j : Fin 9, clippedIntegral (fun t => xi2PieceKernel (gamma5OriginalRow r) t j)
        (upperLeft k) (upperNode k)
        (xi2PieceInterval (gamma5OriginalRow r) j).1
        (xi2PieceInterval (gamma5OriginalRow r) j).2 := by
  rw [Xi2Coefficient_eq_clipped _ _ (xi2Sigma_cell_integrable _ _)
    (fun j => (original_piece_integrable r j).intervalIntegrable), xi2Sigma_cell_eq]

end WuPaper.R2Xi
#print axioms WuPaper.R2Xi.original_Xi2Coefficient_eq_clipped
