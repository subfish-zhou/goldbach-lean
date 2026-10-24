import WR2XiPublicationPaid
import WR2XiCorrectedActual

/-! Original publication baselines with the exact nonnegative corrected Xi2 matrix. -/
noncomputable section
namespace WuPaper.R2Xi
open NodeExtension Wu2008DoubleSieve MotherPair
open scoped BigOperators

theorem Xi2_publication_corrected (r : Fin 4) {δ : ℝ} (hd : 0 < δ)
    (hr : δ ≤ Wu04RemainingStrongFourRows.commonRadius) :
    secondPublication r + (∑ k : Fin 9, Xi2CorrectedCoefficient r k * actualNine δ k) ≤
      wuImprovementLimit true δ (gamma5OriginalRow r).s := by
  have hh : δ ≤ 1/10 := hr.trans ((min_le_left _ _).trans (min_le_left _ _))
  have h := Xi2_four_rows_corrected_matrix r hd hh
  have hb := secondPublication_baseline r hd hr
  linarith only [h,hb]

end WuPaper.R2Xi
