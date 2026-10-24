import WR2XiTightCell
import WR2XiPieceRegularity
import WR2XiSigmaBudget
import WR2XiProductUniform

/-! The exact tight cell consumes a sigma bound and a proved uniform integral payment. -/
noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory Wu2008DoubleSieve MotherPair SecondFunctionalParameters NodeExtension
open WuPaper.RMapMMatrix
open scoped Interval BigOperators

private theorem left_five : upperLeft (5:Fin 9) = 13/5 := by norm_num [upperLeft]
private theorem right_five : upperNode (5:Fin 9) = 27/10 := by norm_num [upperNode]

theorem tight_top_integrable : IntervalIntegrable
    (fun t => log ((t + 1)^5 / xi2ParameterProduct row2) / (5*t)) volume (13/5) (27/10) := by
  have h := (original_piece_integrable (1:Fin 4) (0:Fin 9)).intervalIntegrable
    (a := 13/5) (b := 27/10)
  apply h.congr
  intro t ht
  have ht' : t ∈ Icc (13/5:ℝ) (27/10) := by
    simpa only [uIcc_of_le (by norm_num : (13/5:ℝ) ≤ 27/10)] using (uIoc_subset_uIcc ht)
  change xi2Piece row2 0 t = _
  have hm : t ∈ Icc (xi2PieceInterval row2 0).1 (xi2PieceInterval row2 0).2 := by
    norm_num [xi2PieceInterval, row2, alpha2]
    constructor <;> linarith [ht'.1, ht'.2]
  rw [xi2Piece, indicator_of_mem hm]
  rfl

theorem tight_coefficient_integral : Xi2Coefficient row2 5 =
    (∫ t in (13/5:ℝ)..(27/10), xi2SigmaKernel row2 t) +
    ∫ t in (13/5:ℝ)..(27/10), log ((t + 1)^5 / xi2ParameterProduct row2) / (5*t) := by
  rw [Xi2Coefficient_eq_cell, left_five, right_five]
  have hs : IntervalIntegrable (xi2SigmaKernel row2) volume (13/5) (27/10) := by
    simpa only [left_five, right_five] using xi2Sigma_cell_integrable row2 5
  rw [← intervalIntegral.integral_add hs tight_top_integrable]
  apply intervalIntegral.integral_congr
  intro t ht
  apply second_row_tight_cell_kernel
  simpa only [uIcc_of_le (by norm_num : (13/5:ℝ) ≤ 27/10)] using ht

theorem tight_cell_uniform_lower {N : ℕ} (hN : 0 < N) {A : ℝ}
    (hA : 0 ≤ A) (hbound : A ≤ aProfile (nineProfile (nodeBasis 5))) :
    xi2SigmaScalarLower row2 * A +
      (∑ k ∈ Finset.range N, productPanelPayment (xi2Factors row2) (13/5) (27/10) N k) ≤
      Xi2Coefficient row2 5 := by
  have hs := xi2Sigma_cell_lower (1:Fin 4) (5:Fin 9) hA hbound
  change xi2SigmaScalarLower row2 * A ≤ _ at hs
  rw [left_five, right_five] at hs
  have hq (j : Fin 5) : 0 < xi2Factors row2 j ∧ xi2Factors row2 j ≤ (13/5:ℝ) + 1 := by
    fin_cases j <;> norm_num [xi2Factors, row2]
  have hi : IntervalIntegrable
      (fun t => log ((t + 1)^5 / ∏ j, xi2Factors row2 j) / (5*t)) volume (13/5) (27/10) := by
    simpa only [xi2Factors_prod] using tight_top_integrable
  have hp := product_uniform_lower (by norm_num : (0:ℝ) < 13/5)
    (by norm_num : (13/5:ℝ) ≤ 27/10) hN hq hi
  rw [xi2Factors_prod] at hp
  rw [tight_coefficient_integral]
  exact add_le_add hs hp

end WuPaper.R2Xi
#print axioms WuPaper.R2Xi.tight_cell_uniform_lower
