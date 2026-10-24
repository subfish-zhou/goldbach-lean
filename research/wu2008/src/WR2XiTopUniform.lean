import WR2XiTopCells

/-! One analytic consumer for all twenty-two original top-cell certificates. -/
noncomputable section
namespace WuPaper.R2Xi
open Real MeasureTheory Wu2008DoubleSieve MotherPair SecondFunctionalParameters NodeExtension
open scoped Interval BigOperators

private theorem factors_le_scale (r : Fin 4) (j : Fin 5) :
    xi2Factors (gamma5OriginalRow r) j ≤ (gamma5OriginalRow r).S - 1 := by
  fin_cases r <;> fin_cases j <;>
    norm_num [xi2Factors, gamma5OriginalRow, row1, row2, row3, row4]

theorem top_cell_uniform_lower (r : Fin 4) (k : Fin 9)
    (hcell : (gamma5OriginalRow r).S - 2 ≤ upperLeft k)
    {N : ℕ} (hN : 0 < N) {A : ℝ}
    (hA : 0 ≤ A) (hbound : A ≤ aProfile (nineProfile (nodeBasis k))) :
    xi2SigmaScalarLower (gamma5OriginalRow r) * A +
      (∑ m ∈ Finset.range N, productPanelPayment (xi2Factors (gamma5OriginalRow r))
        (upperLeft k) (upperNode k) N m) ≤ Xi2Coefficient (gamma5OriginalRow r) k := by
  have hb : 0 < upperLeft k ∧ upperLeft k ≤ upperNode k := by
    fin_cases k <;> norm_num [upperLeft, upperNode]
  have hq (j : Fin 5) : 0 < xi2Factors (gamma5OriginalRow r) j ∧
      xi2Factors (gamma5OriginalRow r) j ≤ upperLeft k + 1 := by
    exact ⟨(xi2Factors_bounds r j).1, (factors_le_scale r j).trans (by linarith)⟩
  have hi := top_cell_piece_integrable r k hcell
  change IntervalIntegrable (fun t => log ((t+1)^5 / xi2ParameterProduct (gamma5OriginalRow r)) /
    (5*t)) volume (upperLeft k) (upperNode k) at hi
  have hip : IntervalIntegrable
      (fun t => log ((t+1)^5 / ∏ j, xi2Factors (gamma5OriginalRow r) j) / (5*t))
      volume (upperLeft k) (upperNode k) := by
    simpa only [xi2Factors_prod] using hi
  have hp := product_uniform_lower hb.1 hb.2 hN hq hip
  rw [xi2Factors_prod] at hp
  rw [top_cell_coefficient_integral r k hcell]
  exact add_le_add (xi2Sigma_cell_lower r k hA hbound) hp

end WuPaper.R2Xi
#print axioms WuPaper.R2Xi.top_cell_uniform_lower
