import WR2XiSigmaCell
import WR2XiProductPanels

/-! A rational lower bound for the common sigma coefficient of each original row. -/
noncomputable section
namespace WuPaper.R2Xi
open Real Wu2008DoubleSieve MotherPair SecondFunctionalParameters NodeExtension
open scoped BigOperators Interval

def xi2Factors (p : SecondFunctionalParameters) : Fin 5 → ℝ :=
  ![p.s - 1, p.S - 1, p.kappa1 - 1, p.kappa2 - 1, p.kappa3 - 1]

def xi2SigmaScalarLower (p : SecondFunctionalParameters) : ℝ :=
  productLogLower (xi2Factors p) 3 / 5

theorem xi2Factors_bounds (r : Fin 4) (j : Fin 5) :
    0 < xi2Factors (gamma5OriginalRow r) j ∧ xi2Factors (gamma5OriginalRow r) j ≤ 4 := by
  fin_cases r <;> fin_cases j <;>
    norm_num [xi2Factors, gamma5OriginalRow, row1, row2, row3, row4]

theorem xi2Factors_prod (p : SecondFunctionalParameters) :
    (∏ j : Fin 5, xi2Factors p j) = xi2ParameterProduct p := by
  simp [xi2Factors, xi2ParameterProduct, Fin.prod_univ_succ]
  ring

theorem xi2SigmaScalarLower_nonneg (r : Fin 4) :
    0 ≤ xi2SigmaScalarLower (gamma5OriginalRow r) := by
  apply div_nonneg _ (by norm_num)
  apply productLogLower_nonneg
  intro j
  simpa only [show (3 : ℝ) + 1 = 4 by norm_num] using xi2Factors_bounds r j

theorem xi2SigmaScalarLower_le (r : Fin 4) :
    xi2SigmaScalarLower (gamma5OriginalRow r) ≤
      log (1024 / xi2ParameterProduct (gamma5OriginalRow r)) / 5 := by
  have h := productLogLower_le (q := xi2Factors (gamma5OriginalRow r))
    (a := 3) (t := 3) (by norm_num) le_rfl (fun j => by simpa only [show (3 : ℝ) + 1 = 4 by norm_num] using xi2Factors_bounds r j)
  rw [xi2Factors_prod] at h
  norm_num only [show (3 + 1 : ℝ)^5 = 1024 by norm_num] at h
  exact div_le_div_of_nonneg_right h (by norm_num)

/-- Consumes any proved aProfile lower bound without duplicating its sigma integral. -/
theorem xi2Sigma_cell_lower (r : Fin 4) (k : Fin 9) {A : ℝ}
    (hA : 0 ≤ A) (hbound : A ≤ aProfile (nineProfile (nodeBasis k))) :
    xi2SigmaScalarLower (gamma5OriginalRow r) * A ≤
      ∫ t in upperLeft k..upperNode k, xi2SigmaKernel (gamma5OriginalRow r) t := by
  rw [xi2Sigma_cell_eq]
  have hc := xi2SigmaScalarLower_le r
  have hc0 := (xi2SigmaScalarLower_nonneg r).trans hc
  exact (mul_le_mul_of_nonneg_right hc hA).trans
    (mul_le_mul_of_nonneg_left hbound hc0)

end WuPaper.R2Xi
#print axioms WuPaper.R2Xi.xi2Sigma_cell_lower
