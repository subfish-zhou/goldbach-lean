import WR2XiRationalTightArithmetic
import WR2XiRationalLog
import WR2XiTightIntegral

/-! The 512-panel kernel computation feeds the original tight matrix entry. -/
noncomputable section
namespace Xi2RationalCheck
open WuPaper.R2Xi Wu2008DoubleSieve SecondFunctionalParameters NodeExtension
open scoped BigOperators

private theorem refined_cast (x : ℚ) : (refined x : ℝ) = cellLogLower (x : ℝ) :=
  rationalCellLog_cast x

private theorem factors_cast (j : Fin 5) : (factors j : ℝ) = xi2Factors row2 j := by
  fin_cases j <;> norm_num [factors, xi2Factors, row2]

private theorem endpoint_cast (m : ℕ) :
    (endpoint m : ℝ) = panelPoint (13/5) (27/10) 512 m := by
  unfold endpoint panelPoint
  push_cast
  ring

private theorem scalar_cast : (scalar : ℝ) = xi2SigmaScalarLower row2 := by
  unfold scalar xi2SigmaScalarLower productLogLower
  push_cast
  simp_rw [refined_cast]
  push_cast
  simp_rw [factors_cast]
  norm_num

private theorem payment_cast (m : ℕ) :
    (payment m : ℝ) = productPanelPayment (xi2Factors row2) (13/5) (27/10) 512 m := by
  unfold payment productPanelPayment
  push_cast
  simp_rw [refined_cast]
  push_cast
  simp_rw [factors_cast, endpoint_cast]
  rw [panelPoint_step]
  unfold productLogLower
  ring

private theorem tightEntry_cast : (tightEntry : ℝ) =
    xi2SigmaScalarLower row2 * (sigmaCoeff : ℝ) +
      ∑ m ∈ Finset.range 512, productPanelPayment (xi2Factors row2) (13/5) (27/10) 512 m := by
  unfold tightEntry
  push_cast
  rw [scalar_cast]
  simp_rw [payment_cast]
  ring

/-- Only the shared analytic sigma bound remains explicit. -/
theorem tight_original_entry
    (hsigma : (sigmaCoeff : ℝ) ≤ aProfile (nineProfile (nodeBasis 5))) :
    (27/1000 : ℝ) ≤ Xi2Coefficient row2 5 := by
  have har : (27/1000 : ℝ) ≤ (tightEntry : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr tight_arithmetic
  rw [tightEntry_cast] at har
  have hpos : 0 ≤ (sigmaCoeff : ℝ) := by norm_num [sigmaCoeff]
  exact har.trans (tight_cell_uniform_lower (by norm_num : 0 < 512) hpos hsigma)

end Xi2RationalCheck
#print axioms Xi2RationalCheck.tight_original_entry
