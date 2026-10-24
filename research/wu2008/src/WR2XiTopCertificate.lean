import WR2XiRationalTopArithmetic
import WR2XiRationalLog
import WR2XiTopUniform
import WR2XiRationalCandidate

/-! The remaining top-cell rational computations feed the original corrected matrix. -/
noncomputable section
namespace Xi2RationalTop
open WuPaper.R2Xi WuPaper.R2Xi.RationalCandidate
open Wu2008DoubleSieve MotherPair SecondFunctionalParameters NodeExtension
open scoped BigOperators

private theorem refined_cast (x : ℚ) : (Xi2RationalCheck.refined x : ℝ) = cellLogLower (x : ℝ) :=
  rationalCellLog_cast x

private theorem factors_cast (r : Fin 4) (j : Fin 5) :
    (factors r j : ℝ) = xi2Factors (gamma5OriginalRow r) j := by
  fin_cases r <;> fin_cases j <;>
    norm_num [factors, xi2Factors, gamma5OriginalRow, row1, row2, row3, row4]

private theorem left_cast (k : Fin 9) : (left k : ℝ) = upperLeft k := by
  fin_cases k <;> norm_num [left, upperLeft]

private theorem right_cast (k : Fin 9) : (right k : ℝ) = upperNode k := by
  unfold right upperNode
  push_cast
  rfl

private theorem count_pos (r : Fin 4) (k : Fin 9) : 0 < count r k := by
  unfold count
  split_ifs <;> norm_num

private theorem endpoint_cast (r : Fin 4) (k : Fin 9) (m : ℕ) :
    (endpoint r k m : ℝ) = panelPoint (upperLeft k) (upperNode k) (count r k) m := by
  unfold endpoint panelPoint
  push_cast
  rw [left_cast, right_cast]

private theorem scalar_cast (r : Fin 4) :
    (scalar r : ℝ) = xi2SigmaScalarLower (gamma5OriginalRow r) := by
  unfold scalar xi2SigmaScalarLower productLogLower
  push_cast
  simp_rw [refined_cast]
  push_cast
  simp_rw [factors_cast]
  norm_num

private theorem payment_cast (r : Fin 4) (k : Fin 9) (m : ℕ) :
    (payment r k m : ℝ) = productPanelPayment (xi2Factors (gamma5OriginalRow r))
      (upperLeft k) (upperNode k) (count r k) m := by
  unfold payment productPanelPayment
  push_cast
  simp_rw [refined_cast]
  push_cast
  simp_rw [factors_cast, endpoint_cast]
  rw [panelPoint_step]
  unfold productLogLower
  ring

private theorem entry_cast (r : Fin 4) (k : Fin 9) : (entry r k : ℝ) =
    xi2SigmaScalarLower (gamma5OriginalRow r) * (sigmaCoeff k : ℝ) +
      ∑ m ∈ Finset.range (count r k), productPanelPayment (xi2Factors (gamma5OriginalRow r))
        (upperLeft k) (upperNode k) (count r k) m := by
  unfold entry
  push_cast
  rw [scalar_cast]
  simp_rw [payment_cast]
  ring

private theorem cell_condition_cast (r : Fin 4) (k : Fin 9)
    (hcell : factors r 1 - 1 ≤ left k) : (gamma5OriginalRow r).S - 2 ≤ upperLeft k := by
  have h := (Rat.cast_le (K := ℝ)).mpr hcell
  simp only [Rat.cast_sub, Rat.cast_one, factors_cast, left_cast] at h
  change ((gamma5OriginalRow r).S - 1) - 1 ≤ upperLeft k at h
  linarith

theorem other_top_original_entry (r : Fin 4) (k : Fin 9)
    (hnot : ¬(r = 1 ∧ k = 5)) (hcell : factors r 1 - 1 ≤ left k)
    (hsigma : (sigmaCoeff k : ℝ) ≤ aProfile (nineProfile (nodeBasis k))) :
    (target r k : ℝ) ≤ Xi2Coefficient (gamma5OriginalRow r) k := by
  have har := (Rat.cast_le (K := ℝ)).mpr (other_top_arithmetic r k hnot hcell)
  rw [entry_cast] at har
  have hpos : 0 ≤ (sigmaCoeff k : ℝ) := by
    fin_cases k <;> norm_num [sigmaCoeff, massLower]
  exact har.trans (top_cell_uniform_lower r k (cell_condition_cast r k hcell)
    (count_pos r k) hpos hsigma)

end Xi2RationalTop
#print axioms Xi2RationalTop.other_top_original_entry
