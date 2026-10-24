import WR2XiTopCertificate
import WR2XiTightCorrected

/-! All twenty-two top-cell estimates feed the original corrected nine-row matrix. -/
noncomputable section
namespace Xi2RationalTop
open WuPaper.R2Xi WuPaper.R2Xi.RationalCandidate NodeExtension

private theorem target_cast (r : Fin 4) (k : Fin 9) :
    (target r k : ℝ) = lowerMatrix (r.castAdd 5) k := by
  fin_cases r <;> fin_cases k <;> norm_num [target, lowerMatrix, Fin.castAdd, Fin.castLE, Matrix.cons_val]

private theorem top_column_ne_zero (r : Fin 4) (k : Fin 9)
    (hcell : factors r 1 - 1 ≤ left k) : k ≠ 0 := by
  intro hk
  subst k
  fin_cases r <;> norm_num [factors, left, Matrix.cons_val] at hcell

theorem other_top_corrected_entry (r : Fin 4) (k : Fin 9)
    (hnot : ¬(r = 1 ∧ k = 5)) (hcell : factors r 1 - 1 ≤ left k)
    (hsigma : (sigmaCoeff k : ℝ) ≤ aProfile (nineProfile (nodeBasis k))) :
    lowerMatrix (r.castAdd 5) k ≤ correctedNineMatrix (r.castAdd 5) k := by
  rw [← target_cast r k]
  simp only [correctedNineMatrix, Fin.addCases_left, Xi2CorrectedCoefficient,
    if_neg (top_column_ne_zero r k hcell), sub_zero]
  exact other_top_original_entry r k hnot hcell hsigma

theorem top_corrected_entry (r : Fin 4) (k : Fin 9)
    (hcell : factors r 1 - 1 ≤ left k)
    (hsigma : (sigmaCoeff k : ℝ) ≤ aProfile (nineProfile (nodeBasis k))) :
    lowerMatrix (r.castAdd 5) k ≤ correctedNineMatrix (r.castAdd 5) k := by
  by_cases h : r = 1 ∧ k = 5
  · rcases h with ⟨rfl, rfl⟩
    apply tight_corrected_entry
    simpa only [sigmaCoeff, massLower, Xi2RationalCheck.sigmaCoeff, Matrix.cons_val] using hsigma
  · exact other_top_corrected_entry r k h hcell hsigma

end Xi2RationalTop
#print axioms Xi2RationalTop.top_corrected_entry
