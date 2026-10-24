import WR2XiMixedPanelCasts
import WR2XiTopCorrected
import WR2XiCoefficientBudget

/-! Consume a rational mixed-cell certificate, including the first-column Gamma5 debit. -/
noncomputable section
namespace Xi2RationalMixed
open Xi2RationalTop (factors left right sigmaCoeff scalar target)
open WuPaper.R2Xi WuPaper.R2Xi.RationalCandidate
open Wu2008DoubleSieve MotherPair NodeExtension
open Wu2004MeanValue.GammaFiveLossBudget
open scoped BigOperators

theorem debit_cast (r : Fin 4) : (debit r : ℝ) = rowDebit r / 2 := by
  fin_cases r <;> norm_num [debit, rowDebit]

theorem target_cast (r : Fin 4) (k : Fin 9) :
    (target r k : ℝ) = lowerMatrix (r.castAdd 5) k := by
  fin_cases r <;> fin_cases k <;>
    norm_num [target, lowerMatrix, Fin.castAdd, Fin.castLE, Matrix.cons_val]

theorem mixed_original_entry_of_arithmetic (r : Fin 4) (k : Fin 9)
    (har : target r k + (if k = 0 then debit r else 0) ≤ entry r k)
    (hsigma : (sigmaCoeff k : ℝ) ≤ aProfile (nineProfile (nodeBasis k))) :
    (target r k : ℝ) + (if k = 0 then rowDebit r/2 else 0) ≤
      Xi2Coefficient (gamma5OriginalRow r) k := by
  have h := (Rat.cast_le (K := ℝ)).mpr har
  have hcast : ((target r k + (if k = 0 then debit r else 0) : ℚ) : ℝ) =
      (target r k : ℝ) + (if k = 0 then rowDebit r/2 else 0) := by
    by_cases hk : k = 0 <;> simp [hk, debit_cast]
  rw [hcast, entry_cast] at h
  have hN : 0 < count k := by unfold count; split_ifs <;> norm_num
  have hpos : 0 ≤ (sigmaCoeff k : ℝ) := by
    fin_cases k <;> norm_num [sigmaCoeff, Xi2RationalTop.massLower]
  exact h.trans (original_cell_uniform_lower r k hN hpos hsigma)

theorem mixed_corrected_entry_of_arithmetic (r : Fin 4) (k : Fin 9)
    (har : target r k + (if k = 0 then debit r else 0) ≤ entry r k)
    (hsigma : (sigmaCoeff k : ℝ) ≤ aProfile (nineProfile (nodeBasis k))) :
    lowerMatrix (r.castAdd 5) k ≤ correctedNineMatrix (r.castAdd 5) k := by
  rw [← target_cast r k]
  simp only [correctedNineMatrix, Fin.addCases_left]
  exact correctedCoefficient_lower_of_full r k (mixed_original_entry_of_arithmetic r k har hsigma)

end Xi2RationalMixed
#print axioms Xi2RationalMixed.mixed_corrected_entry_of_arithmetic
