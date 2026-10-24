import WR2XiRationalMixedData
import WR2XiMixedUniform
import WR2XiRationalLog

/-! Cast the computable mixed-cell certificate to the proved real panel sums. -/
noncomputable section
namespace Xi2RationalMixed
open Xi2RationalTop (factors left right sigmaCoeff scalar target)
open WuPaper.R2Xi Wu2008DoubleSieve MotherPair SecondFunctionalParameters NodeExtension
open WuPaper.RMapMMatrix
open scoped BigOperators

private theorem refined_cast (x : ℚ) : (Xi2RationalCheck.refined x : ℝ) = cellLogLower (x : ℝ) :=
  rationalCellLog_cast x

theorem factors_cast (r : Fin 4) (j : Fin 5) :
    (factors r j : ℝ) = xi2Factors (gamma5OriginalRow r) j := by
  fin_cases r <;> fin_cases j <;>
    norm_num [factors, xi2Factors, gamma5OriginalRow, row1, row2, row3, row4]

theorem parameter_cast (r : Fin 4) :
    (s r : ℝ) = (gamma5OriginalRow r).s ∧
    (scale r : ℝ) = (gamma5OriginalRow r).S ∧
    (k1 r : ℝ) = (gamma5OriginalRow r).kappa1 ∧
    (k2 r : ℝ) = (gamma5OriginalRow r).kappa2 ∧
    (k3 r : ℝ) = (gamma5OriginalRow r).kappa3 := by
  simp [s, scale, k1, k2, k3, factors_cast, xi2Factors]

theorem left_cast (k : Fin 9) : (left k : ℝ) = upperLeft k := by
  fin_cases k <;> norm_num [left, upperLeft]

theorem right_cast (k : Fin 9) : (right k : ℝ) = upperNode k := by
  unfold right upperNode
  push_cast
  rfl

theorem intervals_cast (r : Fin 4) (j : Fin 9) :
    ((intervals r j).1 : ℝ) = (xi2PieceInterval (gamma5OriginalRow r) j).1 ∧
    ((intervals r j).2 : ℝ) = (xi2PieceInterval (gamma5OriginalRow r) j).2 := by
  rcases parameter_cast r with ⟨hs, hS, hk1, hk2, hk3⟩
  fin_cases j <;>
    simp [intervals, xi2PieceInterval, hs, hS, hk1, hk2, hk3,
      alpha1, alpha2, alpha3, alpha5, alpha6, alpha7, alpha8, alpha9]

theorem quadratic_cast (S t : ℚ) : (quadratic S t : ℝ) = quadraticDenominator (S : ℝ) (t : ℝ) := by
  simp [quadratic, quadraticDenominator]

theorem denominatorMax_cast (S a b : ℚ) :
    (denominatorMax S a b : ℝ) = quadraticDenominatorMax (S : ℝ) (a : ℝ) (b : ℝ) := by
  by_cases h : b ≤ S/2
  · have hr : (b : ℝ) ≤ (S : ℝ)/2 := by exact_mod_cast h
    simp [denominatorMax, quadraticDenominatorMax, h, hr, quadratic_cast]
  · have hr : ¬(b : ℝ) ≤ (S : ℝ)/2 := by exact_mod_cast h
    by_cases h' : S/2 ≤ a
    · have hr' : (S : ℝ)/2 ≤ (a : ℝ) := by exact_mod_cast h'
      simp [denominatorMax, quadraticDenominatorMax, h, hr, h', hr', quadratic_cast]
    · have hr' : ¬(S : ℝ)/2 ≤ (a : ℝ) := by exact_mod_cast h'
      simp [denominatorMax, quadraticDenominatorMax, h, hr, h', hr']

theorem point_cast (a b : ℚ) (n m : ℕ) :
    (point a b n m : ℝ) = panelPoint (a : ℝ) (b : ℝ) n m := by
  simp [point, panelPoint]

theorem scalar_cast (r : Fin 4) :
    (scalar r : ℝ) = xi2SigmaScalarLower (gamma5OriginalRow r) := by
  unfold scalar xi2SigmaScalarLower productLogLower
  push_cast
  simp_rw [refined_cast]
  push_cast
  simp_rw [factors_cast]
  norm_num

end Xi2RationalMixed
#print axioms Xi2RationalMixed.intervals_cast
#print axioms Xi2RationalMixed.denominatorMax_cast
