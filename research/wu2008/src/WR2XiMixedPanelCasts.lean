import WR2XiMixedCasts

/-! Identify every rational panel and clipped sum with its real integral payment. -/
noncomputable section
namespace Xi2RationalMixed
open Xi2RationalTop (factors left right sigmaCoeff scalar target)
open WuPaper.R2Xi Wu2008DoubleSieve MotherPair NodeExtension
open scoped BigOperators

private theorem refined_cast (x : ℚ) : (Xi2RationalCheck.refined x : ℝ) = cellLogLower (x : ℝ) :=
  rationalCellLog_cast x

theorem panel_cast (r : Fin 4) (j : Fin 9) (a b : ℚ) :
    (panel r j a b : ℝ) = originalPiecePayment (gamma5OriginalRow r) (a : ℝ) (b : ℝ) j := by
  rcases parameter_cast r with ⟨hs, hS, hk1, hk2, hk3⟩
  fin_cases j <;>
    simp [panel, logarithms, originalPiecePayment, productLogLower, middleFactors,
      Fin.sum_univ_succ, refined_cast, denominatorMax_cast, hs, hS, hk1, hk2, hk3,
      factors_cast, xi2Factors] <;> ring

theorem piece_cast (r : Fin 4) (k j : Fin 9) :
    (piece r k j : ℝ) = originalPieceLower r k j (count k) := by
  have hL : ((max (left k) (intervals r j).1 : ℚ) : ℝ) =
      max (upperLeft k) (xi2PieceInterval (gamma5OriginalRow r) j).1 := by
    push_cast
    rw [left_cast, (intervals_cast r j).1]
  have hU : ((min (right k) (intervals r j).2 : ℚ) : ℝ) =
      min (upperNode k) (xi2PieceInterval (gamma5OriginalRow r) j).2 := by
    push_cast
    rw [right_cast, (intervals_cast r j).2]
  have hord : max (left k) (intervals r j).1 < min (right k) (intervals r j).2 ↔
      max (upperLeft k) (xi2PieceInterval (gamma5OriginalRow r) j).1 <
        min (upperNode k) (xi2PieceInterval (gamma5OriginalRow r) j).2 := by
    rw [← hL, ← hU]
    norm_cast
  unfold piece originalPieceLower
  simp only [← hord]
  split_ifs
  · push_cast
    simp_rw [panel_cast, point_cast, hL, hU]
  · norm_num

theorem entry_cast (r : Fin 4) (k : Fin 9) : (entry r k : ℝ) =
    xi2SigmaScalarLower (gamma5OriginalRow r) * (sigmaCoeff k : ℝ) +
      ∑ j : Fin 9, originalPieceLower r k j (count k) := by
  unfold entry
  push_cast
  simp_rw [scalar_cast, piece_cast]
  ring

end Xi2RationalMixed
#print axioms Xi2RationalMixed.entry_cast
