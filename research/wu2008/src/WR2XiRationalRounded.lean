import WR2XiRationalMixedData
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Downward rounding keeps rectangle certificates on a fixed common denominator. -/
namespace Xi2RationalMixed
open Xi2RationalTop (left right sigmaCoeff scalar)
open scoped BigOperators

def roundDown (x : ℚ) : ℚ := (⌊x*1000000000000⌋ : ℚ)/1000000000000

theorem roundDown_le (x : ℚ) : roundDown x ≤ x := by
  have h := Int.floor_le (x*1000000000000)
  unfold roundDown
  exact (div_le_iff₀ (by norm_num : (0:ℚ)<1000000000000)).mpr h

def roundedPiece (r : Fin 4) (k j : Fin 9) : ℚ :=
  let a := max (left k) (intervals r j).1
  let b := min (right k) (intervals r j).2
  if a < b then ∑ m ∈ Finset.range (count k),
    roundDown (panel r j (point a b (count k) m) (point a b (count k) (m+1))) else 0

theorem roundedPiece_le (r : Fin 4) (k j : Fin 9) : roundedPiece r k j ≤ piece r k j := by
  unfold roundedPiece piece
  dsimp only
  split_ifs
  · exact Finset.sum_le_sum (fun m _ => roundDown_le _)
  · exact le_rfl

def roundedEntry (r : Fin 4) (k : Fin 9) : ℚ :=
  sigmaCoeff k * scalar r + ∑ j : Fin 9, roundedPiece r k j

theorem roundedEntry_le (r : Fin 4) (k : Fin 9) : roundedEntry r k ≤ entry r k := by
  unfold roundedEntry entry
  exact add_le_add le_rfl (Finset.sum_le_sum (fun j _ => roundedPiece_le r k j))

end Xi2RationalMixed
#print axioms Xi2RationalMixed.roundedEntry_le
