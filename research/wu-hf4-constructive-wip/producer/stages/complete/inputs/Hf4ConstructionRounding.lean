import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! UNCOMPILED minimal draft. Fixed original scale; signed division is Int.ediv,
not Int.tdiv. No Real/Wu analytical imports and no constructor interpreter. -/
namespace Hf4Quad.Construction

def scale : ℤ := 100000000000000

def floorD (x : ℚ) : ℚ := ((Int.floor (x*(scale:ℚ)) : ℤ):ℚ)/(scale:ℚ)
def upD (x : ℚ) : ℚ := -floorD (-x)

theorem scale_pos : (0:ℚ) < (scale:ℚ) := by norm_num [scale]

private theorem scaled_num_den (x : ℚ) :
    x*(scale:ℚ) = ((x.num*scale:ℤ):ℚ)/(x.den:ℚ) := by
  rw [Int.cast_mul]
  calc
    x*(scale:ℚ) = ((x.num:ℚ)/(x.den:ℚ))*(scale:ℚ) := by rw [Rat.num_div_den]
    _ = (x.num:ℚ)*(scale:ℚ)/(x.den:ℚ) := by ring

/-- Positive Rat.den makes this signed Euclidean quotient the Python // rule. -/
theorem floorD_eq_ediv (x : ℚ) :
    floorD x = ((x.num*scale/(x.den:ℤ):ℤ):ℚ)/(scale:ℚ) := by
  unfold floorD
  rw [scaled_num_den, Rat.floor_intCast_div_natCast]

theorem upD_eq_ediv (x : ℚ) :
    upD x = ((-((-x.num)*scale/(x.den:ℤ)):ℤ):ℚ)/(scale:ℚ) := by
  rw [upD, floorD_eq_ediv]
  simp only [Rat.num_neg_eq_neg_num, Rat.den_neg_eq_den, Int.cast_neg, neg_div]

theorem floorD_le (x : ℚ) : floorD x ≤ x := by
  unfold floorD
  exact (div_le_iff₀ scale_pos).mpr (Int.floor_le (x*(scale:ℚ)))

theorem le_upD (x : ℚ) : x ≤ upD x := by
  change x ≤ -floorD (-x)
  simpa only [neg_neg] using neg_le_neg (floorD_le (-x))

end Hf4Quad.Construction
