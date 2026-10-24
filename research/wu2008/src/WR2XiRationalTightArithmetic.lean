import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin

/-! Exact arithmetic experiment; the analytic integral comparison is separate. -/
namespace Xi2RationalCheck
open scoped BigOperators

def basic (x : ℚ) : ℚ :=
  let y := (x - 1) / (x + 1)
  2*y + 2*y^3/3

def factor (x : ℚ) : ℚ := basic ((1+x)/2) + basic (2*x/(1+x))
def refined (x : ℚ) : ℚ := factor ((1+x)/2) + factor (2*x/(1+x))
def factors : Fin 5 → ℚ := ![13/10, 7/2, 127/50, 47/25, 143/100]
def scalar : ℚ := (∑ j : Fin 5, refined (4 / factors j)) / 5
def sigmaCoeff : ℚ := (75612009467/15625000000000) / (1 - 858467/5000000)
def endpoint (m : ℕ) : ℚ := 13/5 + (1/10)*(m:ℚ)/512
def payment (m : ℕ) : ℚ :=
  ((endpoint (m+1) - endpoint m) / (5 * endpoint (m+1))) *
    ∑ j : Fin 5, refined ((endpoint m + 1) / factors j)
def tightEntry : ℚ := sigmaCoeff * scalar + ∑ m ∈ Finset.range 512, payment m

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tight_arithmetic : (27/1000 : ℚ) ≤ tightEntry := by
  decide +kernel

end Xi2RationalCheck
#print axioms Xi2RationalCheck.tight_arithmetic
