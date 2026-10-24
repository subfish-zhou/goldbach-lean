import WR2XiRationalTopArithmetic

/-! Exact clipped rectangle arithmetic for the fourteen mixed cells, including Gamma5 budgets.
The analytic comparison is separate from this computable rational certificate. -/
namespace Xi2RationalMixed
open Xi2RationalTop (factors left right sigmaCoeff scalar target)
open Xi2RationalCheck (refined)
open scoped BigOperators

def s (r : Fin 4) : ℚ := factors r 0 + 1
def scale (r : Fin 4) : ℚ := factors r 1 + 1
def k1 (r : Fin 4) : ℚ := factors r 2 + 1
def k2 (r : Fin 4) : ℚ := factors r 3 + 1
def k3 (r : Fin 4) : ℚ := factors r 4 + 1

def intervals (r : Fin 4) : Fin 9 → ℚ × ℚ :=
  let S := scale r
  let a1 := k1 r - 2
  let a2 := S - 2
  let a3 := S - S / s r - 1
  let a5 := S - S / k3 r - 1
  let a6 := S - 2*S / k2 r
  let a7 := S - S / k1 r - S / k3 r
  let a8 := S - S / k1 r - S / k2 r
  let a9 := k1 r - k1 r / k2 r - 1
  ![(a2,3),(a9,a1),(a5,a2),(a3,a2),(a1,a2),(a7,a5),(a5,a8),(a6,a8),(a8,a2)]

def quadratic (S t : ℚ) : ℚ := t * (1 - t/S)
def denominatorMax (S a b : ℚ) : ℚ :=
  if b ≤ S/2 then quadratic S b else if S/2 ≤ a then quadratic S a else S/4

def logarithms (r : Fin 4) (a b : ℚ) : Fin 9 → ℚ :=
  let S := scale r
  ![(∑ j : Fin 5, refined ((a+1)/factors r j)),
    refined ((a+1)/((k2 r-1)*(k1 r-1-a))),
    refined ((a+1)/((k3 r-1)*(S-1-a))),
    refined ((a+1)/((s r-1)*(S-1-a))),
    refined ((a+1)/(k1 r-1)) + refined ((a+1)/(k2 r-1)),
    refined (S^2/((k1 r*S-S-k1 r*a)*(k3 r*S-S-k3 r*a))),
    refined (S*(S-1-a)/(k1 r*S-S-k1 r*a)),
    refined (S/(k2 r*S-S-k2 r*a)),
    refined (S-1-b)]

def count (k : Fin 9) : ℕ := if k = 0 then 512 else 128
def point (a b : ℚ) (n m : ℕ) : ℚ := a + (b-a)*m/n

def panel (r : Fin 4) (j : Fin 9) (a b : ℚ) : ℚ :=
  (b-a) * logarithms r a b j /
    (5 * (if j.val < 5 then b else denominatorMax (scale r) a b))

def piece (r : Fin 4) (k j : Fin 9) : ℚ :=
  let a := max (left k) (intervals r j).1
  let b := min (right k) (intervals r j).2
  if a < b then ∑ m ∈ Finset.range (count k),
    panel r j (point a b (count k) m) (point a b (count k) (m+1)) else 0

def entry (r : Fin 4) (k : Fin 9) : ℚ :=
  sigmaCoeff k * scalar r + ∑ j : Fin 9, piece r k j

def debit : Fin 4 → ℚ := ![1/1500,1/1000,9/8000,1/2000]

end Xi2RationalMixed
