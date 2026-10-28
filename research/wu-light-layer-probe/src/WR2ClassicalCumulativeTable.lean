import Mathlib.Data.Nat.Basic

namespace WuPaper.ClassicalCumulativeTable

/-- Exact integer increment for a rounded trapezoid with its analytic error. -/
def increment (q : ℕ → ℕ) (E i : ℕ) : ℕ :=
  (3*4000^2*(q i+q (i+1))+E*1000000000000000+(6*4000^3-1))/(6*4000^3)

/-- Reconstruct only the short prefix following a stored block anchor. -/
def accumulate (q : ℕ → ℕ) (E anchor start : ℕ) : ℕ → ℕ
  | 0 => anchor
  | n+1 => accumulate q E anchor start n + increment q E (start+n)

/-- Anchors bound reduction depth without changing the cumulative table. -/
def table (q : ℕ → ℕ) (E : ℕ) (anchor : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i ≤ 10540 then accumulate q E (anchor (i/4)) (4*(i/4)) (i%4) else 0

end WuPaper.ClassicalCumulativeTable
