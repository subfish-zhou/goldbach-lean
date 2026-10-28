

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIIActualTensorEnergy

/-!
 # Divisor-square moments for the actual Vaughan Type-II tensor energy

The fibre Cauchy bound is summed in `(d,t)` before any pointwise estimate in
`n = d*t`.  Each actual `e*m=t` fibre injects into the divisors of `t`, and its
Mangoldt energy is bounded by the same divisor count times `log (y+1)^2`.
Thus a whole fixed-`d` row is controlled by a divisor-square prefix at length
`y/d`.

The only frozen analytic input below is the classical divisor-square moment
bound.  It is stated for that scalar prefix, not for the tensor energy or for
the final Type-II conclusion.
-/

namespace AnalyticNumberTheory.LargeSieve

open Finset
open scoped BigOperators ArithmeticFunction

/-- The scalar divisor-square prefix, written on the integer interval used by
the primitive large-sieve modules.  On this interval `t.toNat` is positive. -/
noncomputable def divisorSquarePrefix (X : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc (1 : ℤ) X, ((t.toNat.divisors.card : ℝ) ^ 2)

/-- The minimal classical analytic input: an explicit `X log^3(X+1)` upper
bound for the second moment of the divisor function. -/
def DivisorSquareMomentBound (C : ℝ) : Prop :=
  ∀ X : ℕ, divisorSquarePrefix X ≤
    C * (X : ℝ) * Real.log (X + 1 : ℕ) ^ 3


end AnalyticNumberTheory.LargeSieve
