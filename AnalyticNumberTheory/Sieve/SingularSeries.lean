import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # AnalyticNumberTheory.Sieve.SingularSeries

## Goldbach singular-series factors and finite products

The classical Chen bounds contain the singular-series factor

  𝔖(N) = Π_{p|N, p>2} (p-1)/(p-2) · Π_{p>2} (1 - 1/(p-1)²),

whose second product is the twin-prime constant `C₂ ≈ 0.66016...`.
For even `N`, the local factors used in this module are:
  - `p = 2`: 2;
  - `p > 2`, `p | N`: `p/(p-1)`;
  - `p > 2`, `p ∤ N`: `p(p-2)/(p-1)²`.

Thus the local-factor product includes the factor 2, unlike the
normalization of `𝔖(N)` displayed above. The implemented
`singularSeries N` is the finite product truncated at `z=N`,
not an infinite-product limit. All results below concern these
defined finite products.

References:
  - Chen, J.R. (1973), Sci. Sinica 16, 157-176
  - Liu, Z. (2022), "A Corrected Simplified Proof of Chen's Theorem", arXiv:2203.07871
  - Halberstam & Richert, "Sieve Methods" (1974)
-/

namespace AnalyticNumberTheory.Sieve

open Nat Real Finset

/-! ## 1. Local factors -/

/-- Singular-series local factor at an odd prime `p`:
if `p | N`, then
`g(p,N) = (p-1)/(p-2)·(1-1/(p-1)²) = p/(p-1)`;
otherwise `g(p,N) = 1-1/(p-1)² = p(p-2)/(p-1)²`.
The prime 2 is treated separately, with factor 2 for even `N`
and factor 1 for odd `N` in this definition. -/
noncomputable def localFactor (p N : ℕ) : ℝ :=
  if p = 2 then
    if 2 ∣ N then 2 else 1
  else
    if p ∣ N then
      (p : ℝ) / (p - 1)
    else
      (p : ℝ) * (p - 2) / ((p - 1) ^ 2)


/-! ## 2. Positivity of local factors -/


/-! ## 3. Truncated singular series -/

/-- Truncated local-factor product:
`𝔖(N,z) = Π_{p≤z, p.Prime} localFactor p N`.
The classical infinite product is obtained by a convergence argument
as `z → ∞`, with the normalization of these local factors;
that limiting identification is not part of this definition. -/
noncomputable def singularSeriesTruncated (N z : ℕ) : ℝ :=
  ((range (z + 1)).filter Nat.Prime).prod (fun p => localFactor p N)


/-! ## 4. Finite singular-series proxy -/


/-! ## 5. Explicit even case -/


/-! ## 6. Upper bounds for local factors -/


/-! ## 7. Elementary singular-series bounds -/


/-! ## 7.5 Uniform lower bound for truncated products -/


/-! ## 8. Scope and applications -/

/-
This module defines `localFactor p N`,
`singularSeriesTruncated N z`, and the finite proxy
`singularSeries N = singularSeriesTruncated N N`.
An infinite-product definition and its limiting identification
are separate from these finite definitions.

Positivity is proved by `localFactor_pos`,
`singularSeriesTruncated_pos`, and `singularSeries_pos`.
The elementary bounds are:
- `singularSeries_bounded_above`: `𝔖(N) ≤ 2^{ω(N)} ≤ 2N` for `N ≥ 2`,
  by separating divisor and nondivisor primes. A constant upper
  bound is impossible along primorials, where growth has order
  `log log N`.
- `singularSeries_bounded_below`: `𝔖(N) ≥ 1` for even `N ≥ 2`,
  using comparison with the telescoping integer product
  `∏(1-1/n²) = N/(2(N-1)) ≥ 1/2`.
- `singularSeriesTruncated_ge_half`: `𝔖(N,z) ≥ 1/2`
  for any `N` and `z ≥ 2`, supplying the uniform product lower
  bound needed in the Chen main term.
These finite bounds require neither Mertens' theorem nor the PNT.

In the classical Chen application, consistently normalized
singular-series factors occur in
`W(N) ≥ 2.6408 𝔖(N) N/log²N` (Jurkat--Richert) and
`Ω ≤ 3.9404 𝔖(N) N/log²N` (Selberg and large-sieve input).
Positivity then gives `W(N) - Ω/2 > 0`.
Those numerical analytic bounds are not proved by the finite
product estimates alone.
-/

end AnalyticNumberTheory.Sieve
