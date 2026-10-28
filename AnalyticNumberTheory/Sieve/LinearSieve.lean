import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.AlmostPrime
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.Linarith

/-! # AnalyticNumberTheory.Sieve.LinearSieve

## Linear sieve and Jurkat--Richert interfaces

The Jurkat--Richert theorem (1965) is a central tool for the lower bound
on `W(N)` in Chen's theorem. It expresses upper and lower sieve bounds
using functions `F(s)` and `f(s)`.

The intended delay-differential description is:
  - `F(s) = 2e^γ / s` on the initial range `2 ≤ s ≤ 4`;
  - `f(s) = 0` for `s ≤ 3`;
  - `(s·F(s))' = f(s-1)` for `s ≥ 4`;
  - `(s·f(s))' = F(s-1)` for `s ≥ 3`,
where `γ` is the Euler--Mascheroni constant.

The definitions below use explicit initial formulas, with `F(2) = 1`
by the first branch, and approximate extensions beyond their initial
ranges. They do not implement the full delay-differential recursion.
The module proves finite sieve bridges and fixed-parameter remainder
interfaces, and records uniform main-term and lower-bound propositions
with an implication between them.

References:
  - Jurkat & Richert (1965), Acta Arith. 11, 217-240
  - Halberstam & Richert, "Sieve Methods" (1974), Ch. 8
  - Liu, Z. (2022), arXiv:2203.07871, §III
-/

namespace AnalyticNumberTheory.Sieve

open Real BoundingSieve

open scoped Classical

/-! ## 0. Finite lower-bound sieve interface -/


/-! ## 1. Euler--Mascheroni constant -/


/-! ## 2. Sieve functions F(s) and f(s) -/


/-! ## 3. Basic properties of the sieve functions -/


/-! ## 4. Sieve setup via Mathlib.BoundingSieve -/


/-! ## 5. Fixed-parameter Jurkat--Richert-shaped bounds -/


/-! ## 5.5 Uniform Jurkat--Richert lower-bound propositions -/

/-- Standard sieve product over the prime factors of `prodPrimes`:
`V_S = ∏_{p | prodPrimes} (1 - ν(p))`.
For a classical `SieveProblem`, where `prodPrimes` is the product of
primes below `z`, this equals `sieveProduct`
(`sieveProduct_eq_sieveProductPrimeFactors`).
For the modified Chen sieve, `prodPrimes` already excludes 2 and the
prime divisors of `N`, so this definition applies directly without
requiring the representation through `SieveProblem.z`. -/
noncomputable def sieveProductPrimeFactors (S : BoundingSieve) : ℝ :=
  ∏ p ∈ S.prodPrimes.primeFactors, (1 - S.nu p)


/-! ## 6. Application in Chen's theorem -/

/-
The classical Jurkat--Richert application in Chen's theorem uses:
  - `A = {N-p : p is prime, N^(1/10) < p < N}`, a Goldbach-type set;
  - `X ≈ N/log N`, approximating the prime count;
  - `ν(d) = Π_{p|d} (p-1)⁻¹`, the Goldbach density;
  - `z = N^(1/10)`, the sifting level;
  - `D = N^(1/2 - ε)`, the Bombieri--Vinogradov distribution level;
  - `s = log(D)/log(z) ≈ 5`, the sieve ratio.

The intended lower bound is `W(N) ≥ 2.6408 𝔖(N) N/log²N`, using
the relation `V(z) ≈ 𝔖(N)/log N` between the sieve product and
singular series. For the initial formula implemented here,
`f(5) = 2e^γ·log((5-1)/2)/5`; the numerical application requires
the appropriate analytic sieve estimates in addition to this definition.
-/

/-! ## 6.5 Chen's key inequality

The definitions of `W(N)` and `Ω(N)` and the key inequality belong to
`SwitchingPrinciple.lean` (`chenW`, `chenOmega`, `chen_key_inequality`).
The deduction uses explicit uniform analytic and counting inputs.
The fixed-parameter `jurkat_richert_lower_bound` here does not by itself
supply those inputs. In particular, replacing both counts by zero
would make `W(N) - Ω(N)/2 > 0` false. -/

/-! ## 7. Scope and dependencies -/

/-
**Sieve theory interfaces**

1. `SingularSeries.lean` supplies local factors, truncated products,
   and positivity; quantitative estimates use Mertens/PNT input.

2. This module defines `F`, `f`, and `SieveProblem`, proves finite
   sieve bridges, and provides fixed-parameter remainder interfaces.
   The formula for `f` on `(3,5]` is
   `2e^γ·log((s-1)/2)/s`; its extension beyond 5 remains approximate.
   `UniformJurkatRichertLowerBound` places constants before `∀ N`.
   Its finite bridge is `siftedSum_lower_bound_of_mainTerm`;
   `UniformJurkatRichertMainTerm` records the uniform analytic input
   `mainSum(μ⁻) ≥ V·(f(s) - η)`.

3. The mathlib bridges are:
   - `SieveProblem` extends `BoundingSieve`;
   - `sieveProduct_eq_prod_one_sub_nu`: `V(z) = Π_{p|P} (1-ν(p))`;
   - `sieveProduct_mul_selbergTerms_eq_nu`: `V(z)·g(P) = ν(P)`;
   - `sieveProduct_eq_nu_div_selbergTerms`: `V(z) = ν(P)/g(P)`;
   - `siftedSum_eq_filter`: weighted sieve sum as an unweighted count
     under the unit-weight hypothesis;
   - `distribution_condition`: the inherited `multSum_eq_main_err`.

4. The Chen deduction depends on explicit inputs:
   `chens_theorem (ChenAnalyticBounds, ChenCountingBridge)` uses
   `key_inequality_implies_chen`, the exact switching-count bridge,
   and `chen_key_inequality` (`W(N) - Ω/2 > 0`).
   The uniform Jurkat--Richert/Selberg content is carried by
   `ChenAnalyticBounds`, not by the pointwise remainder interfaces.

5. Separate analytic requirements include the uniform main-term
   lower estimate and the final Selberg upper estimate. Exact
   switching counts are defined in `SwitchingPrinciple.lean`;
   Bombieri--Vinogradov and large-sieve interfaces are in their
   respective modules. None of these uniform conclusions follows
   merely from the finite bridges proved here.
-/

end AnalyticNumberTheory.Sieve
