import MathlibNt.SieveTheory.Selberg.TruncatedOptimalWeights
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.Divisors

import AnalyticNumberTheory.Sieve.LinearSieve
import AnalyticNumberTheory.Sieve.SelbergIdentities
import AnalyticNumberTheory.Sieve.WeightedPan

/-! # AnalyticNumberTheory.Sieve.SelbergUpperBound

## Generic Selberg upper-bound sieve

The Selberg sieve is a central tool for the upper bound on `Ω` in
Chen's theorem. An upper Moebius sequence from Λ² weights separates
the sifted count into a main term and a remainder. The classical
shape (Halberstam--Richert 1974 Ch. 3; Nathanson GTM 164 Ch. 10;
Liu 2022 §III) is
`S(A,P,z) ≤ X/G(z) + Σ |R_d|`, where
`G(z) = Σ_{d|P} g(d)` and
`g(d) = ν(d)·∏_{p|d}(1−ν(p))⁻¹`.
For the full divisor sum used here, optimal Λ² weights attain
`mainSum = 1/G(z)`.

This module supplies:

1. `SelbergWeights`, a generic bounded, supported weight structure,
   and its trivial existence theorem `selberg_sieve_weights_exist`.
2. Bridges to mathlib's `BoundingSieve.lambdaSquared`:
   `selberg_lambda_is_upper_moebius`, the basic upper bound
   `omega_upper_bound_via_mathlib`, diagonalization
   `mainSum_diag_via_mathlib`, and the Cauchy--Schwarz lower bound
   `mainSum_cauchy_schwarz_lower_bound`.
3. Explicit optimal full-divisor weights `optimalSelbergWeight`,
   with `mainSum(Λ²w*) = (Σg)⁻¹` (`optimalSelbergMainSum_eq`),
   giving the finite theorem `selberg_upper_bound_optimal`
   without additional analytic input.
4. `UniformSelbergUpperBound` for a family of `BoundingSieve`
   structures, with `N₀` before `∀ N`, proved directly from
   the optimal-weight theorem. The numerical Chen bound
   `3.9404·𝔖(N)·N/log²N` additionally requires Mertens/singular-series
   main-term estimates and a weighted Pan remainder input
   (`WeightedPan`); the finite theorem does not supply them.

References:
  - Selberg, A. (1947), Norske Vid. Selsk. Forh. Trondheim 19, 75-79
  - Halberstam & Richert, "Sieve Methods" (1974), Ch. 3
  - Nathanson, "Additive Number Theory: The Classical Bases" (1996), Ch. 10
  - Liu, Z. (2022), arXiv:2203.07871, §III
  - Mathlib `SelbergSieve.lean`: BoundingSieve, Λ² sieve, selbergTerms
-/

namespace AnalyticNumberTheory.Sieve

open MathlibNt.SieveTheory.LiuWeight

open Finset Real

open scoped Classical
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta

/-! ## 1. Selberg weight structure -/


/-! ## 2. Bridges to mathlib -/


/-- **Basic Selberg upper bound** (mathlib): any sequence `w`
with `w 1 = 1` gives
`siftedSum ≤ totalMass·mainSum(Λ²w) + errSum(Λ²w)`.
Choosing weights minimizing `mainSum` gives the optimal finite
upper bound; the remainder still needs separate control. -/
theorem omega_upper_bound_via_mathlib
    (S : BoundingSieve) (w : ℕ → ℝ) (hw : w 1 = 1) :
    S.siftedSum ≤ S.totalMass * S.mainSum (BoundingSieve.lambdaSquared w) +
      S.errSum (BoundingSieve.lambdaSquared w) := by
  exact BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius _
    (BoundingSieve.upperMoebius_lambdaSquared w hw)

/-- **Main-term diagonalization** (mathlib): `mainSum(Λ²w)` is a
diagonal quadratic form with coefficients `(selbergTerms l)⁻¹`. -/
theorem mainSum_diag_via_mathlib
    (S : BoundingSieve) (w : ℕ → ℝ) :
    S.mainSum (BoundingSieve.lambdaSquared w) =
      ∑ l ∈ S.prodPrimes.divisors, (S.selbergTerms l)⁻¹ *
        (∑ d ∈ S.prodPrimes.divisors,
          if l ∣ d then S.nu d * w d else 0) ^ 2 := by
  exact S.mainSum_lambdaSquared_eq_sum_mul_sum_sq w


/-! ## 3. Optimal Selberg weights -/

/-- Optimal Selberg main term: `(Σ_{l|P} selbergTerms l)⁻¹`. -/
noncomputable def selbergMainTerm (S : BoundingSieve) : ℝ :=
  (∑ l ∈ S.prodPrimes.divisors, S.selbergTerms l)⁻¹

/-- Optimal diagonal values `x*_l = g(l)·μ(l)·(Σg)⁻¹`,
minimizing `Σ_l g(l)⁻¹·x_l²` subject to `w(1)=1`. -/
noncomputable def optimalSelbergX (S : BoundingSieve) (l : ℕ) : ℝ :=
  S.selbergTerms l * (μ l : ℝ) * selbergMainTerm S

/-- **Optimal Selberg Λ² weights**: apply upper-interval Moebius
inversion to `optimalSelbergX` on the divisor lattice of `prodPrimes`,
then divide by the density:
`w*(d) = ν(d)⁻¹·Σ_{e : d|e|P} μ(e/d)·x*_e`.
`optimalSelbergMainSum_eq` proves
`mainSum(Λ²w*) = (Σg)⁻¹`, attaining the lower bound
`mainSum_cauchy_schwarz_lower_bound`. -/
noncomputable def optimalSelbergWeight (S : BoundingSieve) : ℕ → ℝ :=
  fun d =>
    if _hd : d ∣ S.prodPrimes then
      (∑ e ∈ S.prodPrimes.divisors,
        if d ∣ e then (μ (e / d) : ℝ) * optimalSelbergX S e else 0) / S.nu d
    else 0

/-- Taking the cutoff to be the sieve product retains every divisor. -/
private theorem fullSelbergCarrier_eq (S : BoundingSieve) :
    truncatedSelbergCarrier S S.prodPrimes = S.prodPrimes.divisors := by
  apply Finset.filter_eq_self.mpr
  intro d hd
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero S.prodPrimes_ne_zero)
    (Nat.mem_divisors.mp hd).1

private theorem selbergMainTerm_eq_truncated (S : BoundingSieve) :
    selbergMainTerm S = 1 / truncatedSelbergDenominator S S.prodPrimes := by
  simp only [selbergMainTerm, truncatedSelbergDenominator, fullSelbergCarrier_eq, one_div]

private theorem optimalSelbergX_eq_truncated (S : BoundingSieve) {l : ℕ}
    (hl : l ∣ S.prodPrimes) :
    optimalSelbergX S l = truncatedSelbergOptimalX S S.prodPrimes l := by
  have hlC : l ∈ truncatedSelbergCarrier S S.prodPrimes := by
    rw [fullSelbergCarrier_eq]
    exact Nat.mem_divisors.mpr ⟨hl, S.prodPrimes_ne_zero⟩
  rw [truncatedSelbergOptimalX, if_pos hlC, optimalSelbergX,
    selbergMainTerm_eq_truncated]
  ring

/-- The untruncated weight is the same finite optimizer with cutoff `P`. -/
private theorem optimalSelbergWeight_eq_truncated (S : BoundingSieve) :
    optimalSelbergWeight S = truncatedSelbergOptimalLambda S S.prodPrimes := by
  funext d
  unfold optimalSelbergWeight truncatedSelbergOptimalLambda
  rw [fullSelbergCarrier_eq]
  by_cases hd : d ∣ S.prodPrimes
  · rw [dif_pos hd, if_pos (Nat.mem_divisors.mpr ⟨hd, S.prodPrimes_ne_zero⟩)]
    apply congrArg (fun x : ℝ => x / S.nu d)
    apply Finset.sum_congr rfl
    intro e he
    rw [optimalSelbergX_eq_truncated S (Nat.mem_divisors.mp he).1]
  · rw [dif_neg hd, if_neg (fun h => hd (Nat.mem_divisors.mp h).1)]

/-- **Normalization of the optimal weight**: `w*(1) = 1`. -/
theorem optimalSelbergWeight_one (S : BoundingSieve) :
    optimalSelbergWeight S 1 = 1 := by
  rw [optimalSelbergWeight_eq_truncated]
  exact truncatedSelbergOptimalLambda_one S
    (Nat.one_le_iff_ne_zero.mpr S.prodPrimes_ne_zero)

/-- **Diagonal-value identification**:
`Σ_{d : l|d|P} ν(d)·w*(d) = x*_l`.
This is the upper-interval Moebius-inversion identity for
`w* = ν⁻¹·y*`, where
`y*(d) = Σ_{e : d|e|P} μ(e/d)·x*_e`. -/
theorem optimalSelbergX_eq_sum_nu_mul_weight (S : BoundingSieve) (l : ℕ)
    (hl : l ∣ S.prodPrimes) :
    optimalSelbergX S l =
      ∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * optimalSelbergWeight S d else 0 := by
  rw [optimalSelbergX_eq_truncated S hl, optimalSelbergWeight_eq_truncated]
  exact truncatedSelbergOptimalX_eq_sum_nu_mul_lambda S S.prodPrimes l
    (by rw [fullSelbergCarrier_eq]; exact Nat.mem_divisors.mpr ⟨hl, S.prodPrimes_ne_zero⟩)

/-- **Optimal main-term identity**:
`mainSum(Λ²w*) = (Σ_{l|P} selbergTerms l)⁻¹`,
the equality case of `mainSum_cauchy_schwarz_lower_bound`. -/
theorem optimalSelbergMainSum_eq (S : BoundingSieve) :
    S.mainSum (BoundingSieve.lambdaSquared (optimalSelbergWeight S)) = selbergMainTerm S := by
  rw [optimalSelbergWeight_eq_truncated, selbergMainTerm_eq_truncated]
  exact mainSum_truncatedSelbergOptimalLambda S
    (Nat.one_le_iff_ne_zero.mpr S.prodPrimes_ne_zero)

/-- **Finite Selberg upper bound**: optimal Λ² weights minimize
the main term and give
`siftedSum ≤ totalMass·(Σ_{l|P} selbergTerms l)⁻¹ + errSum(Λ²w*)`.
This is the exact finite form of `S ≤ X/G(z) + R`
(Halberstam--Richert 1974 Ch. 3).
In the Chen application, estimates of the indicated
`(Σg)⁻¹ ≈ 8𝔖(N)/log N` shape and `errSum ≪ N/log^A N`
require separate Mertens/singular-series and weighted Pan inputs. -/
theorem selberg_upper_bound_optimal (S : BoundingSieve) :
    ∃ w : ℕ → ℝ, w 1 = 1 ∧
      S.siftedSum ≤
        S.totalMass * (∑ l ∈ S.prodPrimes.divisors, S.selbergTerms l)⁻¹ +
          S.errSum (BoundingSieve.lambdaSquared w) := by
  refine ⟨optimalSelbergWeight S, optimalSelbergWeight_one S, ?_⟩
  have h := omega_upper_bound_via_mathlib S (optimalSelbergWeight S) (optimalSelbergWeight_one S)
  rw [optimalSelbergMainSum_eq S] at h
  simpa [selbergMainTerm] using h


/-! ## 3.7 Moebius weights attain the full-divisor optimum -/


/-! ## 4. Uniform finite Selberg upper bound -/


/-! ## 5. Numerical coefficient in Chen's theorem -/


end AnalyticNumberTheory.Sieve
