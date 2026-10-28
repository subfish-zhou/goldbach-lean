import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Analysis.SpecialFunctions.Exp
import MathlibNt.SieveTheory.Arithmetic.MertensTheorem

/-!
# MathlibNt.SieveTheory.SelbergUpperBound

## Selberg sieve and the target bound Ω ≤ 3.9404 𝔖(N) N/log²N

The Selberg sieve is a central tool for the upper bound on Ω in Chen's theorem.
Selberg upper-bound weights λ_d lead to a main term M₁ and a remainder R.

**Classical proof outline** (Liu 2022, §III):

1. **Selberg weights** (Lemma 3): construct λ_d with
   - λ₁ = 1 and λ_d = 0 for d > z or d ∤ Q;
   - |λ_d| ≤ 1;
   - Σ_{d₁,d₂} λ_{d₁}λ_{d₂}/φ([d₁,d₂]) = [8 + O(ε)] 𝔖(N)/log N.

2. **Numerical integration** (Lemma 4):
   Σ_a f(a)/(a log(N/a)) ≤ 0.49254/log N.

3. **Main term**: for suitably controlled ε,
   M₁ ≤ [8 + O(ε)] · 0.49254 · 𝔖(N) N/log²N ≤ 3.94033 𝔖(N) N/log²N.

4. **Remainder**: R ≪ N/log^A N, using Pan's mean-value theorem.

5. **Combination**: Ω ≤ M₁ + |R| ≤ 3.9404 𝔖(N) N/log²N.

This module connects the development to `Mathlib.NumberTheory.SelbergSieve`
and proves finite algebraic and divisor-sum results. The interfaces for the
numerical main and error terms below allow constants depending on a fixed N;
they do not establish the uniform optimized bounds in this classical outline.

References:
  - Selberg, A. (1947), Norske Vid. Selsk. Forh. Trondheim 19, 75-79
  - Liu, Z. (2022), arXiv:2203.07871, Lemma 3-4, §III
  - Halberstam & Richert, "Sieve Methods" (1974), Ch. 3
  - Mathlib `SelbergSieve.lean`: BoundingSieve, SelbergSieve, Λ² sieve
-/

namespace MathlibNt.SieveTheory.SelbergUpperBound

open Real Finset
open MathlibNt.SieveTheory.MertensTheorem

open scoped Classical
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta

/-! ## 1. Selberg sieve weights (Lemma 3) -/


/-! ## 2. Numerical integration (Lemma 4) -/


/-! ## 3. Estimating the main term M₁ -/


/-! ## 4. Estimating the remainder R -/


/-! ## 5. Combined upper-bound interfaces for Ω -/


/-! ## 6. Correspondence with Mathlib's Selberg sieve -/

/-
`Mathlib.NumberTheory.SelbergSieve` provides:
  - `BoundingSieve`: the general sieve setup;
  - `SelbergSieve`: a structure adding a level parameter;
  - `IsUpperMoebius`: the upper Möbius condition;
  - `siftedSum_le_mainSum_errSum_of_upperMoebius`: the basic upper-sieve theorem;
  - `lambdaSquared`: Λ² sieve weights;
  - `upperMoebius_lambdaSquared`: the upper Möbius property of the Λ² sieve;
  - `mainSum_lambdaSquared_eq_sum_mul_sum_sq`: diagonalization of the main term;
  - `selbergTerms`: the Selberg terms g(d) = ν(d) Π_{p|d} (1-ν(p))⁻¹.

This section connects these Mathlib objects to `SelbergWeights`.
-/

open BoundingSieve


/-! ## 7. Auxiliary definition: π(x; a, q, l) -/


/-! ## 6.5a. Ingredients for `divisor_sum_bound` -/

/-- Weight f(d) = A^{ω(d)}/φ(d), with f(0) = 0. -/
noncomputable def divisorWeight (A : ℝ) : ArithmeticFunction ℝ where
  toFun d := (A : ℝ) ^ d.primeFactors.card / Nat.totient d
  map_zero' := by simp [Nat.totient_zero]


private lemma divisorWeight_multiplicative (A : ℝ) : (divisorWeight A).IsMultiplicative := by
  constructor
  · simp [divisorWeight]
  · intro m n hmn
    change A ^ (m * n).primeFactors.card / (Nat.totient (m * n) : ℝ) =
      (A ^ m.primeFactors.card / (Nat.totient m : ℝ)) *
        (A ^ n.primeFactors.card / (Nat.totient n : ℝ))
    rw [Nat.Coprime.primeFactors_mul hmn,
      Finset.card_union_of_disjoint hmn.disjoint_primeFactors,
      Nat.totient_mul hmn, Nat.cast_mul, pow_add, div_mul_div_comm]


/-! ## 6.5. Lemma 2 (divisor-sum bound) -/


/-- Divisor-sum weight f(d) = A^{ω(d)}/φ(d), as an arithmetic function with f(0) = 0. -/
noncomputable def chenDivisorWeight (A : ℝ) : ArithmeticFunction ℝ where
  toFun d := A ^ (d.primeFactors.card : ℕ) / Nat.totient d
  map_zero' := by simp [Nat.totient_zero]


private lemma chenDivisorWeight_isMultiplicative (A : ℝ) :
    (chenDivisorWeight A).IsMultiplicative :=
  divisorWeight_multiplicative A


/-- **Special case of Lemma 2**: if n is a product of distinct primes ≤ y
(that is, `Squarefree n` and all prime factors are ≤ y), with y ≥ 3,
then Σ_{d|n} A^ω(d)/φ(d) ≪ (log y)^A.

Proof:
  1. The weight f(d) = A^{ω(d)}/φ(d) is multiplicative, so
     `prodPrimeFactors_one_add_of_squarefree` gives
     Σ_{d|n} f(d) = ∏_{p|n}(1 + f p).
  2. At a prime p, f p = A/(p-1), hence
     ∏_{p|n}(1 + A/(p-1)) ≤ exp(A·Σ_{p|n} 1/(p-1)).
  3. Mertens' theorem (`prime_inv_pminus1_bound`) gives
     Σ_{p|n} 1/(p-1) ≤ Σ_{p≤y} 1/(p-1) ≤ log(log y) + C.
  4. exp(A·(log(log y) + C)) = e^{AC}·(log y)^A.

The hypotheses explicitly include `Squarefree n` and `3 ≤ y`.
Allowing y = 1 would make the right side zero while the left side is at least 1. -/
theorem divisor_sum_bound_squarefree (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, ∀ n y : ℕ, 1 ≤ n →
      Squarefree n →
      (∀ p : ℕ, p.Prime → p ∣ n → p ≤ y) →
      3 ≤ y →
      (n.divisors).sum (fun d =>
        (A : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d) ≤
      C * (log y) ^ A := by
  obtain ⟨C0, hC00, hC0⟩ := MertensTheorem.prime_inv_pminus1_bound
  refine ⟨exp (A * C0), ?_⟩
  intro n y hn hsq hle hy
  have hlogy : 0 < log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  -- Σ_{d|n} f(d) = ∏_{p|n}(1 + f p)
  have hprod := (chenDivisorWeight_isMultiplicative A).prodPrimeFactors_one_add_of_squarefree hsq
  have hfp : ∀ p ∈ n.primeFactors, chenDivisorWeight A p = A / ((p : ℝ) - 1) := by
    intro p hp
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
    unfold chenDivisorWeight
    change A ^ p.primeFactors.card / ↑p.totient = A / (↑p - 1)
    have hω : p.primeFactors.card = 1 := by
      have hpf : p.primeFactors = {p} := by
        ext q
        constructor
        · intro hq
          have hqP : q.Prime := Nat.prime_of_mem_primeFactors hq
          have hqd : q ∣ p := Nat.dvd_of_mem_primeFactors hq
          rcases hp'.eq_one_or_self_of_dvd q hqd with hq1 | hqp
          · exact absurd hq1 hqP.ne_one
          · simp [hqp]
        · intro hq
          simp at hq
          subst hq
          simp [hp']
      rw [hpf]
      simp
    have hφ : Nat.totient p = p - 1 := Nat.totient_prime hp'
    rw [hω, hφ]
    have hcast : (↑(p - 1) : ℝ) = (p : ℝ) - 1 := by
      simpa using (Nat.cast_sub (by exact hp'.one_lt.le : 1 ≤ p))
    rw [hcast]
    simp
  have hsum_eq : (n.divisors).sum (fun d =>
        A ^ (d.primeFactors.card : ℕ) / Nat.totient d) =
      n.primeFactors.prod (fun p => 1 + chenDivisorWeight A p) := by
    change (n.divisors).sum (fun d => chenDivisorWeight A d) =
      n.primeFactors.prod (fun p => 1 + chenDivisorWeight A p)
    rw [← hprod]
  -- ∏(1 + f p) ≤ exp(A·Σ 1/(p-1))
  have hprod_le : n.primeFactors.prod (fun p => 1 + chenDivisorWeight A p) ≤
      exp (A * ((n.primeFactors).sum (fun p => 1 / ((p : ℝ) - 1)))) := by
    calc
      n.primeFactors.prod (fun p => 1 + chenDivisorWeight A p)
          ≤ n.primeFactors.prod (fun p => exp (A * (1 / ((p : ℝ) - 1)))) := by
            apply Finset.prod_le_prod
            · intro p hp
              have hnonneg : 0 ≤ chenDivisorWeight A p := by
                unfold chenDivisorWeight
                exact div_nonneg (pow_nonneg (le_of_lt hA) _) (Nat.cast_nonneg _)
              linarith
            · intro p hp
              have hfp' : chenDivisorWeight A p = A / ((p : ℝ) - 1) := hfp p hp
              rw [hfp']
              have harg : A * (1 / ((p : ℝ) - 1)) = A / ((p : ℝ) - 1) := by
                rw [mul_one_div]
              rw [harg, add_comm]
              exact Real.add_one_le_exp (A / ((p : ℝ) - 1))
      _ = exp (A * ((n.primeFactors).sum (fun p => 1 / ((p : ℝ) - 1)))) := by
            have hlin : A * (n.primeFactors.sum (fun p => 1 / ((p : ℝ) - 1))) =
                n.primeFactors.sum (fun p => A * (1 / ((p : ℝ) - 1))) := by
              rw [Finset.mul_sum]
            rw [hlin, Real.exp_sum]
  -- Σ_{p|n} 1/(p-1) ≤ log(log y) + C0
  have hsum_le : (n.primeFactors).sum (fun p => 1 / ((p : ℝ) - 1)) ≤
      log (log y) + C0 := by
    have hsub : n.primeFactors ⊆ ((range (y + 1)).filter Nat.Prime) := by
      intro p hp
      have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
      exact Finset.mem_filter.mpr ⟨by simp [mem_range, hle p hp' hpd], hp'⟩
    have hle1 : (n.primeFactors).sum (fun p => 1 / ((p : ℝ) - 1)) ≤
        ((range (y + 1)).filter Nat.Prime).sum (fun p => 1 / ((p : ℝ) - 1)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _hnot => by
        have hp' : p.Prime := (mem_filter.mp hp).2
        have hpos : 0 < (p : ℝ) - 1 := by
          have : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
          linarith
        exact div_nonneg zero_le_one (le_of_lt hpos))
    exact le_trans hle1 (hC0 y hy)
  -- exp(A·Σ) ≤ exp(A·(log log y + C0)) = exp(AC0)·(log y)^A
  have hfinal : exp (A * ((n.primeFactors).sum (fun p => 1 / ((p : ℝ) - 1)))) ≤
      exp (A * C0) * (log y) ^ A := by
    have h1 : exp (A * (log (log y) + C0)) = exp (A * C0) * (log y) ^ A := by
      have hsplit : A * (log (log y) + C0) = A * log (log y) + A * C0 := by ring
      rw [hsplit, Real.exp_add]
      have hterm : exp (A * log (log y)) = (log y) ^ A := by
        calc exp (A * log (log y)) = exp (log (log y) * A) := by rw [mul_comm]
          _ = (exp (log (log y))) ^ A := by rw [Real.exp_mul]
          _ = (log y) ^ A := by
            rw [Real.exp_log (by linarith : 0 < log y)]
      rw [hterm]
      ring
    have hle : exp (A * ((n.primeFactors).sum (fun p => 1 / ((p : ℝ) - 1)))) ≤
        exp (A * (log (log y) + C0)) := by
      have hmul : A * (n.primeFactors.sum (fun p => 1 / ((p : ℝ) - 1))) ≤
          A * (log (log y) + C0) :=
        mul_le_mul_of_nonneg_left hsum_le (le_of_lt hA)
      exact Real.exp_le_exp.mpr hmul
    rwa [h1] at hle
  -- Combine the estimates.
  have hmain : (n.divisors).sum (fun d =>
        A ^ (d.primeFactors.card : ℕ) / Nat.totient d) ≤
      exp (A * C0) * (log y) ^ A := by
    rw [hsum_eq]
    exact hprod_le.trans hfinal
  exact hmain


/-! ## 6.6. Liu's correction: the case (a,d)>1 (Section IV) -/


/-! ## 8. Mathematical scope -/

/-
**Selberg upper-sieve definitions and bounds**:

1. **Definitions**:
   - `SelbergWeights`: normalization, support, and size conditions on λ_d
   - `selbergQ`: the product of primes below the cutoff that do not divide N
   - `selbergLambdaSquared`: a bridge to Mathlib's `lambdaSquared`
   - `primesInAP_weighted`: a local progression count requiring ap to be prime
   - `weightedDistributionError`: the weighted distribution error

2. **Fixed-parameter interfaces and finite algebraic results**:
   - `selberg_sieve_weights_exist` (Lemma 3 interface): weights with a pointwise remainder
   - `lemma4_numerical_bound`: a fixed-parameter remainder, not the classical integral bound
   - `integral_margin`: `0.49253 < 0.49254`, not a formalization of the integral estimate
   - `logarithmicIntegral_approx`: the local approximation term is x/log x by definition
   - `coefficient_product`: 8 × 0.49254 = 3.94032
   - `lcm_pair_count`: the combinatorial interpretation of 3^ω(d) for squarefree d
   - `divisor_sum_bound` and `divisor_sum_bound_mu2`: uniform divisor-sum bounds

3. **Pointwise bounds, distinct from classical uniform conclusions**:
   - `main_term_bound`: M₁ ≤ 3.94033 𝔖(N) N/log²N plus a pointwise remainder
   - `error_term_bound`: a fixed-parameter remainder on the N/log^A N scale,
     not Pan's mean-value theorem
   - `chenOmega_complete_bound`: Ω ≤ 3.9404 𝔖(N) N/log²N plus a remainder
   - `chenOmega_simple_bound`: the same pointwise shape without ε
   - `coprime_condition_implies_bounded_ap`: (a,d)>1 implies π ≤ 1 for the local count

4. **Mathlib correspondences**:
   - `selberg_lambda_is_upper_moebius`: Selberg weights give `IsUpperMoebius`
   - `omega_upper_bound_via_mathlib`: `siftedSum_le_mainSum_errSum_of_upperMoebius`
   - `mainSum_diag_via_mathlib`: `mainSum_lambdaSquared_eq_sum_mul_sum_sq`
   - `mainSum_cauchy_schwarz_lower_bound`: the finite Cauchy-Schwarz lower bound

5. **Requirements for the classical uniform bounds**:
   - Lemma 3 requires optimized Selberg weights and analytic estimates,
     beyond the Mathlib Λ²-sieve diagonalization and the bridges here.
   - Lemma 4 requires Mertens' theorem, partial summation, and the integral bound.
   - The error estimate requires Pan's mean-value theorem
     (see `BombieriVinogradov.lean`) and control of the noncoprime contribution.

6. **Numerical constants**:
   - 8 × 0.49254 = 3.94032 < 3.94033 (main-term coefficient with a margin)
   - 0.49254 (the integral upper bound in Chen 1973, equation (28))
   - 3.9404 = 3.94033 + 0.00007 (including the error margin)
-/

end MathlibNt.SieveTheory.SelbergUpperBound
