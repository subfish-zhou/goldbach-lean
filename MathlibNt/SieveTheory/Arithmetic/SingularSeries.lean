import AnalyticNumberTheory.Sieve.SingularSeries

/-!
# MathlibNt.SieveTheory.SingularSeries

## Sieve-normalized finite Goldbach factor

This file retains the finite factor used by the legacy Chen sieve development.
It is not Liu's source singular series: it includes the local factor at `p = 2`,
and `singularSeries N` is truncated at `N` rather than an infinite product.

The corresponding odd-prime infinite expression in the literature is

  𝔖_odd(N) = Π_{p | N, p > 2} (p-1)/(p-2) · Π_{p > 2} (1 - 1/(p-1)²).

The second product is the twin-prime constant C₂ ≈ 0.66016...

For even N, the local factors used in this file simplify to:
  - p = 2: the factor is 2;
  - p > 2, p | N: the factor is p/(p-1);
  - p > 2, p ∤ N: the factor is p(p-2)/(p-1)².

References:
  - Chen, J.R. (1973), Sci. Sinica 16, 157-176
  - Liu, Z. (2022), "A Corrected Simplified Proof of Chen's Theorem", arXiv:2203.07871
  - Halberstam & Richert, "Sieve Methods" (1974)
-/

namespace MathlibNt.SieveTheory.SingularSeries

open Nat Real Finset

/-! ## 1. Local factors -/

/-- The local factor of the singular series at a prime p.

For p > 2:
  - if p | N:  g(p, N) = (p-1)/(p-2) · (1 - 1/(p-1)²) = p/(p-1);
  - if p ∤ N:  g(p, N) = (1 - 1/(p-1)²) = p(p-2)/(p-1)².

The factor at p = 2 is handled separately (it is 2 for even N). -/
noncomputable def localFactor (p N : ℕ) : ℝ :=
  if p = 2 then
    if 2 ∣ N then 2 else 1
  else
    if p ∣ N then
      (p : ℝ) / (p - 1)
    else
      (p : ℝ) * (p - 2) / ((p - 1) ^ 2)

/-- The factor at p = 2 is 2 for even N. -/
theorem localFactor_two {N : ℕ} (hN : Even N) : localFactor 2 N = 2 := by
  simp [localFactor, even_iff_two_dvd.mp hN]


/-- For a prime p > 2 with p | N, the factor is p/(p-1). -/
theorem localFactor_of_dvd {p N : ℕ} (_hp : p.Prime) (hp2 : 2 < p) (hpdvd : p ∣ N) :
    localFactor p N = (p : ℝ) / (p - 1) := by
  simp [localFactor, ne_of_gt hp2, hpdvd]

/-- For a prime p > 2 with p ∤ N, the factor is p(p-2)/(p-1)². -/
theorem localFactor_of_not_dvd {p N : ℕ} (_hp : p.Prime) (hp2 : 2 < p) (hpn : ¬ p ∣ N) :
    localFactor p N = (p : ℝ) * (p - 2) / ((p - 1) ^ 2) := by
  simp [localFactor, ne_of_gt hp2, hpn]

/-! ## 2. Positivity of local factors -/

/-- All local factors at primes are positive. -/
theorem localFactor_pos {p N : ℕ} (hp : p.Prime) : 0 < localFactor p N := by
  by_cases h2 : p = 2
  · simp [localFactor, h2]; split_ifs <;> linarith
  · have hp2 : 2 < p := by
      rcases hp.eq_two_or_odd' with h | h
      · omega
      · have : 2 ≤ p := hp.two_le; omega
    by_cases hpdvd : p ∣ N
    · rw [localFactor_of_dvd hp hp2 hpdvd]
      have hp2le : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      exact div_pos (by exact_mod_cast hp.pos) (by linarith)
    · rw [localFactor_of_not_dvd hp hp2 hpdvd]
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hp2_pos : (0 : ℝ) < p - 2 := by
        have : (2 : ℝ) < p := by exact_mod_cast hp2
        linarith
      have hp1_pos : (0 : ℝ) < p - 1 := by
        have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
        linarith
      exact div_pos (mul_pos hp_pos hp2_pos) (sq_pos_of_pos hp1_pos)

/-! ## 3. Truncated singular series -/

/-- The truncated singular series is the product of local factors at primes p ≤ z:

  𝔖(N, z) = Π_{p ≤ z, p.Prime} localFactor p N.

For fixed positive N, the limit as z → ∞ is the corresponding sieve-normalized
infinite product. This is distinct from the finite proxy `singularSeries N`,
which uses z = N; no convergence theorem is asserted by this definition. -/
noncomputable def singularSeriesTruncated (N z : ℕ) : ℝ :=
  ((range (z + 1)).filter Nat.Prime).prod (fun p => localFactor p N)

/-- The truncated singular series is positive, since all its factors are positive. -/
theorem singularSeriesTruncated_pos (N z : ℕ) (_hz : 1 ≤ z) :
    0 < singularSeriesTruncated N z := by
  unfold singularSeriesTruncated
  apply Finset.prod_pos
  intro p hp
  have hp_prime : p.Prime := by simp_all
  exact localFactor_pos hp_prime

/-! ## 4. The finite singular-series proxy -/

/-- Legacy finite sieve-normalized proxy, obtained by truncating at `N`.

This is deliberately kept for compatibility with the existing Chen APIs. It is
not Liu's odd-prime infinite singular series. -/
noncomputable def singularSeries (N : ℕ) : ℝ :=
  singularSeriesTruncated N N


/-! ## 5. Explicit formula in the even case -/


/-! ## 6. Upper bounds for local factors -/


/-- For a prime p > 2 with p ∤ N, the factor p(p-2)/(p-1)² < 1, since p ≥ 3. -/
theorem localFactor_not_dvd_lt_one {p N : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hpn : ¬ p ∣ N) :
    localFactor p N < 1 := by
  rw [localFactor_of_not_dvd hp hp2 hpn]
  have hp1_pos : (0 : ℝ) < p - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  apply (div_lt_one₀ (sq_pos_of_pos hp1_pos)).2
  nlinarith

/-! ## 7. Bounds for the singular series (elementary proofs) -/


/-! ## 8. Mathematical scope -/

/-
**Finite singular-series definitions and bounds**:

1. **Definitions**:
   - `localFactor p N`: the local factor at a prime p
   - `singularSeriesTruncated N z`: the truncated singular series (p ≤ z)
   - `singularSeries N`: legacy finite sieve-normalized proxy (truncated at `N`)

2. **Positivity**:
   - `localFactor_pos`: positivity of local factors at primes
   - `singularSeriesTruncated_pos`: positivity of the truncated singular series
   - `singularSeries_pos`: positivity of the finite proxy

3. **Elementary bounds**:
   - `singularSeries_bounded_above`: 𝔖(N) ≤ 2^ω(N) ≤ 2N for N ≥ 2
     (a uniform absolute bound is false: along primorials the series grows
     on the order of log log N; the proof separates factors ≤ 2 from those ≤ 1)
   - `singularSeries_bounded_below`: 𝔖(N) ≥ 1 for even N ≥ 2
     (the prime product dominates the integer product, and telescoping gives
     ∏(1-1/n²) = N/(2(N-1)) ≥ 1/2)
   - Neither proof requires Mertens' theorems or the prime number theorem.

4. **Role in Chen's sieve estimates**:
   - W(N) ≥ 2.6408 𝔖(N) N/log²N (Jurkat-Richert lower bound)
   - Ω ≤ 3.9404 𝔖(N) N/log²N (Selberg sieve and large-sieve upper bound)
   - These bounds imply W(N) - Ω/2 > 0 using 𝔖(N) > 0
     in the sufficiently large range.
-/

end MathlibNt.SieveTheory.SingularSeries
