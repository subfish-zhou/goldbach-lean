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
theorem localFactor_two (hN : Even N) : localFactor 2 N = 2 := by
  simp [localFactor, even_iff_two_dvd.mp hN]

/-- The factor at p = 2 is 1 for odd N. -/
theorem localFactor_two_odd (hN : Odd N) : localFactor 2 N = 1 := by
  simp [localFactor, hN.not_two_dvd_nat]

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

/-- The finite singular-series proxy is positive. -/
theorem singularSeries_pos (N : ℕ) (hN : 2 ≤ N) :
    0 < singularSeries N := by
  exact singularSeriesTruncated_pos N N (by omega : 1 ≤ N)

/-! ## 5. Explicit formula in the even case -/

/-- For even N, the singular series contains the factor 2 at p = 2;
the truncation at 2 consists of this factor alone. -/
theorem singularSeries_even_factor (N : ℕ) (hN : Even N) (_hN2 : 2 ≤ N) :
    singularSeriesTruncated N 2 = 2 := by
  unfold singularSeriesTruncated
  have h_range : (range 3).filter Nat.Prime = {2} := by decide
  rw [h_range]
  simp [localFactor_two hN]

/-! ## 6. Upper bounds for local factors -/

/-- For a prime p > 2 with p | N, the factor p/(p-1) ≤ 3/2, since p ≥ 3. -/
theorem localFactor_dvd_le {p N : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hpdvd : p ∣ N) :
    localFactor p N ≤ 3 / 2 := by
  rw [localFactor_of_dvd hp hp2 hpdvd]
  have hp3 : 3 ≤ p := by omega
  have hp1 : (0 : ℝ) < p - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  apply (div_le_iff₀ hp1).2
  have hp3' : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  linarith

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

/-- Lower bound at an odd prime p > 2: localFactor p N ≥ 1 - 1/(p-1)². -/
private lemma localFactor_ge_square {p N : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    1 - 1 / ((p : ℝ) - 1) ^ 2 ≤ localFactor p N := by
  by_cases hpdvd : p ∣ N
  · rw [localFactor_of_dvd hp hp2 hpdvd]
    have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      linarith
    field_simp [ne_of_gt hp1_pos]
    nlinarith [show (0 : ℝ) ≤ (p : ℝ) by exact_mod_cast (Nat.zero_le p)]
  · rw [localFactor_of_not_dvd hp hp2 hpdvd]
    have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      linarith
    field_simp [ne_of_gt hp1_pos]
    nlinarith

/-- Telescoping product: ∏_{n=2}^{N-1} (1 - 1/n²) = N / (2(N-1)) for N ≥ 2. -/
private lemma int_square_product (N : ℕ) (hN : 2 ≤ N) :
    (Finset.Ico 2 N).prod (fun n : ℕ => (1 : ℝ) - 1 / (n : ℝ) ^ 2) =
      (N : ℝ) / (2 * ((N : ℝ) - 1)) := by
  exact AnalyticNumberTheory.Sieve.int_square_product N hN

/-- The product over primes dominates the product over all integers:
∏_{3 ≤ p ≤ N, p prime} (1 - 1/(p-1)²) ≥ ∏_{n=2}^{N-1} (1 - 1/n²). -/
private lemma prime_square_product_ge_int (N : ℕ) :
    (Finset.Ico 2 N).prod (fun n : ℕ => (1 : ℝ) - 1 / (n : ℝ) ^ 2) ≤
      ((range (N + 1)).filter (fun p => Nat.Prime p ∧ 2 < p)).prod
        (fun p => 1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  exact AnalyticNumberTheory.Sieve.prime_square_product_ge_int N

/-- The local factor is at most 2 for every prime p. -/
private lemma localFactor_le_two {p N : ℕ} (hp : p.Prime) : localFactor p N ≤ 2 := by
  by_cases h2 : p = 2
  · subst h2
    unfold localFactor
    split_ifs <;> norm_num
  · have hp2 : 2 < p := by
      rcases hp.eq_two_or_odd' with h | h
      · exact absurd h h2
      · have : 2 ≤ p := hp.two_le
        omega
    by_cases hpdvd : p ∣ N
    · exact (localFactor_dvd_le hp hp2 hpdvd).trans (by norm_num)
    · exact le_trans (le_of_lt (localFactor_not_dvd_lt_one hp hp2 hpdvd)) (by norm_num)

/-- The local factor is at most 1 when the prime p does not divide N. -/
private lemma localFactor_le_one_of_not_dvd {p N : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ N) :
    localFactor p N ≤ 1 := by
  by_cases h2 : p = 2
  · subst h2
    unfold localFactor
    simp [hpn]
  · have hp2 : 2 < p := by
      rcases hp.eq_two_or_odd' with h | h
      · exact absurd h h2
      · have : 2 ≤ p := hp.two_le
        omega
    exact le_of_lt (localFactor_not_dvd_lt_one hp hp2 hpn)

/-- A positive lower bound for the finite singular series: 𝔖(N) ≥ 1
for every even N ≥ 2.

Elementary proof: for even N, with all prime products restricted to p ≤ N,
𝔖(N) = 2 · ∏_{p|N, p>2} p/(p-1) · ∏_{p∤N, p>2} p(p-2)/(p-1)².
Here p/(p-1) ≥ 1, and the prime product ∏_{2<p≤N} (1 - 1/(p-1)²)
is at least ∏_{n=2}^{N-1} (1 - 1/n²) = N/(2(N-1)) ≥ 1/2
by telescoping. Thus 𝔖(N) ≥ 2 · 1 · 1/2 = 1. -/
theorem singularSeries_bounded_below :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 2 ≤ N → Even N → c ≤ singularSeries N := by
  refine ⟨1, by norm_num, ?_⟩
  intro N hN hEven
  unfold singularSeries singularSeriesTruncated
  set A := (range (N + 1)).filter Nat.Prime with hA_def
  have h2mem : 2 ∈ A := by
    rw [hA_def]
    simp [mem_filter, hN, Nat.prime_two]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem h2mem]
  rw [localFactor_two hEven]
  have hfilter_eq : A \ {2} = (range (N + 1)).filter (fun p => Nat.Prime p ∧ 2 < p) := by
    rw [hA_def]
    ext p
    constructor
    · intro hp
      rw [mem_sdiff, mem_filter] at hp
      rcases hp with ⟨hp_mem, hp_ne⟩
      rcases hp_mem with ⟨hp_range, hp_prime⟩
      rw [mem_filter]
      refine ⟨hp_range, hp_prime, ?_⟩
      have hp_ne' : p ≠ 2 := by
        intro h
        exact hp_ne (by simp [h])
      rcases hp_prime.eq_two_or_odd' with h2 | hodd
      · exact absurd h2 hp_ne'
      · have : 2 ≤ p := hp_prime.two_le
        omega
    · intro hp
      rw [mem_filter] at hp
      rcases hp with ⟨hp_range, hp_props⟩
      rcases hp_props with ⟨hp_prime, hp2⟩
      rw [mem_sdiff, mem_filter]
      constructor
      · exact ⟨hp_range, hp_prime⟩
      · intro hp_mem2
        have hp_eq2 : p = 2 := by simpa using hp_mem2
        omega
  rw [hfilter_eq]
  have hfac : ((range (N + 1)).filter (fun p => Nat.Prime p ∧ 2 < p)).prod
        (fun p => 1 - 1 / ((p : ℝ) - 1) ^ 2) ≤
      ((range (N + 1)).filter (fun p => Nat.Prime p ∧ 2 < p)).prod
        (fun p => localFactor p N) := by
    apply Finset.prod_le_prod
    · intro p hp
      rw [mem_filter] at hp
      have hp3 : 3 ≤ p := by omega
      have hp1_ge : (1 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by
        have : (2 : ℝ) ≤ (p : ℝ) - 1 := by
          have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
          linarith
        nlinarith
      have hdiv : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
        exact div_le_one_of_le₀ hp1_ge (sq_nonneg ((p : ℝ) - 1))
      linarith
    · intro p hp
      rw [mem_filter] at hp
      exact localFactor_ge_square hp.2.1 hp.2.2
  have htel : (N : ℝ) / (2 * ((N : ℝ) - 1)) ≤
      ((range (N + 1)).filter (fun p => Nat.Prime p ∧ 2 < p)).prod
        (fun p => 1 - 1 / ((p : ℝ) - 1) ^ 2) := by
    rw [← int_square_product N hN]
    exact prime_square_product_ge_int N
  calc
    (1 : ℝ) ≤ 2 * ((N : ℝ) / (2 * ((N : ℝ) - 1))) := by
      have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by
        have : (2 : ℝ) ≤ N := by exact_mod_cast hN
        linarith
      field_simp
      nlinarith [show (2 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN]
    _ ≤ 2 * ((range (N + 1)).filter (fun p => Nat.Prime p ∧ 2 < p)).prod
        (fun p => 1 - 1 / ((p : ℝ) - 1) ^ 2) :=
          mul_le_mul_of_nonneg_left htel (by norm_num)
    _ ≤ 2 * ((range (N + 1)).filter (fun p => Nat.Prime p ∧ 2 < p)).prod
        (fun p => localFactor p N) :=
          mul_le_mul_of_nonneg_left hfac (by norm_num)

/-- Upper bound for the truncated definition: 𝔖(N) ≤ 2^ω(N) ≤ 2N.

A bound 𝔖(N) ≤ C with an absolute constant C is **false**: along primorials
(products of all primes up to x, such as 2·3·5·7·...),
the factors ∏_{p|N} p/(p-1) grow on the order of log log N, while the
remaining product stays bounded away from zero, so 𝔖(N) is unbounded.
The elementary bound uses local factors ≤ 2 when p | N and ≤ 1 otherwise.
It gives 𝔖(N) ≤ 2^ω(N), and hence also the looser bound
𝔖(N) ≤ 2^{ω(N)+1} ≤ 2N. -/
theorem singularSeries_bounded_above :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → singularSeries N ≤ C * (N : ℝ) := by
  refine ⟨2, by norm_num, ?_⟩
  intro N hN
  unfold singularSeries singularSeriesTruncated
  set A := (range (N + 1)).filter Nat.Prime with hA_def
  have prime_of_mem_A {p : ℕ} (hp : p ∈ A) : p.Prime := (mem_filter.mp hp).2
  have hsplit := Finset.prod_filter_mul_prod_filter_not A (fun p => p ∣ N)
    (fun p => localFactor p N)
  -- First part (p | N): each of the ω(N) factors is at most 2.
  have h1 : (A.filter (fun p => p ∣ N)).prod (fun p => localFactor p N) ≤
      (2 : ℝ) ^ (A.filter (fun p => p ∣ N)).card := by
    calc
      (A.filter (fun p => p ∣ N)).prod (fun p => localFactor p N)
          ≤ (A.filter (fun p => p ∣ N)).prod (fun _ => (2 : ℝ)) := by
              apply Finset.prod_le_prod
              · intro p hp
                rw [mem_filter] at hp
                have hpA : p ∈ A := hp.1
                have hpPrime : p.Prime := prime_of_mem_A hpA
                exact le_of_lt (localFactor_pos hpPrime)
              · intro p hp
                rw [mem_filter] at hp
                have hpA : p ∈ A := hp.1
                have hpPrime : p.Prime := prime_of_mem_A hpA
                exact localFactor_le_two hpPrime
      _ = (2 : ℝ) ^ (A.filter (fun p => p ∣ N)).card := by
              rw [Finset.prod_const]
  -- Second part (p ∤ N): each factor is at most 1.
  have h2 : (A.filter (fun p => ¬ p ∣ N)).prod (fun p => localFactor p N) ≤ 1 := by
    apply Finset.prod_le_one
    · intro p hp
      rw [mem_filter] at hp
      have hpA : p ∈ A := hp.1
      have hpPrime : p.Prime := prime_of_mem_A hpA
      exact le_of_lt (localFactor_pos hpPrime)
    · intro p hp
      rw [mem_filter] at hp
      have hpA : p ∈ A := hp.1
      have hpPrime : p.Prime := prime_of_mem_A hpA
      exact localFactor_le_one_of_not_dvd hpPrime hp.2
  -- 2^ω(N) ≤ N
  have hpow : (2 : ℝ) ^ (A.filter (fun p => p ∣ N)).card ≤ (N : ℝ) := by
    have hsubset : A.filter (fun p => p ∣ N) ⊆ N.primeFactors := by
      intro p hp
      rw [mem_filter] at hp
      rcases hp with ⟨hpA, hpdvd⟩
      rw [mem_filter] at hpA
      exact (Nat.mem_primeFactors_of_ne_zero (by omega : N ≠ 0)).2 ⟨hpA.2, hpdvd⟩
    have hcard : (A.filter (fun p => p ∣ N)).card ≤ N.primeFactors.card :=
      Finset.card_le_card hsubset
    calc
      (2 : ℝ) ^ (A.filter (fun p => p ∣ N)).card ≤ (2 : ℝ) ^ N.primeFactors.card :=
          by
            have hpow_nat : 2 ^ (A.filter (fun p => p ∣ N)).card ≤ 2 ^ N.primeFactors.card :=
              Nat.pow_le_pow_right (by norm_num) hcard
            exact_mod_cast hpow_nat
      _ = (N.primeFactors.prod fun _ => (2 : ℝ)) := by
          rw [← Finset.prod_const]
      _ ≤ N.primeFactors.prod (fun p => (p : ℝ)) := by
          apply Finset.prod_le_prod
          · intro p hp
            norm_num
          · intro p hp
            have hp2 : (2 : ℝ) ≤ p := by
              exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
            linarith
      _ ≤ (N : ℝ) := by
          have hdvd_nat : (N.primeFactors.prod fun p => p) ∣ N := Nat.prod_primeFactors_dvd N
          have hNpos : 0 < N := by omega
          have hle_nat : N.primeFactors.prod (fun p => p) ≤ N :=
            Nat.le_of_dvd hNpos hdvd_nat
          rw [← cast_prod]
          exact_mod_cast hle_nat
  calc
    A.prod (fun p => localFactor p N)
        = (A.filter (fun p => p ∣ N)).prod (fun p => localFactor p N) *
          (A.filter (fun p => ¬ p ∣ N)).prod (fun p => localFactor p N) := hsplit.symm
    _ ≤ (2 : ℝ) ^ (A.filter (fun p => p ∣ N)).card * 1 :=
            by
              have h3 : 0 ≤ (A.filter (fun p => ¬ p ∣ N)).prod (fun p => localFactor p N) := by
                apply Finset.prod_nonneg
                intro p hp
                rw [mem_filter] at hp
                have hpA : p ∈ A := hp.1
                have hpPrime : p.Prime := prime_of_mem_A hpA
                exact le_of_lt (localFactor_pos hpPrime)
              have h4 : (0 : ℝ) ≤ (2 : ℝ) ^ (A.filter (fun p => p ∣ N)).card := by positivity
              exact mul_le_mul h1 h2 h3 h4
    _ = (2 : ℝ) ^ (A.filter (fun p => p ∣ N)).card := by ring
    _ ≤ (N : ℝ) := hpow
    _ ≤ 2 * (N : ℝ) := by
        have hN0 : (0 : ℝ) ≤ N := by exact_mod_cast (by omega : 0 ≤ N)
        nlinarith

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
