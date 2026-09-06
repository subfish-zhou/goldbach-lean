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

/-- The factor at 2 is 2 for even `N`. -/
theorem localFactor_two (hN : Even N) : localFactor 2 N = 2 := by
  simp [localFactor, hN.two_dvd]

/-- The factor at 2 is 1 for odd `N`. -/
theorem localFactor_two_odd (hN : Odd N) : localFactor 2 N = 1 := by
  simp [localFactor, hN.not_two_dvd_nat]

/-- For a prime `p > 2` dividing `N`, the factor is `p/(p-1)`. -/
theorem localFactor_of_dvd {p N : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hpdvd : p ∣ N) :
    localFactor p N = (p : ℝ) / (p - 1) := by
  simp [localFactor, ne_of_gt hp2, hpdvd]

/-- For a prime `p > 2` not dividing `N`,
the factor is `p(p-2)/(p-1)²`. -/
theorem localFactor_of_not_dvd {p N : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hpn : ¬ p ∣ N) :
    localFactor p N = (p : ℝ) * (p - 2) / ((p - 1) ^ 2) := by
  simp [localFactor, ne_of_gt hp2, hpn]

/-! ## 2. Positivity of local factors -/

/-- Every prime local factor is positive. -/
theorem localFactor_pos {p N : ℕ} (hp : p.Prime) : 0 < localFactor p N := by
  by_cases h2 : p = 2
  · simp [localFactor, h2]; split_ifs <;> linarith
  · have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm h2)
    by_cases hpdvd : p ∣ N
    · rw [localFactor_of_dvd hp hp2 hpdvd]
      have hp2le : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      exact div_pos (by exact_mod_cast hp.pos) (by linarith)
    · rw [localFactor_of_not_dvd hp hp2 hpdvd]
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hp2_pos : (0 : ℝ) < p - 2 := by
        exact sub_pos.mpr (by exact_mod_cast hp2)
      have hp1_pos : (0 : ℝ) < p - 1 := by
        exact sub_pos.mpr (by exact_mod_cast hp.one_lt)
      exact div_pos (mul_pos hp_pos hp2_pos) (sq_pos_of_pos hp1_pos)

/-! ## 3. Truncated singular series -/

/-- Truncated local-factor product:
`𝔖(N,z) = Π_{p≤z, p.Prime} localFactor p N`.
The classical infinite product is obtained by a convergence argument
as `z → ∞`, with the normalization of these local factors;
that limiting identification is not part of this definition. -/
noncomputable def singularSeriesTruncated (N z : ℕ) : ℝ :=
  ((range (z + 1)).filter Nat.Prime).prod (fun p => localFactor p N)

/-- The truncated singular series is positive, since all factors
are positive. -/
theorem singularSeriesTruncated_pos (N z : ℕ) (hz : 1 ≤ z) :
    0 < singularSeriesTruncated N z := by
  unfold singularSeriesTruncated
  apply Finset.prod_pos
  intro p hp
  have hp_prime : p.Prime := by simp_all
  exact localFactor_pos hp_prime

/-! ## 4. Finite singular-series proxy -/

/-- Finite singular-series proxy, truncated at `z=N`.
The classical full series is a limit
`lim_{z→∞} 𝔖(N,z)`, requiring an infinite-product convergence
argument. Mertens-type estimates such as
`Σ_{p≤x}1/p ~ log log x` are relevant to quantitative
singular-series analysis; this definition does not take that limit. -/
noncomputable def singularSeries (N : ℕ) : ℝ :=
  -- Use the finite truncated product at the specified cutoff.
  -- The cutoff is z = N; an infinite-product definition would require a separate convergence argument.
  singularSeriesTruncated N N

/-- The finite singular-series proxy is positive. -/
theorem singularSeries_pos (N : ℕ) (hN : 2 ≤ N) :
    0 < singularSeries N := by
  exact singularSeriesTruncated_pos N N (by omega : 1 ≤ N)

/-! ## 5. Explicit even case -/

/-- For even `N`, truncating at 2 gives exactly the factor 2. -/
theorem singularSeries_even_factor (N : ℕ) (hN : Even N) (hN2 : 2 ≤ N) :
    singularSeriesTruncated N 2 = 2 := by
  unfold singularSeriesTruncated
  have h_range : (range 3).filter Nat.Prime = {2} := by decide
  rw [h_range]
  simp [localFactor_two hN]

/-! ## 6. Upper bounds for local factors -/

/-- For a prime `p > 2` dividing `N`, `p/(p-1) ≤ 3/2`,
since `p ≥ 3`. -/
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

/-- For a prime `p > 2` not dividing `N`,
`p(p-2)/(p-1)² < 1`, since `p ≥ 3`. -/
theorem localFactor_not_dvd_lt_one {p N : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hpn : ¬ p ∣ N) :
    localFactor p N < 1 := by
  rw [localFactor_of_not_dvd hp hp2 hpn]
  have hp1_pos : (0 : ℝ) < p - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  -- The positive denominator exceeds the numerator by exactly one.
  apply (div_lt_one (sq_pos_of_pos hp1_pos)).2
  nlinarith

/-! ## 7. Elementary singular-series bounds -/

/-- For an odd prime `p`,
`localFactor p N ≥ 1-1/(p-1)²`. -/
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

/-- Telescoping product A: `∏_{k<n} (k+1)/(k+2) = 1/(n+1)`. -/
lemma telescope_a (n : ℕ) :
    (Finset.range n).prod (fun k : ℕ => ((k : ℝ) + 1) / ((k : ℝ) + 2)) =
      1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
      have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
      norm_num [Nat.cast_add]
      field_simp [hn1, hn2]
      ring

/-- Telescoping product B: `∏_{k<n} (k+3)/(k+2) = (n+2)/2`. -/
lemma telescope_b (n : ℕ) :
    (Finset.range n).prod (fun k : ℕ => ((k : ℝ) + 3) / ((k : ℝ) + 2)) =
      ((n : ℝ) + 2) / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
      norm_num [Nat.cast_add]
      field_simp [hn2]
      ring

/-- Telescoping product:
`∏_{n=2}^{N-1} (1-1/n²) = N/(2(N-1))` for `N ≥ 2`. -/
lemma int_square_product (N : ℕ) (hN : 2 ≤ N) :
    (Finset.Ico 2 N).prod (fun n : ℕ => (1 : ℝ) - 1 / (n : ℝ) ^ 2) =
      (N : ℝ) / (2 * ((N : ℝ) - 1)) := by
  rw [Finset.prod_Ico_eq_prod_range (fun n : ℕ => (1 : ℝ) - 1 / (n : ℝ) ^ 2) 2 N]
  have hfac : ∀ k : ℕ,
      1 - 1 / ((2 + k : ℕ) : ℝ) ^ 2 =
        (((k : ℝ) + 1) / ((k : ℝ) + 2)) * (((k : ℝ) + 3) / ((k : ℝ) + 2)) := by
    intro k
    have hk2 : (k : ℝ) + 2 ≠ 0 := by
      have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast Nat.zero_le k
      nlinarith
    norm_num [Nat.cast_add]
    field_simp [hk2]
    ring
  rw [Finset.prod_congr rfl (fun k hk => hfac k)]
  rw [Finset.prod_mul_distrib]
  have h1 : (Finset.range (N - 2)).prod (fun k : ℕ => ((k : ℝ) + 1) / ((k : ℝ) + 2)) =
      1 / ((N : ℝ) - 1) := by
    rw [telescope_a (N - 2)]
    have hcast : (((N - 2 : ℕ) : ℝ) + 1) = (N : ℝ) - 1 := by
      rw [Nat.cast_sub hN]
      ring
    rw [hcast]
  have h2 : (Finset.range (N - 2)).prod (fun k : ℕ => ((k : ℝ) + 3) / ((k : ℝ) + 2)) =
      (N : ℝ) / 2 := by
    rw [telescope_b (N - 2)]
    have hcast : (((N - 2 : ℕ) : ℝ) + 2) = (N : ℝ) := by
      rw [Nat.cast_sub hN]
      ring
    rw [hcast]
  rw [h1, h2]
  have hN1 : (N : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) ≤ (N : ℝ) - 1 := by
      have : (2 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    linarith
  field_simp [hN1]

/-- The prime-indexed product is at least the full integer product:
`∏_{3≤p≤N, p prime} (1-1/(p-1)²)
 ≥ ∏_{n=2}^{N-1} (1-1/n²)`. -/
lemma prime_square_product_ge_int (N : ℕ) :
    (Finset.Ico 2 N).prod (fun n : ℕ => (1 : ℝ) - 1 / (n : ℝ) ^ 2) ≤
      ((range (N + 1)).filter (fun p => Nat.Prime p ∧ 2 < p)).prod
        (fun p => 1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  classical
  let T : Finset ℕ := (Finset.Ico 2 N).filter (fun n => (n + 1).Prime)
  have hsubset : T ⊆ Finset.Ico 2 N := Finset.filter_subset _ _
  have h_int_le_T :
      (Finset.Ico 2 N).prod (fun n : ℕ => (1 : ℝ) - 1 / (n : ℝ) ^ 2) ≤
        T.prod (fun n : ℕ => (1 : ℝ) - 1 / (n : ℝ) ^ 2) := by
    exact Finset.prod_le_prod_of_subset_of_le_one hsubset
      (by
        intro n hn
        have hn2 : (2 : ℝ) ≤ n := by
          exact_mod_cast (mem_Ico.mp hn).1
        have hn1 : (1 : ℝ) ≤ n ^ 2 := by nlinarith
        have hdiv : (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 :=
          div_le_one_of_le₀ hn1 (by exact_mod_cast (sq_nonneg n) : (0 : ℝ) ≤ n ^ 2)
        linarith)
      (by
        intro n hn hnT
        have hsq : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 2 := div_nonneg zero_le_one (sq_nonneg _)
        linarith)
  have hreindex :
      T.prod (fun n : ℕ => (1 : ℝ) - 1 / (n : ℝ) ^ 2) =
        ((range (N + 1)).filter (fun p => Nat.Prime p ∧ 2 < p)).prod
          (fun p => 1 - 1 / ((p : ℝ) - 1) ^ 2) := by
    symm
    refine Finset.prod_bij (fun p hp => p - 1) ?_ ?_ ?_ ?_
    · intro p hp
      rw [mem_filter] at hp
      rcases hp with ⟨hp_range, hp_prime, hp2⟩
      have hp_lt : p < N + 1 := mem_range.mp hp_range
      have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel (by omega : 1 ≤ p)
      have hp1_ge2 : 2 ≤ p - 1 := by omega
      have hp1_lt : p - 1 < N := by omega
      have hp1_prime : (p - 1 + 1).Prime := by rwa [hp1]
      simp [T, mem_filter, hp1_ge2, hp1_lt, hp1_prime]
    · intro p hp
      intro p' hp' hpp'
      rw [mem_filter] at hp hp'
      rcases hp with ⟨_, _, hp2⟩
      rcases hp' with ⟨_, _, hp2'⟩
      omega
    · intro n hn
      rw [mem_filter] at hn
      rcases hn with ⟨hn_Ico, hn_prime⟩
      have hn2 : 2 ≤ n := (mem_Ico.mp hn_Ico).1
      have hnlt : n < N := (mem_Ico.mp hn_Ico).2
      refine ⟨n + 1, ?_, ?_⟩
      · rw [mem_filter]
        exact ⟨mem_range.mpr (by omega), hn_prime, by omega⟩
      · omega
    · intro p hp
      rw [mem_filter] at hp
      rcases hp with ⟨_, _, hp2⟩
      have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ p)]
        norm_num
      rw [hcast]
  exact le_trans h_int_le_T hreindex.le

/-- Every prime local factor is at most 2. -/
private lemma localFactor_le_two {p N : ℕ} (hp : p.Prime) : localFactor p N ≤ 2 := by
  by_cases h2 : p = 2
  · subst h2
    unfold localFactor
    split_ifs <;> norm_num
  · have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm h2)
    by_cases hpdvd : p ∣ N
    · exact (localFactor_dvd_le hp hp2 hpdvd).trans (by norm_num)
    · exact le_trans (le_of_lt (localFactor_not_dvd_lt_one hp hp2 hpdvd)) (by norm_num)

/-- If the prime `p` does not divide `N`, its local factor is at most 1. -/
private lemma localFactor_le_one_of_not_dvd {p N : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ N) :
    localFactor p N ≤ 1 := by
  by_cases h2 : p = 2
  · subst h2
    unfold localFactor
    simp [hpn]
  · have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm h2)
    exact le_of_lt (localFactor_not_dvd_lt_one hp hp2 hpn)

/-- **Positive lower bound for even N**: the finite proxy is at
least 1 for every even `N ≥ 2`.
Its product is
`2·∏_{p≤N, p|N, p>2} p/(p-1)
 ·∏_{p≤N, p∤N, p>2} p(p-2)/(p-1)²`.
The divisor factors are at least 1, and
`∏_{2<p≤N}(1-1/(p-1)²)
 ≥ ∏_{n=2}^{N-1}(1-1/n²)
 = N/(2(N-1)) ≥ 1/2`.
Thus the product is at least `2·1·1/2 = 1`. -/
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
    simp only [mem_sdiff, mem_filter, mem_singleton]
    constructor
    · rintro ⟨⟨hp_range, hp⟩, hp_ne⟩
      exact ⟨hp_range, hp, lt_of_le_of_ne hp.two_le (Ne.symm hp_ne)⟩
    · rintro ⟨hp_range, hp, hp2⟩
      exact ⟨⟨hp_range, hp⟩, ne_of_gt hp2⟩
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

/-- **Upper bound for the finite proxy**: for `N ≥ 2`,
the local-factor estimates give `𝔖(N) ≤ 2^{ω(N)}`
and in particular the stated bound `≤ 2N`.
Each factor at a prime dividing `N` is at most 2; the others
are at most 1. The coarser `2^{ω(N)+1} ≤ 2N` also suffices.

An absolute bound `𝔖(N) ≤ C` is false. For primorials
`N = 2·3·5·7·...·x`, the divisor-prime product
`∏_{p|N} p/(p-1)` has order `log log N` and is unbounded;
the remaining twin-prime-type factors do not remove that growth. -/
theorem singularSeries_bounded_above :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → singularSeries N ≤ C * (N : ℝ) := by
  refine ⟨2, by norm_num, ?_⟩
  intro N hN
  unfold singularSeries singularSeriesTruncated
  set A := (range (N + 1)).filter Nat.Prime with hA_def
  have hsplit := Finset.prod_filter_mul_prod_filter_not A (fun p => p ∣ N)
    (fun p => localFactor p N)
  -- For p|N, each local factor is at most 2, with ω(N) such primes.
  have h1 : (A.filter (fun p => p ∣ N)).prod (fun p => localFactor p N) ≤
      (2 : ℝ) ^ (A.filter (fun p => p ∣ N)).card := by
    calc
      (A.filter (fun p => p ∣ N)).prod (fun p => localFactor p N)
          ≤ (A.filter (fun p => p ∣ N)).prod (fun _ => (2 : ℝ)) := by
              apply Finset.prod_le_prod
              · intro p hp
                rw [mem_filter] at hp
                have hpA : p ∈ A := hp.1
                have hpPrime : p.Prime := by
                  rw [mem_filter] at hpA
                  exact hpA.2
                exact le_of_lt (localFactor_pos hpPrime)
              · intro p hp
                rw [mem_filter] at hp
                have hpA : p ∈ A := hp.1
                have hpPrime : p.Prime := by
                  rw [mem_filter] at hpA
                  exact hpA.2
                exact localFactor_le_two hpPrime
      _ = (2 : ℝ) ^ (A.filter (fun p => p ∣ N)).card := by
              rw [Finset.prod_const]
  -- For p not dividing N, each local factor is at most 1.
  have h2 : (A.filter (fun p => ¬ p ∣ N)).prod (fun p => localFactor p N) ≤ 1 := by
    apply Finset.prod_le_one
    · intro p hp
      rw [mem_filter] at hp
      have hpA : p ∈ A := hp.1
      have hpPrime : p.Prime := by
        rw [mem_filter] at hpA
        exact hpA.2
      exact le_of_lt (localFactor_pos hpPrime)
    · intro p hp
      rw [mem_filter] at hp
      have hpA : p ∈ A := hp.1
      have hpPrime : p.Prime := by
        rw [mem_filter] at hpA
        exact hpA.2
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
                have hpPrime : p.Prime := by
                  rw [mem_filter] at hpA
                  exact hpA.2
                exact le_of_lt (localFactor_pos hpPrime)
              have h4 : (0 : ℝ) ≤ (2 : ℝ) ^ (A.filter (fun p => p ∣ N)).card := by positivity
              exact mul_le_mul h1 h2 h3 h4
    _ = (2 : ℝ) ^ (A.filter (fun p => p ∣ N)).card := by ring
    _ ≤ (N : ℝ) := hpow
    _ ≤ 2 * (N : ℝ) := by
        have hN0 : (0 : ℝ) ≤ N := by exact_mod_cast (by omega : 0 ≤ N)
        nlinarith

/-! ## 7.5 Uniform lower bound for truncated products -/

/-- **Uniform truncated-product lower bound**:
`𝔖(N,z) ≥ 1/2` for every `N` and `z ≥ 2`.
Write the product as
`localFactor(2,N)·∏_{2<p≤z} localFactor(p,N)`.
The factor at 2 is at least 1, and for odd primes
`localFactor(p,N) ≥ 1-1/(p-1)²`
(the divisor case is at least 1, and the nondivisor case is equality).
Therefore
`𝔖(N,z) ≥ ∏_{2<p≤z}(1-1/(p-1)²)
 ≥ ∏_{n=2}^{z-1}(1-1/n²) = z/(2(z-1)) ≥ 1/2`.
This supplies the twin-prime-constant-scale input `c_S = 1/2`
for `CorrectedChenMainTermLower`. -/
theorem singularSeriesTruncated_ge_half (N z : ℕ) (hz : 2 ≤ z) :
    (1 : ℝ) / 2 ≤ singularSeriesTruncated N z := by
  unfold singularSeriesTruncated
  set A := (range (z + 1)).filter Nat.Prime with hA_def
  have h2mem : 2 ∈ A := by
    rw [hA_def]
    simp [mem_filter, hz, Nat.prime_two]
  have hfilter_eq : A \ {2} = (range (z + 1)).filter (fun p => Nat.Prime p ∧ 2 < p) := by
    rw [hA_def]
    ext p
    simp only [mem_sdiff, mem_filter, mem_singleton]
    constructor
    · rintro ⟨⟨hp_range, hp⟩, hp_ne⟩
      exact ⟨hp_range, hp, lt_of_le_of_ne hp.two_le (Ne.symm hp_ne)⟩
    · rintro ⟨hp_range, hp, hp2⟩
      exact ⟨⟨hp_range, hp⟩, ne_of_gt hp2⟩
  -- Odd-prime product comparison: ∏(1-1/(p-1)²) ≤ ∏ localFactor(p,N).
  have hfac : ((range (z + 1)).filter (fun p => Nat.Prime p ∧ 2 < p)).prod
        (fun p => 1 - 1 / ((p : ℝ) - 1) ^ 2) ≤
      ((range (z + 1)).filter (fun p => Nat.Prime p ∧ 2 < p)).prod
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
  -- Telescoping comparison: ∏_{n=2}^{z-1}(1-1/n²) = z/(2(z-1)).
  have htel : (z : ℝ) / (2 * ((z : ℝ) - 1)) ≤
      ((range (z + 1)).filter (fun p => Nat.Prime p ∧ 2 < p)).prod
        (fun p => 1 - 1 / ((p : ℝ) - 1) ^ 2) := by
    rw [← int_square_product z hz]
    exact prime_square_product_ge_int z
  -- localFactor(2,N) ≥ 1
  have h2ge1 : (1 : ℝ) ≤ localFactor 2 N := by
    unfold localFactor
    simp
    split_ifs <;> norm_num
  -- Combine the bounds.
  calc
    (1 : ℝ) / 2 ≤ (z : ℝ) / (2 * ((z : ℝ) - 1)) := by
      have hz1 : (0 : ℝ) < (z : ℝ) - 1 := by
        have : (2 : ℝ) ≤ z := by exact_mod_cast hz
        linarith
      have hz2 : (z : ℝ) - 1 ≠ 0 := ne_of_gt hz1
      field_simp [hz2]
      linarith
    _ ≤ ((range (z + 1)).filter (fun p => Nat.Prime p ∧ 2 < p)).prod
        (fun p => 1 - 1 / ((p : ℝ) - 1) ^ 2) := htel
    _ ≤ ((range (z + 1)).filter (fun p => Nat.Prime p ∧ 2 < p)).prod
        (fun p => localFactor p N) := hfac
    _ ≤ localFactor 2 N *
          ((range (z + 1)).filter (fun p => Nat.Prime p ∧ 2 < p)).prod
            (fun p => localFactor p N) := by
      have hprod_pos : (0 : ℝ) ≤
          ((range (z + 1)).filter (fun p => Nat.Prime p ∧ 2 < p)).prod
            (fun p => localFactor p N) := by
        apply Finset.prod_nonneg
        intro p hp
        rw [mem_filter] at hp
        exact le_of_lt (localFactor_pos hp.2.1)
      exact le_mul_of_one_le_left hprod_pos h2ge1
    _ = singularSeriesTruncated N z := by
      unfold singularSeriesTruncated
      rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem h2mem]
      congr 1
      rw [hfilter_eq]

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
