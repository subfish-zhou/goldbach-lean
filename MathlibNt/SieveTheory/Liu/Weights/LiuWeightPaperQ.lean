import MathlibNt.SieveTheory.Liu.Weights.LiuWeight
import MathlibNt.SieveTheory.Arithmetic.MertensTheorem

/-!
# A generic paper-Q-style modulus for Liu's finite weight

This module first develops the generic non-strict integer convention
`Q(N, w) = ∏ {r prime | r ≤ w and r ∤ N}`.  It then identifies the specialization
at `w = ⌊N^(1/4 - ε/2)⌋` with Liu's source definition, whose membership condition
is the real inequality `r ≤ N^(1/4 - ε/2)`.

The exact finite outer divisor sum from Liu's `eqn-r0` is also assembled, with
its cutoff retained. No asymptotic estimate or subsequent maximum bound is
asserted.
-/

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiuWeight

open Finset

/-- Liu's source lower cutoff for the first prime in `eqn-adef`. This is
independent of the modulus-prime cutoff `paperQSourceCutoff`. -/
noncomputable def liuSourceZ10 (N : ℕ) : ℕ :=
  Nat.floor ((N : ℝ) ^ (1 / 10 : ℝ))

/-- Liu's source split point between the two primes in `eqn-adef`. -/
noncomputable def liuSourceY3 (N : ℕ) : ℕ :=
  Nat.floor ((N : ℝ) ^ (1 / 3 : ℝ))

/-- The floor cutoffs recover the three strict/non-strict real source
inequalities in `eqn-adef`. -/
lemma liuWeightPairs_source_basic_range {N : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N)) :
    (N : ℝ) ^ (1 / 10 : ℝ) < p.1 ∧
      (p.1 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) ∧
      (N : ℝ) ^ (1 / 3 : ℝ) < p.2 := by
  have h := mem_liuWeightPairs.mp hp
  have hpow10 : 0 ≤ (N : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hpow3 : 0 ≤ (N : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_nonneg (by positivity) _
  constructor
  · exact (Nat.floor_lt hpow10).mp (by simpa [liuSourceZ10] using h.2.2.1)
  constructor
  · exact (Nat.le_floor_iff hpow3).mp (by simpa [liuSourceY3] using h.2.2.2.1)
  · exact (Nat.floor_lt hpow3).mp (by simpa [liuSourceY3] using h.2.2.2.2.1)

/-- The support condition and the strict `N^(1/10)` lower bound on `p₁` imply
the corrected upper exponent `p₂ ≤ N^(9/20)`. -/
lemma liuWeightPairs_source_p₂_le_rpow_nine_twentieth
    {N : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N)) :
    (p.2 : ℝ) ≤ (N : ℝ) ^ (9 / 20 : ℝ) := by
  have h := mem_liuWeightPairs.mp hp
  have hNpos_nat : 0 < N := lt_of_lt_of_le
    (Nat.mul_pos h.1.pos (pow_pos h.2.1.pos 2)) h.2.2.2.2.2
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hNpos_nat
  have hpow10 : 0 < (N : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hNpos _
  have hp₁lower : (N : ℝ) ^ (1 / 10 : ℝ) < p.1 :=
    (liuWeightPairs_source_basic_range hp).1
  have hsize : (p.1 : ℝ) * (p.2 : ℝ) ^ 2 ≤ N := by
    exact_mod_cast h.2.2.2.2.2
  have hpow9 : (N : ℝ) ^ (9 / 10 : ℝ) =
      (N : ℝ) / (N : ℝ) ^ (1 / 10 : ℝ) := by
    calc
      (N : ℝ) ^ (9 / 10 : ℝ) = (N : ℝ) ^ (1 - 1 / 10 : ℝ) := by norm_num
      _ = (N : ℝ) ^ (1 : ℝ) / (N : ℝ) ^ (1 / 10 : ℝ) :=
        Real.rpow_sub hNpos 1 (1 / 10)
      _ = (N : ℝ) / (N : ℝ) ^ (1 / 10 : ℝ) := by rw [Real.rpow_one]
  have hsquare : (p.2 : ℝ) ^ 2 ≤ (N : ℝ) ^ (9 / 10 : ℝ) := by
    rw [hpow9, le_div_iff₀ hpow10]
    calc
      (p.2 : ℝ) ^ 2 * (N : ℝ) ^ (1 / 10 : ℝ) =
          (N : ℝ) ^ (1 / 10 : ℝ) * (p.2 : ℝ) ^ 2 := by ring
      _ ≤ (p.1 : ℝ) * (p.2 : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hp₁lower.le (sq_nonneg _)
      _ ≤ N := hsize
  have hpow_square : ((N : ℝ) ^ (9 / 20 : ℝ)) ^ 2 =
      (N : ℝ) ^ (9 / 10 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt hNpos)]
    norm_num
  apply (sq_le_sq₀ (by positivity) (Real.rpow_nonneg (le_of_lt hNpos) _)).mp
  rwa [hpow_square]

/-- All source-facing real consequences of an admissible pair at Liu's
`N^(1/10)` and `N^(1/3)` cutoffs. The final exponent is `9/20`, not the
unsupported `4/10` printed in `main.tex` line 312. -/
lemma liuWeightPairs_source_range {N : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N)) :
    (N : ℝ) ^ (1 / 10 : ℝ) < p.1 ∧
      (p.1 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) ∧
      (N : ℝ) ^ (1 / 3 : ℝ) < p.2 ∧
      (p.2 : ℝ) ≤ (N : ℝ) ^ (9 / 20 : ℝ) := by
  exact ⟨(liuWeightPairs_source_basic_range hp).1,
    (liuWeightPairs_source_basic_range hp).2.1,
    (liuWeightPairs_source_basic_range hp).2.2,
    liuWeightPairs_source_p₂_le_rpow_nine_twentieth hp⟩

/-- The finite set of primes at most `w` which do not divide `N`. -/
def paperQStylePrimes (N w : ℕ) : Finset ℕ :=
  (range (w + 1)).filter (fun r => r.Prime ∧ ¬r ∣ N)

/-- A generic paper-`Q`-style modulus with the non-strict integer convention
`r ≤ w`. -/
def paperQStyleModulus (N w : ℕ) : ℕ :=
  (paperQStylePrimes N w).prod id

private theorem primeFactors_prod_eq_self_paperQ {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) : (S.prod id).primeFactors = S := by
  induction S using Finset.induction_on with
  | empty => simp [Nat.primeFactors_one]
  | insert p S hp ih =>
      rw [Finset.prod_insert hp]
      show (p * S.prod id).primeFactors = insert p S
      have hp' := hS p (Finset.mem_insert_self _ _)
      have h0p : p ≠ 0 := hp'.ne_zero
      have h0s : S.prod id ≠ 0 := ne_of_gt <| Finset.prod_pos fun q hq =>
        Nat.Prime.pos (hS q (Finset.mem_insert_of_mem hq))
      rw [Nat.primeFactors_mul h0p h0s, Nat.Prime.primeFactors hp',
        ih fun q hq => hS q (Finset.mem_insert_of_mem hq)]
      rfl

/-- The generic modulus is nonzero because every factor is prime. -/
theorem paperQStyleModulus_ne_zero (N w : ℕ) :
    paperQStyleModulus N w ≠ 0 := by
  unfold paperQStyleModulus paperQStylePrimes
  exact ne_of_gt (Finset.prod_pos (by
    intro r hr
    exact (Finset.mem_filter.mp hr).2.1.pos))

/-- The prime-factor finset of the generic modulus is exactly its defining set. -/
theorem paperQStyleModulus_primeFactors (N w : ℕ) :
    (paperQStyleModulus N w).primeFactors = paperQStylePrimes N w := by
  unfold paperQStyleModulus
  exact primeFactors_prod_eq_self_paperQ (by
    intro p hp
    exact (Finset.mem_filter.mp hp).2.1)

/-- Exact prime-divisor characterization for the non-strict cutoff convention. -/
theorem prime_dvd_paperQStyleModulus {N w r : ℕ} (hr : r.Prime) :
    r ∣ paperQStyleModulus N w ↔ r ≤ w ∧ ¬r ∣ N := by
  constructor
  · intro hrd
    have hmem : r ∈ (paperQStyleModulus N w).primeFactors :=
      (Nat.mem_primeFactors_of_ne_zero (paperQStyleModulus_ne_zero N w)).mpr
        ⟨hr, hrd⟩
    rw [paperQStyleModulus_primeFactors N w] at hmem
    rcases Finset.mem_filter.mp hmem with ⟨hrange, hcond⟩
    exact ⟨by simpa using hrange, hcond.2⟩
  · rintro ⟨hrw, hrN⟩
    have hmem : r ∈ (paperQStyleModulus N w).primeFactors := by
      rw [paperQStyleModulus_primeFactors N w]
      exact Finset.mem_filter.mpr ⟨by simpa using hrw, hr, hrN⟩
    exact (Nat.mem_primeFactors_of_ne_zero
      (paperQStyleModulus_ne_zero N w)).mp hmem |>.2

/-- The generic prime product is squarefree. -/
theorem paperQStyleModulus_squarefree (N w : ℕ) :
    Squarefree (paperQStyleModulus N w) := by
  unfold paperQStyleModulus
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · rintro p hp q hq hpq
    simp only [Finset.mem_coe] at hp hq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (Finset.mem_filter.mp hp).2.1
        (Finset.mem_filter.mp hq).2.1).mpr hpq)
  · intro p hp
    exact (Finset.mem_filter.mp hp).2.1.squarefree

/-- Every prime factor of a divisor of the generic modulus respects both its
cutoff and its exclusion from `N`. -/
theorem prime_le_and_not_dvd_of_dvd_paperQStyleModulus
    {N w d r : ℕ} (hd : d ∣ paperQStyleModulus N w)
    (hr : r.Prime) (hrd : r ∣ d) :
    r ≤ w ∧ ¬r ∣ N :=
  (prime_dvd_paperQStyleModulus hr).mp (hrd.trans hd)

/-- Exact finite arbitrary-model `R₁` majorant for a divisor of the generic
modulus. The weight cutoff `z` remains independent of the modulus cutoff `w`. -/
theorem liuMainNoncoprimeMajorant_liuWeight_mod_eq_abs_main_sum_of_dvd_paperQStyleModulus
   (main : ℝ → ℝ) (N z w y Y X d : ℕ) (hwy : w ≤ y)
   (hd : d ∣ paperQStyleModulus N w) :
   liuMainNoncoprimeMajorant main Y X d (N % d) (liuWeight N z y) =
     ∑ p ∈ (liuWeightPairs N z y).filter
         (fun p => p.1 * p.2 ≤ X ∧ p.1 ∣ d),
       |main ((Y : ℝ) / (p.1 * p.2))| / Nat.totient d := by
 apply liuMainNoncoprimeMajorant_liuWeight_mod_eq_abs_main_sum
   main N z w y Y X d hwy
 · intro r hr hrd
   exact (prime_le_and_not_dvd_of_dvd_paperQStyleModulus hd hr hrd).1
 · intro r hr hrd
   exact (prime_le_and_not_dvd_of_dvd_paperQStyleModulus hd hr hrd).2

/-- Signed finite arbitrary-model `R₁` bound for a divisor of the generic
modulus. -/
theorem abs_liuMainNoncoprimeSum_liuWeight_mod_le_abs_main_sum_of_dvd_paperQStyleModulus
   (main : ℝ → ℝ) (N z w y Y X d : ℕ) (hwy : w ≤ y)
   (hd : d ∣ paperQStyleModulus N w) :
   |liuMainNoncoprimeSum main Y X d (N % d) (liuWeight N z y)| ≤
     ∑ p ∈ (liuWeightPairs N z y).filter
         (fun p => p.1 * p.2 ≤ X ∧ p.1 ∣ d),
       |main ((Y : ℝ) / (p.1 * p.2))| / Nat.totient d := by
 apply abs_liuMainNoncoprimeSum_liuWeight_mod_le_abs_main_sum
   main N z w y Y X d hwy
 · intro r hr hrd
   exact (prime_le_and_not_dvd_of_dvd_paperQStyleModulus hd hr hrd).1
 · intro r hr hrd
   exact (prime_le_and_not_dvd_of_dvd_paperQStyleModulus hd hr hrd).2

/-- **Proxy specialization.** Exact finite `R₁` majorant using ANT's historical
`x / log x` model. This is not a theorem about the paper's true `li`. -/
theorem panDistributionNoncoprimeMajorant_liuWeight_mod_eq_abs_li_sum_of_dvd_paperQStyleModulus
    (N z w y Y X d : ℕ) (hwy : w ≤ y)
    (hd : d ∣ paperQStyleModulus N w) :
    AnalyticNumberTheory.Sieve.panDistributionNoncoprimeMajorant
        Y X d (N % d) (liuWeight N z y) =
      ∑ p ∈ (liuWeightPairs N z y).filter
          (fun p => p.1 * p.2 ≤ X ∧ p.1 ∣ d),
        |AnalyticNumberTheory.Sieve.logarithmicIntegral
          ((Y : ℝ) / (p.1 * p.2))| / Nat.totient d := by
 simpa [← liuMainNoncoprimeMajorant_proxy] using
   liuMainNoncoprimeMajorant_liuWeight_mod_eq_abs_main_sum_of_dvd_paperQStyleModulus
     AnalyticNumberTheory.Sieve.logarithmicIntegral N z w y Y X d hwy hd

/-- **Proxy specialization.** Signed finite `R₁` bound using ANT's historical
`x / log x` model. Its type exhibits `N`, independent `z,w,y`, and the
hypothesis `d ∣ Q(N,w)`. -/
theorem abs_panDistributionNoncoprimeSum_liuWeight_mod_le_abs_li_sum_of_dvd_paperQStyleModulus
    (N z w y Y X d : ℕ) (hwy : w ≤ y)
    (hd : d ∣ paperQStyleModulus N w) :
    |AnalyticNumberTheory.Sieve.panDistributionNoncoprimeSum
        Y X d (N % d) (liuWeight N z y)| ≤
      ∑ p ∈ (liuWeightPairs N z y).filter
          (fun p => p.1 * p.2 ≤ X ∧ p.1 ∣ d),
        |AnalyticNumberTheory.Sieve.logarithmicIntegral
          ((Y : ℝ) / (p.1 * p.2))| / Nat.totient d := by
  simpa [← liuMainNoncoprimeSum_proxy] using
    abs_liuMainNoncoprimeSum_liuWeight_mod_le_abs_main_sum_of_dvd_paperQStyleModulus
      AnalyticNumberTheory.Sieve.logarithmicIntegral N z w y Y X d hwy hd

/-- The exact divisor index in Liu 2022, `main.tex` lines 296--300 (`eqn-r0`),
using the explicit non-strict `paperQStyleModulus` convention. In particular,
`d = 1` is not removed. -/
def paperQStyleR1Divisors (N w D : ℕ) : Finset ℕ :=
  (paperQStyleModulus N w).divisors.filter (fun d => d ≤ D)

/-- The finite outer non-coprime majorant with an arbitrary main-term model,
generic support cutoff `X`, and exact index `d ∣ Q(N,w), d ≤ D`. -/
noncomputable def paperQStyleMainR1Majorant
    (main : ℝ → ℝ) (N z w y D X : ℕ) : ℝ :=
  ∑ d ∈ paperQStyleR1Divisors N w D,
    (3 : ℝ) ^ d.primeFactors.card *
      liuMainNoncoprimeMajorant main N X d (N % d) (liuWeight N z y)

/-- The corresponding finite outer signed sum for an arbitrary main-term model. -/
noncomputable def paperQStyleMainR1SignedSum
    (main : ℝ → ℝ) (N z w y D X : ℕ) : ℝ :=
  ∑ d ∈ paperQStyleR1Divisors N w D,
    (3 : ℝ) ^ d.primeFactors.card *
      liuMainNoncoprimeSum main N X d (N % d) (liuWeight N z y)

/-- Exact outer arbitrary-model rewrite before every analytic estimate in Liu
2022 `main.tex` line 304. -/
theorem paperQStyleMainR1Majorant_eq_abs_main_sum
    (main : ℝ → ℝ) (N z w y D X : ℕ) (hwy : w ≤ y) :
    paperQStyleMainR1Majorant main N z w y D X =
      ∑ d ∈ paperQStyleR1Divisors N w D,
        (3 : ℝ) ^ d.primeFactors.card *
          (∑ p ∈ (liuWeightPairs N z y).filter
              (fun p => p.1 * p.2 ≤ X ∧ p.1 ∣ d),
            |main ((N : ℝ) / (p.1 * p.2))| / Nat.totient d) := by
  classical
  unfold paperQStyleMainR1Majorant
  apply Finset.sum_congr rfl
  intro d hd
  rw [paperQStyleR1Divisors, Finset.mem_filter] at hd
  rw [liuMainNoncoprimeMajorant_liuWeight_mod_eq_abs_main_sum_of_dvd_paperQStyleModulus
    main N z w y N X d hwy (Nat.mem_divisors.mp hd.1).1]

/-- Outer triangle bound for the arbitrary-model signed finite sum. -/
theorem abs_paperQStyleMainR1SignedSum_le_majorant
    (main : ℝ → ℝ) (N z w y D X : ℕ) :
    |paperQStyleMainR1SignedSum main N z w y D X| ≤
      paperQStyleMainR1Majorant main N z w y D X := by
  classical
  unfold paperQStyleMainR1SignedSum paperQStyleMainR1Majorant
  calc
    |∑ d ∈ paperQStyleR1Divisors N w D,
        (3 : ℝ) ^ d.primeFactors.card *
          liuMainNoncoprimeSum main N X d (N % d) (liuWeight N z y)| ≤
        ∑ d ∈ paperQStyleR1Divisors N w D,
          |(3 : ℝ) ^ d.primeFactors.card *
            liuMainNoncoprimeSum main N X d (N % d) (liuWeight N z y)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ d ∈ paperQStyleR1Divisors N w D,
          (3 : ℝ) ^ d.primeFactors.card *
            |liuMainNoncoprimeSum main N X d (N % d) (liuWeight N z y)| := by
      apply Finset.sum_congr rfl
      intro d _
      rw [abs_mul, abs_of_nonneg (by positivity :
        0 ≤ (3 : ℝ) ^ d.primeFactors.card)]
    _ ≤ ∑ d ∈ paperQStyleR1Divisors N w D,
          (3 : ℝ) ^ d.primeFactors.card *
            liuMainNoncoprimeMajorant main N X d (N % d) (liuWeight N z y) := by
      apply Finset.sum_le_sum
      intro d _
      exact mul_le_mul_of_nonneg_left
        (abs_liuMainNoncoprimeSum_le main N X d (N % d) (liuWeight N z y))
        (by positivity)

/-- Source-facing Liu `R₁` majorant with the paper scale fixed as `X = N`.
The function `main` remains abstract, so this definition does not identify the
paper's `li` with ANT's proxy. -/
noncomputable def paperQStyleSourceR1Majorant
    (main : ℝ → ℝ) (N z w y D : ℕ) : ℝ :=
  paperQStyleMainR1Majorant main N z w y D N

/-- Source-facing signed Liu `R₁` sum with `X = N`. -/
noncomputable def paperQStyleSourceR1SignedSum
    (main : ℝ → ℝ) (N z w y D : ℕ) : ℝ :=
  paperQStyleMainR1SignedSum main N z w y D N

/-- Source-facing outer rewrite with `X = N`, matching the `N` in Liu's
`eqn-delta-def` and `eqn-r0`. -/
theorem paperQStyleSourceR1Majorant_eq_abs_main_sum
    (main : ℝ → ℝ) (N z w y D : ℕ) (hwy : w ≤ y) :
    paperQStyleSourceR1Majorant main N z w y D =
      ∑ d ∈ paperQStyleR1Divisors N w D,
        (3 : ℝ) ^ d.primeFactors.card *
          (∑ p ∈ (liuWeightPairs N z y).filter
              (fun p => p.1 * p.2 ≤ N ∧ p.1 ∣ d),
            |main ((N : ℝ) / (p.1 * p.2))| / Nat.totient d) := by
  exact paperQStyleMainR1Majorant_eq_abs_main_sum main N z w y D N hwy

/-- Source-facing outer triangle bound with `X = N`. -/
theorem abs_paperQStyleSourceR1SignedSum_le_majorant
    (main : ℝ → ℝ) (N z w y D : ℕ) :
    |paperQStyleSourceR1SignedSum main N z w y D| ≤
      paperQStyleSourceR1Majorant main N z w y D :=
  abs_paperQStyleMainR1SignedSum_le_majorant main N z w y D N

/-! ## Reduction under a paper-li upper model -/

/-- An explicit upper model for a candidate paper logarithmic integral.
No identification with ANT's historical `x / log x` proxy is made. -/
def PaperLiUpperModel (main : ℝ → ℝ) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x → |main x| ≤ C * x / Real.log x

/-- An admissible Liu pair has positive product. -/
lemma liuWeightPairs_product_pos {N z y : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ liuWeightPairs N z y) : 0 < p.1 * p.2 := by
  have h := mem_liuWeightPairs.mp hp
  exact Nat.mul_pos h.1.pos h.2.1.pos

/-- The root-free cube support bound gives the real cube-root lower bound for
the quotient appearing in the main term. -/
lemma liuWeightPairs_rpow_one_third_le_div {N z y : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ liuWeightPairs N z y) :
    (N : ℝ) ^ (1 / 3 : ℝ) ≤ (N : ℝ) / (p.1 * p.2) := by
  have hcond := mem_liuWeightPairs.mp hp
  have hprod : 0 < p.1 * p.2 := liuWeightPairs_product_pos hp
  have hN : 0 < N := lt_of_lt_of_le
    (Nat.mul_pos hcond.1.pos (pow_pos hcond.2.1.pos 2)) hcond.2.2.2.2.2
  have hcube_nat := liuPairConditions_product_cube_le_sq hcond
  have hcube : ((p.1 : ℝ) * p.2) ^ 3 ≤ (N : ℝ) ^ 2 := by
    exact_mod_cast hcube_nat
  have hroot_cube : ((N : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = (N : ℝ) := by
    convert Real.rpow_inv_natCast_pow (show 0 ≤ (N : ℝ) by positivity)
      (show (3 : ℕ) ≠ 0 by norm_num) using 1
    norm_num
  rw [le_div_iff₀ (by exact_mod_cast hprod : (0 : ℝ) < p.1 * p.2)]
  apply le_of_pow_le_pow_left₀ (show (3 : ℕ) ≠ 0 by norm_num)
    (show (0 : ℝ) ≤ N by positivity)
  calc
    ((N : ℝ) ^ (1 / 3 : ℝ) * ((p.1 : ℝ) * p.2)) ^ 3 =
        ((N : ℝ) ^ (1 / 3 : ℝ)) ^ 3 * ((p.1 : ℝ) * p.2) ^ 3 := by ring
    _ = (N : ℝ) * ((p.1 : ℝ) * p.2) ^ 3 := by rw [hroot_cube]
    _ ≤ (N : ℝ) * (N : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hcube (by positivity)
    _ = (N : ℝ) ^ 3 := by ring

/-- The threshold `N ≥ 8` makes the source main-term argument at least `2`. -/
lemma two_le_div_of_mem_liuWeightPairs {N z y : ℕ} {p : ℕ × ℕ}
    (hN : 8 ≤ N) (hp : p ∈ liuWeightPairs N z y) :
    (2 : ℝ) ≤ (N : ℝ) / (p.1 * p.2) := by
  have hroot8 : (8 : ℝ) ^ (1 / 3 : ℝ) = 2 := by
    rw [show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num]
    convert Real.pow_rpow_inv_natCast (show (0 : ℝ) ≤ 2 by norm_num)
      (show (3 : ℕ) ≠ 0 by norm_num) using 1
    norm_num
  calc
    (2 : ℝ) = (8 : ℝ) ^ (1 / 3 : ℝ) := hroot8.symm
    _ ≤ (N : ℝ) ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hN) (by norm_num)
    _ ≤ (N : ℝ) / (p.1 * p.2) := liuWeightPairs_rpow_one_third_le_div hp

/-- Logarithmic consequence of the cube-root lower bound. -/
lemma one_third_mul_log_le_log_div_of_mem_liuWeightPairs
    {N z y : ℕ} {p : ℕ × ℕ} (hN : 8 ≤ N) (hp : p ∈ liuWeightPairs N z y) :
    (1 / 3 : ℝ) * Real.log N ≤ Real.log ((N : ℝ) / (p.1 * p.2)) := by
  have hN8 : (8 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le (by norm_num) hN8
  calc
    (1 / 3 : ℝ) * Real.log N = Real.log ((N : ℝ) ^ (1 / 3 : ℝ)) :=
      (Real.log_rpow hNpos (1 / 3 : ℝ)).symm
    _ ≤ Real.log ((N : ℝ) / (p.1 * p.2)) :=
      Real.log_le_log (Real.rpow_pos_of_pos hNpos _)
        (liuWeightPairs_rpow_one_third_le_div hp)

/-- Pointwise Liu-pair estimate under an explicit paper-li upper model. -/
lemma PaperLiUpperModel.abs_main_div_le {main : ℝ → ℝ} {C : ℝ}
    {N z y : ℕ} {p : ℕ × ℕ} (hmain : PaperLiUpperModel main C)
    (hN : 8 ≤ N) (hp : p ∈ liuWeightPairs N z y) :
    |main ((N : ℝ) / (p.1 * p.2))| ≤
      3 * C * N / (((p.1 : ℝ) * p.2) * Real.log N) := by
  have hprod : (0 : ℝ) < (p.1 : ℝ) * p.2 := by
    exact_mod_cast liuWeightPairs_product_pos hp
  have hN8 : (8 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le (by norm_num) hN8
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hthirdlog : 0 < (1 / 3 : ℝ) * Real.log N := mul_pos (by norm_num) hlogN
  have hx2 := two_le_div_of_mem_liuWeightPairs hN hp
  calc
    |main ((N : ℝ) / (p.1 * p.2))| ≤
        C * ((N : ℝ) / (p.1 * p.2)) / Real.log ((N : ℝ) / (p.1 * p.2)) :=
      hmain.2 _ hx2
    _ ≤ C * ((N : ℝ) / (p.1 * p.2)) / ((1 / 3 : ℝ) * Real.log N) :=
      div_le_div_of_nonneg_left
        (mul_nonneg hmain.1 (le_of_lt (div_pos hNpos hprod))) hthirdlog
        (one_third_mul_log_le_log_div_of_mem_liuWeightPairs hN hp)
    _ = 3 * C * N / (((p.1 : ℝ) * p.2) * Real.log N) := by
      field_simp [ne_of_gt hprod, ne_of_gt hlogN]

/-- The exact finite double reciprocal sum left after applying the paper-li
upper model. No maximum, Euler product, or Mertens estimate is built into it. -/
noncomputable def paperQStyleSourceR1ReciprocalSum
    (N z w y D : ℕ) : ℝ :=
  ∑ d ∈ paperQStyleR1Divisors N w D,
    (3 : ℝ) ^ d.primeFactors.card *
      (∑ p ∈ (liuWeightPairs N z y).filter
          (fun p => p.1 * p.2 ≤ N ∧ p.1 ∣ d),
        1 / (((p.1 : ℝ) * p.2) * Nat.totient d))

/-- The reciprocal sum over admissible Liu pairs whose first prime divides
`d`. The parameters `z` and `y` retain their independent source roles. -/
noncomputable def paperQStyleR1PairReciprocalSum
    (N z y d : ℕ) : ℝ :=
  ∑ p ∈ (liuWeightPairs N z y).filter
      (fun p => p.1 * p.2 ≤ N ∧ p.1 ∣ d),
    1 / ((p.1 : ℝ) * p.2)

/-- The exact outer `p₁` index in Liu's nested source sum, including primality
and `p₁ ∣ d`. -/
noncomputable def liuSourceR1P₁Range (N d : ℕ) : Finset ℕ :=
  (range (N + 1)).filter fun p₁ =>
    p₁.Prime ∧ liuSourceZ10 N < p₁ ∧ p₁ ≤ liuSourceY3 N ∧ p₁ ∣ d

/-- The exact inner `p₂` index in Liu's nested source sum. The root-free size
condition is exactly the square-root cutoff from `eqn-adef`. -/
noncomputable def liuSourceR1P₂Range (N p₁ : ℕ) : Finset ℕ :=
  (range (N + 1)).filter fun p₂ =>
    p₂.Prime ∧ liuSourceY3 N < p₂ ∧ p₁ * p₂ ^ 2 ≤ N

/-- Liu's pair reciprocal sum written as an exact nested `p₁,p₂` finite sum. -/
noncomputable def liuSourceR1NestedPairReciprocalSum (N d : ℕ) : ℝ :=
  ∑ p₁ ∈ liuSourceR1P₁Range N d,
    ∑ p₂ ∈ liuSourceR1P₂Range N p₁, 1 / ((p₁ : ℝ) * p₂)

/-- Exact reindexing of the retained pair sum into Liu's nested source ranges.
The redundant `p₁*p₂ ≤ N` filter follows from the exact square-root condition. -/
theorem paperQStyleR1PairReciprocalSum_source_eq_nested (N d : ℕ) :
    paperQStyleR1PairReciprocalSum
        N (liuSourceZ10 N) (liuSourceY3 N) d =
      liuSourceR1NestedPairReciprocalSum N d := by
  classical
  unfold paperQStyleR1PairReciprocalSum liuWeightPairs
    liuSourceR1NestedPairReciprocalSum liuSourceR1P₁Range liuSourceR1P₂Range
  simp only [Finset.sum_filter]
  change (∑ a ∈ range (N + 1) ×ˢ range (N + 1), _) = _
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro p₁ hp₁
  by_cases h1 : p₁.Prime <;> by_cases hz : liuSourceZ10 N < p₁ <;>
    by_cases hy1 : p₁ ≤ liuSourceY3 N <;> by_cases hd : p₁ ∣ d <;>
    simp [LiuPairConditions, h1, hz, hy1, hd]
  all_goals
    apply Finset.sum_congr rfl
    intro p₂ hp₂
    by_cases h2 : p₂.Prime <;> by_cases hy2 : liuSourceY3 N < p₂ <;>
      by_cases hs : p₁ * p₂ ^ 2 ≤ N <;> simp [h2, hy2, hs]
    have hprod : p₁ * p₂ ≤ N := liuWeightSupport_le
      ⟨(p₁, p₂), mem_liuWeightPairs.mpr ⟨h1, h2, hz, hy1, hy2, hs⟩, rfl⟩
    simp [hprod]

/-- The corrected rectangular source range: `p₁ > N^(1/10)` and
`N^(1/3) < p₂ ≤ N^(9/20)`, with primality and `p₁ ∣ d` retained. -/
noncomputable def liuSourceR1RectangularPairs (N d : ℕ) : Finset (ℕ × ℕ) :=
  ((range (N + 1)).product (range (N + 1))).filter fun p =>
    p.1.Prime ∧ (N : ℝ) ^ (1 / 10 : ℝ) < p.1 ∧ p.1 ∣ d ∧
      p.2.Prime ∧ (N : ℝ) ^ (1 / 3 : ℝ) < p.2 ∧
        (p.2 : ℝ) ≤ (N : ℝ) ^ (9 / 20 : ℝ)

/-- The reciprocal sum over the corrected rectangular source range. -/
noncomputable def liuSourceR1RectangularPairReciprocalSum (N d : ℕ) : ℝ :=
  ∑ p ∈ liuSourceR1RectangularPairs N d, 1 / ((p.1 : ℝ) * p.2)

/-- Monotonicity from the exact nested source range to the corrected rectangle.
No prime-reciprocal estimate or Mertens theorem is used. -/
theorem paperQStyleR1PairReciprocalSum_source_le_rectangular (N d : ℕ) :
    paperQStyleR1PairReciprocalSum
        N (liuSourceZ10 N) (liuSourceY3 N) d ≤
      liuSourceR1RectangularPairReciprocalSum N d := by
  classical
  unfold paperQStyleR1PairReciprocalSum liuSourceR1RectangularPairReciprocalSum
    liuSourceR1RectangularPairs
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    have hpairs : p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N) :=
      (Finset.mem_filter.mp hp).1
    have hfilter := (Finset.mem_filter.mp hp).2
    have hrange : p ∈ (range (N + 1)).product (range (N + 1)) := by
      rw [liuWeightPairs] at hpairs
      exact (Finset.mem_filter.mp hpairs).1
    have hcond := mem_liuWeightPairs.mp hpairs
    have hsource := liuWeightPairs_source_range hpairs
    exact Finset.mem_filter.mpr
      ⟨hrange, hcond.1, hsource.1, hfilter.2, hcond.2.1,
        hsource.2.2.1, hsource.2.2.2⟩
  · intro p hp hnot
    positivity

/-- The first-coordinate index in the corrected rectangular majorant. -/
noncomputable def liuSourceR1RectangularP₁Range (N d : ℕ) : Finset ℕ :=
  (range (N + 1)).filter fun p =>
    p.Prime ∧ (N : ℝ) ^ (1 / 10 : ℝ) < p ∧ p ∣ d

/-- The corrected `[1/3, 9/20]` prime interval in the second coordinate. -/
noncomputable def liuSourceR1RectangularP₂Range (N : ℕ) : Finset ℕ :=
  (range (N + 1)).filter fun p =>
    p.Prime ∧ (N : ℝ) ^ (1 / 3 : ℝ) < p ∧
      (p : ℝ) ≤ (N : ℝ) ^ (9 / 20 : ℝ)

/-- The reciprocal divisor-prime factor in the corrected rectangle. -/
noncomputable def liuSourceR1P₁DivisorReciprocalSum (N d : ℕ) : ℝ :=
  ∑ p ∈ liuSourceR1RectangularP₁Range N d, 1 / (p : ℝ)

/-- The reciprocal prime sum on the corrected `[1/3, 9/20]` interval. -/
noncomputable def liuSourceR1P₂IntervalReciprocalSum (N : ℕ) : ℝ :=
  ∑ p ∈ liuSourceR1RectangularP₂Range N, 1 / (p : ℝ)

/-- The finite corrected rectangle is exactly the product of its two coordinate
indices. -/
lemma liuSourceR1RectangularPairs_eq_product (N d : ℕ) :
    liuSourceR1RectangularPairs N d =
      (liuSourceR1RectangularP₁Range N d).product
        (liuSourceR1RectangularP₂Range N) := by
  ext p
  simp [liuSourceR1RectangularPairs, liuSourceR1RectangularP₁Range,
    liuSourceR1RectangularP₂Range, and_assoc, and_left_comm, and_comm]

/-- Exact factorization of the corrected rectangular pair reciprocal sum. -/
theorem liuSourceR1RectangularPairReciprocalSum_eq_mul (N d : ℕ) :
    liuSourceR1RectangularPairReciprocalSum N d =
      liuSourceR1P₁DivisorReciprocalSum N d *
        liuSourceR1P₂IntervalReciprocalSum N := by
  classical
  rw [liuSourceR1RectangularPairReciprocalSum,
    liuSourceR1RectangularPairs_eq_product]
  change (∑ p ∈ liuSourceR1RectangularP₁Range N d ×ˢ
      liuSourceR1RectangularP₂Range N, 1 / ((p.1 : ℝ) * p.2)) = _
  rw [Finset.sum_product]
  unfold liuSourceR1P₁DivisorReciprocalSum
    liuSourceR1P₂IntervalReciprocalSum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p₁ hp₁
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p₂ hp₂
  have hp₁pos : (0 : ℝ) < p₁ := by
    exact_mod_cast ((Finset.mem_filter.mp hp₁).2.1.pos)
  have hp₂pos : (0 : ℝ) < p₂ := by
    exact_mod_cast ((Finset.mem_filter.mp hp₂).2.1.pos)
  field_simp [ne_of_gt hp₁pos, ne_of_gt hp₂pos]

/-- The second-coordinate reciprocal interval sum is nonnegative. -/
lemma liuSourceR1P₂IntervalReciprocalSum_nonneg (N : ℕ) :
    0 ≤ liuSourceR1P₂IntervalReciprocalSum N := by
  unfold liuSourceR1P₂IntervalReciprocalSum
  apply Finset.sum_nonneg
  intro p hp
  positivity

/-- A fixed global bound for the corrected `[1/3, 9/20]` reciprocal prime
interval, chosen from the verified Mertens theorem. -/
noncomputable def liuSourceR1P₂ReciprocalBound : ℝ :=
  Classical.choose
    (MertensTheorem.prime_reciprocal_sum_bounded
      (1 / 3 : ℝ) (9 / 20 : ℝ) (by norm_num) (by norm_num))

lemma liuSourceR1P₂ReciprocalBound_spec (N : ℕ) (hN : 2 ≤ N) :
    |liuSourceR1P₂IntervalReciprocalSum N| ≤
      liuSourceR1P₂ReciprocalBound := by
  simpa [liuSourceR1P₂IntervalReciprocalSum,
    liuSourceR1RectangularP₂Range, liuSourceR1P₂ReciprocalBound] using
    (Classical.choose_spec
      (MertensTheorem.prime_reciprocal_sum_bounded
        (1 / 3 : ℝ) (9 / 20 : ℝ) (by norm_num) (by norm_num)) N hN)

lemma liuSourceR1P₂ReciprocalBound_nonneg :
    0 ≤ liuSourceR1P₂ReciprocalBound := by
  exact (liuSourceR1P₂IntervalReciprocalSum_nonneg 2).trans
    ((le_abs_self _).trans
      (liuSourceR1P₂ReciprocalBound_spec 2 (by norm_num)))

lemma liuSourceR1P₂IntervalReciprocalSum_le (N : ℕ) (hN : 2 ≤ N) :
    liuSourceR1P₂IntervalReciprocalSum N ≤
      liuSourceR1P₂ReciprocalBound :=
  (le_abs_self _).trans (liuSourceR1P₂ReciprocalBound_spec N hN)

/-- The pointwise logarithmic gain from `p > N^(1/10)`. The threshold `N ≥ 2`
is sufficient for every positivity and logarithmic division used here. -/
lemma one_div_le_ten_mul_rpow_neg_one_tenth_mul_log_div_log
    (N p : ℕ) (hN : 2 ≤ N)
    (hp : (N : ℝ) ^ (1 / 10 : ℝ) < (p : ℝ)) :
    1 / (p : ℝ) ≤
      10 * (N : ℝ) ^ (-1 / 10 : ℝ) * Real.log p / Real.log N := by
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (by omega : 0 < N)
  have hNnonneg : (0 : ℝ) ≤ N := hNpos.le
  have hpowpos : 0 < (N : ℝ) ^ (1 / 10 : ℝ) :=
    Real.rpow_pos_of_pos hNpos _
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hinv :
      1 / (p : ℝ) ≤ 1 / ((N : ℝ) ^ (1 / 10 : ℝ)) :=
    one_div_le_one_div_of_le hpowpos hp.le
  have hloglower :
      (1 / 10 : ℝ) * Real.log N ≤ Real.log p := by
    rw [← Real.log_rpow hNpos]
    exact Real.log_le_log hpowpos hp.le
  have hratio : (1 : ℝ) ≤ 10 * Real.log p / Real.log N := by
    rw [le_div_iff₀ hlogN]
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hratio
    (Real.rpow_nonneg hNnonneg (-1 / 10 : ℝ))
  calc
    1 / (p : ℝ) ≤ 1 / ((N : ℝ) ^ (1 / 10 : ℝ)) := hinv
    _ = (N : ℝ) ^ (-1 / 10 : ℝ) := by
      rw [show (-1 / 10 : ℝ) = -(1 / 10 : ℝ) by norm_num,
        Real.rpow_neg hNnonneg]
      simp [div_eq_mul_inv]
    _ = (N : ℝ) ^ (-1 / 10 : ℝ) * 1 := by ring
    _ ≤ (N : ℝ) ^ (-1 / 10 : ℝ) *
        (10 * Real.log p / Real.log N) := hmul
    _ = 10 * (N : ℝ) ^ (-1 / 10 : ℝ) *
        Real.log p / Real.log N := by ring

/-- The logarithms of the selected distinct prime divisors sum to at most
`log d`. This uses their product dividing `d`, not a cardinality estimate. -/
lemma liuSourceR1P₁_log_sum_le_log (N d : ℕ) (hd : 0 < d) :
    (∑ p ∈ liuSourceR1RectangularP₁Range N d, Real.log p) ≤
      Real.log d := by
  let s := liuSourceR1RectangularP₁Range N d
  have hsub : s ⊆ d.primeFactors := by
    intro p hp
    have hcond := (Finset.mem_filter.mp hp).2
    exact Nat.mem_primeFactors.mpr
      ⟨hcond.1, hcond.2.2, ne_of_gt hd⟩
  have hproddiv : (∏ p ∈ s, p) ∣ d :=
    dvd_trans
      (Finset.prod_dvd_prod_of_subset s d.primeFactors id hsub)
      (Nat.prod_primeFactors_dvd d)
  have hprodle : (∏ p ∈ s, p) ≤ d :=
    Nat.le_of_dvd hd hproddiv
  have hprodpos : 0 < ∏ p ∈ s, p := by
    apply Finset.prod_pos
    intro p hp
    exact ((Finset.mem_filter.mp hp).2.1.pos)
  change (∑ p ∈ s, Real.log p) ≤ Real.log d
  calc
    (∑ p ∈ s, Real.log p) =
        Real.log (∏ p ∈ s, (p : ℝ)) := by
      rw [Real.log_prod]
      intro p hp
      exact_mod_cast
        (ne_of_gt ((Finset.mem_filter.mp hp).2.1.pos))
    _ = Real.log ((∏ p ∈ s, p : ℕ) : ℝ) := by
      congr 1
      exact (Nat.cast_prod (R := ℝ) id s).symm
    _ ≤ Real.log d :=
      Real.log_le_log (by exact_mod_cast hprodpos)
        (by exact_mod_cast hprodle)

/-- Liu's source divisor cutoff `D₂ = floor(N^(1/2))`. -/
noncomputable def liuSourceD2 (N : ℕ) : ℕ :=
  Nat.floor ((N : ℝ) ^ (1 / 2 : ℝ))

/-- The first-coordinate reciprocal divisor sum has the concrete uniform
`5 N^(-1/10)` bound up to the source cutoff `D₂`. -/
theorem liuSourceR1P₁DivisorReciprocalSum_le
    (N d : ℕ) (hN : 2 ≤ N) (hd : 0 < d)
    (hdD : d ≤ liuSourceD2 N) :
    liuSourceR1P₁DivisorReciprocalSum N d ≤
      5 * (N : ℝ) ^ (-1 / 10 : ℝ) := by
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (by omega : 0 < N)
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hdfloor :
      (d : ℝ) ≤ Nat.floor ((N : ℝ) ^ (1 / 2 : ℝ)) := by
    exact_mod_cast hdD
  have hdroot : (d : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
    hdfloor.trans
      (Nat.floor_le (Real.rpow_nonneg hNpos.le _))
  have hlogd :
      Real.log d ≤ (1 / 2 : ℝ) * Real.log N := by
    calc
      Real.log d ≤ Real.log ((N : ℝ) ^ (1 / 2 : ℝ)) :=
        Real.log_le_log hdpos hdroot
      _ = (1 / 2 : ℝ) * Real.log N :=
        Real.log_rpow hNpos _
  have hcoeff :
      0 ≤ 10 * (N : ℝ) ^ (-1 / 10 : ℝ) / Real.log N :=
    div_nonneg
      (mul_nonneg (by norm_num) (Real.rpow_nonneg hNpos.le _))
      hlogN.le
  unfold liuSourceR1P₁DivisorReciprocalSum
  calc
    (∑ p ∈ liuSourceR1RectangularP₁Range N d, 1 / (p : ℝ)) ≤
        ∑ p ∈ liuSourceR1RectangularP₁Range N d,
          10 * (N : ℝ) ^ (-1 / 10 : ℝ) *
            Real.log p / Real.log N := by
      apply Finset.sum_le_sum
      intro p hp
      exact
        one_div_le_ten_mul_rpow_neg_one_tenth_mul_log_div_log
          N p hN (Finset.mem_filter.mp hp).2.2.1
    _ = (10 * (N : ℝ) ^ (-1 / 10 : ℝ) / Real.log N) *
        (∑ p ∈ liuSourceR1RectangularP₁Range N d,
          Real.log p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ (10 * (N : ℝ) ^ (-1 / 10 : ℝ) / Real.log N) *
        Real.log d :=
      mul_le_mul_of_nonneg_left
        (liuSourceR1P₁_log_sum_le_log N d hd) hcoeff
    _ ≤ (10 * (N : ℝ) ^ (-1 / 10 : ℝ) / Real.log N) *
        ((1 / 2 : ℝ) * Real.log N) :=
      mul_le_mul_of_nonneg_left hlogd hcoeff
    _ = 5 * (N : ℝ) ^ (-1 / 10 : ℝ) := by
      field_simp [ne_of_gt hlogN]
      ring

/-- The truncated divisor-weight sum from the exact `R₁` index, including
`d = 1` whenever `1 ≤ D`. -/
noncomputable def paperQStyleR1DivisorWeightSum
    (N w D : ℕ) : ℝ :=
  ∑ d ∈ paperQStyleR1Divisors N w D,
    (3 : ℝ) ^ d.primeFactors.card / Nat.totient d

/-- The full divisor-weight sum over all divisors of the generic paper-Q-style
modulus. -/
noncomputable def paperQStyleFullDivisorWeightSum
    (N w : ℕ) : ℝ :=
  ∑ d ∈ (paperQStyleModulus N w).divisors,
    (3 : ℝ) ^ d.primeFactors.card / Nat.totient d

/-- Exact factorization of the retained reciprocal sum into the divisor weight
and the per-modulus pair reciprocal sum. -/
theorem paperQStyleSourceR1ReciprocalSum_eq_weighted_pair_sums
    (N z w y D : ℕ) :
    paperQStyleSourceR1ReciprocalSum N z w y D =
      ∑ d ∈ paperQStyleR1Divisors N w D,
        ((3 : ℝ) ^ d.primeFactors.card / Nat.totient d) *
          paperQStyleR1PairReciprocalSum N z y d := by
  classical
  unfold paperQStyleSourceR1ReciprocalSum paperQStyleR1PairReciprocalSum
  apply Finset.sum_congr rfl
  intro d hd
  rw [paperQStyleR1Divisors, Finset.mem_filter] at hd
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos
    (Nat.mem_divisors.mp hd.1).1
    (Nat.pos_of_ne_zero (paperQStyleModulus_ne_zero N w))
  have htot : (0 : ℝ) < Nat.totient d := by
    exact_mod_cast Nat.totient_pos.mpr hdpos
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpairs : p ∈ liuWeightPairs N z y := (Finset.mem_filter.mp hp).1
  have hprod : (0 : ℝ) < (p.1 : ℝ) * p.2 := by
    exact_mod_cast liuWeightPairs_product_pos hpairs
  field_simp [ne_of_gt hprod, ne_of_gt htot]

/-- A transparent uniform upper bound for every per-modulus pair reciprocal
sum in the exact truncated divisor index. -/
def PaperQStyleR1PairUniformBound
    (N z w y D : ℕ) (M : ℝ) : Prop :=
  0 ≤ M ∧ ∀ d ∈ paperQStyleR1Divisors N w D,
    paperQStyleR1PairReciprocalSum N z y d ≤ M

/-- Every per-modulus pair reciprocal sum is nonnegative. -/
lemma paperQStyleR1PairReciprocalSum_nonneg
    (N z y d : ℕ) :
    0 ≤ paperQStyleR1PairReciprocalSum N z y d := by
  classical
  unfold paperQStyleR1PairReciprocalSum
  apply Finset.sum_nonneg
  intro p hp
  positivity

/-- At the frozen source cutoffs and `D₂`, every per-modulus pair sum is bounded
by `5 C₂ N^(-1/10)`. -/
theorem paperQStyleR1PairUniformBound_source
    (N w : ℕ) (hN : 2 ≤ N) :
    PaperQStyleR1PairUniformBound
      N (liuSourceZ10 N) w (liuSourceY3 N) (liuSourceD2 N)
        (5 * liuSourceR1P₂ReciprocalBound *
          (N : ℝ) ^ (-1 / 10 : ℝ)) := by
  constructor
  · exact mul_nonneg
      (mul_nonneg (by norm_num)
        liuSourceR1P₂ReciprocalBound_nonneg)
      (Real.rpow_nonneg (by positivity) _)
  intro d hd
  rw [paperQStyleR1Divisors, Finset.mem_filter] at hd
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos
    (Nat.mem_divisors.mp hd.1).1
    (Nat.pos_of_ne_zero (paperQStyleModulus_ne_zero N w))
  have hp₁bound :=
    liuSourceR1P₁DivisorReciprocalSum_le N d hN hdpos hd.2
  have hp₂bound :=
    liuSourceR1P₂IntervalReciprocalSum_le N hN
  have hfactor :
      liuSourceR1RectangularPairReciprocalSum N d ≤
        (5 * (N : ℝ) ^ (-1 / 10 : ℝ)) *
          liuSourceR1P₂ReciprocalBound := by
    rw [liuSourceR1RectangularPairReciprocalSum_eq_mul]
    exact mul_le_mul hp₁bound hp₂bound
      (liuSourceR1P₂IntervalReciprocalSum_nonneg N)
      (mul_nonneg (by norm_num)
        (Real.rpow_nonneg (by positivity) _))
  calc
    paperQStyleR1PairReciprocalSum
        N (liuSourceZ10 N) (liuSourceY3 N) d ≤
      liuSourceR1RectangularPairReciprocalSum N d :=
        paperQStyleR1PairReciprocalSum_source_le_rectangular N d
    _ ≤ (5 * (N : ℝ) ^ (-1 / 10 : ℝ)) *
        liuSourceR1P₂ReciprocalBound := hfactor
    _ = 5 * liuSourceR1P₂ReciprocalBound *
        (N : ℝ) ^ (-1 / 10 : ℝ) := by ring

/-- A uniform per-modulus pair bound factors out of the exact reciprocal sum. -/
theorem paperQStyleSourceR1ReciprocalSum_le_divisorWeight_mul
    (N z w y D : ℕ) (M : ℝ)
    (hM : PaperQStyleR1PairUniformBound N z w y D M) :
    paperQStyleSourceR1ReciprocalSum N z w y D ≤
      paperQStyleR1DivisorWeightSum N w D * M := by
  rw [paperQStyleSourceR1ReciprocalSum_eq_weighted_pair_sums,
    paperQStyleR1DivisorWeightSum]
  calc
    (∑ d ∈ paperQStyleR1Divisors N w D,
        ((3 : ℝ) ^ d.primeFactors.card / Nat.totient d) *
          paperQStyleR1PairReciprocalSum N z y d) ≤
        ∑ d ∈ paperQStyleR1Divisors N w D,
          ((3 : ℝ) ^ d.primeFactors.card / Nat.totient d) * M := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left (hM.2 d hd) (by positivity)
    _ = (∑ d ∈ paperQStyleR1Divisors N w D,
          (3 : ℝ) ^ d.primeFactors.card / Nat.totient d) * M := by
      rw [Finset.sum_mul]

/-- Source-facing Liu `R₁` reduction under an explicit paper-li upper model.
The right side retains the exact finite divisor and pair sums. -/
lemma PaperLiUpperModel.paperQStyleSourceR1Majorant_le
    {main : ℝ → ℝ} {C : ℝ} (N z w y D : ℕ)
    (hmain : PaperLiUpperModel main C) (hN : 8 ≤ N) (hwy : w ≤ y) :
    paperQStyleSourceR1Majorant main N z w y D ≤
      (3 * C * N / Real.log N) *
        paperQStyleSourceR1ReciprocalSum N z w y D := by
  classical
  rw [paperQStyleSourceR1Majorant_eq_abs_main_sum main N z w y D hwy]
  calc
    (∑ d ∈ paperQStyleR1Divisors N w D,
        (3 : ℝ) ^ d.primeFactors.card *
          (∑ p ∈ (liuWeightPairs N z y).filter
              (fun p => p.1 * p.2 ≤ N ∧ p.1 ∣ d),
            |main ((N : ℝ) / (p.1 * p.2))| / Nat.totient d)) ≤
      ∑ d ∈ paperQStyleR1Divisors N w D,
        (3 : ℝ) ^ d.primeFactors.card *
          (∑ p ∈ (liuWeightPairs N z y).filter
              (fun p => p.1 * p.2 ≤ N ∧ p.1 ∣ d),
            (3 * C * N / Real.log N) *
              (1 / (((p.1 : ℝ) * p.2) * Nat.totient d))) := by
      apply Finset.sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro p hp
      have hpairs : p ∈ liuWeightPairs N z y := (Finset.mem_filter.mp hp).1
      have hprod : (0 : ℝ) < (p.1 : ℝ) * p.2 := by
        exact_mod_cast liuWeightPairs_product_pos hpairs
      rw [paperQStyleR1Divisors, Finset.mem_filter] at hd
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos
        (Nat.mem_divisors.mp hd.1).1
        (Nat.pos_of_ne_zero (paperQStyleModulus_ne_zero N w))
      have htot : (0 : ℝ) < Nat.totient d := by
        exact_mod_cast Nat.totient_pos.mpr hdpos
      have hN8 : (8 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
      calc
        |main ((N : ℝ) / (p.1 * p.2))| / Nat.totient d ≤
            (3 * C * N / (((p.1 : ℝ) * p.2) * Real.log N)) / Nat.totient d :=
          div_le_div_of_nonneg_right (hmain.abs_main_div_le hN hpairs)
            (le_of_lt htot)
        _ = (3 * C * N / Real.log N) *
            (1 / (((p.1 : ℝ) * p.2) * Nat.totient d)) := by
          field_simp [ne_of_gt hprod, ne_of_gt htot, ne_of_gt hlogN]
    _ = (3 * C * N / Real.log N) *
        paperQStyleSourceR1ReciprocalSum N z w y D := by
      rw [paperQStyleSourceR1ReciprocalSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [← Finset.mul_sum]
      ring

/-- The paper-li upper-model reduction combined with a transparent uniform
bound for the exact per-modulus pair sums. -/
theorem PaperLiUpperModel.paperQStyleSourceR1Majorant_le_divisorWeight_mul
    {main : ℝ → ℝ} {C M : ℝ} (N z w y D : ℕ)
    (hmain : PaperLiUpperModel main C) (hN : 8 ≤ N) (hwy : w ≤ y)
    (hM : PaperQStyleR1PairUniformBound N z w y D M) :
    paperQStyleSourceR1Majorant main N z w y D ≤
      (3 * C * N / Real.log N) *
       (paperQStyleR1DivisorWeightSum N w D * M) := by
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 8) hN)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 8) hN)
    )
  exact (hmain.paperQStyleSourceR1Majorant_le N z w y D hN hwy).trans
    (mul_le_mul_of_nonneg_left
      (paperQStyleSourceR1ReciprocalSum_le_divisorWeight_mul
       N z w y D M hM)
      (div_nonneg
       (mul_nonneg (mul_nonneg (by positivity) hmain.1) (le_of_lt hNpos))
       (le_of_lt hlogN)))

/-- The paper-li majorant specialized to the verified source pair bound at
`z = floor(N^(1/10))`, `y = floor(N^(1/3))`, and
`D₂ = floor(N^(1/2))`. -/
theorem PaperLiUpperModel.paperQStyleSourceR1Majorant_le_source_pair_bound
    {main : ℝ → ℝ} {C : ℝ} (N w : ℕ)
    (hmain : PaperLiUpperModel main C) (hN : 8 ≤ N)
    (hwy : w ≤ liuSourceY3 N) :
    paperQStyleSourceR1Majorant main N
        (liuSourceZ10 N) w (liuSourceY3 N) (liuSourceD2 N) ≤
      (3 * C * N / Real.log N) *
        (paperQStyleR1DivisorWeightSum N w (liuSourceD2 N) *
          (5 * liuSourceR1P₂ReciprocalBound *
            (N : ℝ) ^ (-1 / 10 : ℝ))) := by
  exact hmain.paperQStyleSourceR1Majorant_le_divisorWeight_mul
    N (liuSourceZ10 N) w (liuSourceY3 N) (liuSourceD2 N)
    hN hwy (paperQStyleR1PairUniformBound_source N w (by omega))

/-- Dropping the cutoff `d ≤ D` only enlarges the nonnegative divisor-weight
sum. -/
theorem paperQStyleR1DivisorWeightSum_le_full
    (N w D : ℕ) :
    paperQStyleR1DivisorWeightSum N w D ≤
      paperQStyleFullDivisorWeightSum N w := by
  classical
  unfold paperQStyleR1DivisorWeightSum paperQStyleFullDivisorWeightSum
    paperQStyleR1Divisors
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    exact (Finset.mem_filter.mp hd).1
  · intro d _ _
    positivity

private noncomputable def paperQStyleDivisorWeight :
    ArithmeticFunction ℝ where
  toFun d := (3 : ℝ) ^ d.primeFactors.card / Nat.totient d
  map_zero' := by simp [Nat.totient_zero]

private lemma primeFactors_card_eq_cardDistinctFactors_paperQ (d : ℕ) :
    d.primeFactors.card = ArithmeticFunction.cardDistinctFactors d := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
    Nat.toFinset_factors]

private lemma paperQStyleDivisorWeight_mul
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m.Coprime n) :
    paperQStyleDivisorWeight (m * n) =
      paperQStyleDivisorWeight m * paperQStyleDivisorWeight n := by
  unfold paperQStyleDivisorWeight
  change (3 : ℝ) ^ (m * n).primeFactors.card / ↑(m * n).totient =
    ((3 : ℝ) ^ m.primeFactors.card / ↑m.totient) *
      ((3 : ℝ) ^ n.primeFactors.card / ↑n.totient)
  have hcard :
      (m * n).primeFactors.card =
       m.primeFactors.card + n.primeFactors.card := by
    rw [primeFactors_card_eq_cardDistinctFactors_paperQ,
      primeFactors_card_eq_cardDistinctFactors_paperQ,
      primeFactors_card_eq_cardDistinctFactors_paperQ]
    exact ArithmeticFunction.cardDistinctFactors_mul hmn
  have htot : Nat.totient (m * n) = Nat.totient m * Nat.totient n :=
    Nat.totient_mul hmn
  have htotm : Nat.totient m ≠ 0 :=
    ne_of_gt (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm))
  have htotn : Nat.totient n ≠ 0 :=
    ne_of_gt (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn))
  rw [hcard, htot, pow_add]
  field_simp [htotm, htotn]
  rw [Nat.cast_mul]

private lemma paperQStyleDivisorWeight_isMultiplicative :
    paperQStyleDivisorWeight.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · unfold paperQStyleDivisorWeight
    simp
  · intro m n hm hn hmn
    exact paperQStyleDivisorWeight_mul hm hn hmn

/-- Exact squarefree Euler product for the full divisor-weight sum.

Liu 2022 `main.tex` line 194 prints `p - 2` in this local factor. That is a
source typo: because `Nat.totient p = p - 1` for prime `p`, the exact factor is
`1 + 3 / (p - 1)`. No Mertens or asymptotic estimate is used here. -/
theorem paperQStyleFullDivisorWeightSum_eq_eulerProduct
    (N w : ℕ) :
    paperQStyleFullDivisorWeightSum N w =
      ∏ p ∈ paperQStylePrimes N w,
       (1 + 3 / ((p : ℝ) - 1)) := by
  classical
  have heuler :=
    ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_add_of_squarefree
      paperQStyleDivisorWeight_isMultiplicative
      (paperQStyleModulus_squarefree N w)
  rw [paperQStyleModulus_primeFactors N w] at heuler
  unfold paperQStyleFullDivisorWeightSum
  change (∑ d ∈ (paperQStyleModulus N w).divisors,
      paperQStyleDivisorWeight d) =
    ∏ p ∈ paperQStylePrimes N w, (1 + 3 / ((p : ℝ) - 1))
  rw [← heuler]
  apply Finset.prod_congr rfl
  intro p hp
  have hpprime : p.Prime := (Finset.mem_filter.mp hp).2.1
  congr 1
  change (3 : ℝ) ^ p.primeFactors.card / Nat.totient p =
    3 / ((p : ℝ) - 1)
  rw [hpprime.primeFactors, Nat.totient_prime hpprime]
  simp [Nat.cast_sub hpprime.one_le]

/-- The corrected local divisor factor is bounded by the reciprocal cube of the
corresponding Mertens factor. This includes `p = 2`; primality supplies all
denominator positivity used in the proof. -/
theorem paperQStyleEulerFactor_le_mertensFactor_inv_cube
    {p : ℕ} (hp : p.Prime) :
    (1 : ℝ) + 3 / ((p : ℝ) - 1) ≤
      (1 - 1 / (p : ℝ))⁻¹ ^ 3 := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hpR
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := sub_pos.mpr hpR
  rw [show (1 - 1 / (p : ℝ))⁻¹ =
      (p : ℝ) / ((p : ℝ) - 1) by
    field_simp [ne_of_gt hp0, ne_of_gt hpm1]]
  rw [div_pow, le_div_iff₀ (pow_pos hpm1 3)]
  field_simp [ne_of_gt hpm1]
  nlinarith [hpR]

private lemma paperQStyleMertensFactor_pos
    {p : ℕ} (hp : p.Prime) :
    0 < (1 : ℝ) - 1 / (p : ℝ) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [sub_pos, div_lt_iff₀ (by positivity : (0 : ℝ) < (p : ℝ))]
  simpa using hpR

/-- For `w ≤ N`, enlarging from the primes defining the paper-Q-style modulus
to every prime at most `N` bounds the full divisor sum by the reciprocal cube
of the Mertens product. -/
theorem paperQStyleFullDivisorWeightSum_le_primeProduct_inv_cube
    (N w : ℕ) (hw : w ≤ N) :
    paperQStyleFullDivisorWeightSum N w ≤
      (MertensTheorem.primeProduct N)⁻¹ ^ 3 := by
  classical
  rw [paperQStyleFullDivisorWeightSum_eq_eulerProduct]
  let allPrimes := (range (N + 1)).filter Nat.Prime
  calc
    (∏ p ∈ paperQStylePrimes N w,
        (1 + 3 / ((p : ℝ) - 1))) ≤
      ∏ p ∈ paperQStylePrimes N w,
        (1 - 1 / (p : ℝ))⁻¹ ^ 3 := by
          apply Finset.prod_le_prod
          · intro p hp
            have hp' := (Finset.mem_filter.mp hp).2.1
            have hpR : (1 : ℝ) < p := by exact_mod_cast hp'.one_lt
            have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := sub_pos.mpr hpR
            positivity
          · intro p hp
            exact paperQStyleEulerFactor_le_mertensFactor_inv_cube
              (Finset.mem_filter.mp hp).2.1
    _ ≤ ∏ p ∈ allPrimes, (1 - 1 / (p : ℝ))⁻¹ ^ 3 := by
      apply Finset.prod_le_prod_of_subset_of_one_le
      · intro p hp
        rw [paperQStylePrimes, Finset.mem_filter] at hp
        have hpw : p < w + 1 := Finset.mem_range.mp hp.1
        have hpall : p ∈ Finset.range (N + 1) :=
          Finset.mem_range.mpr (by omega)
        exact Finset.mem_filter.mpr ⟨hpall, hp.2.1⟩
      · intro p hp
        have hp' := (Finset.mem_filter.mp hp).2.1
        exact le_of_lt
          (pow_pos (inv_pos.mpr (paperQStyleMertensFactor_pos hp')) 3)
      · intro p hp _
        simp only [allPrimes, Finset.mem_filter] at hp
        have hbase := paperQStyleMertensFactor_pos hp.2
        have hbase_le : (1 : ℝ) - 1 / (p : ℝ) ≤ 1 :=
          sub_le_self _ (by positivity)
        exact one_le_pow₀ ((one_le_inv₀ hbase).2 hbase_le)
    _ = (MertensTheorem.primeProduct N)⁻¹ ^ 3 := by
      dsimp [allPrimes]
      unfold MertensTheorem.primeProduct
      rw [Finset.prod_pow, Finset.prod_inv_distrib]

/-- A fixed positive choice of lower-bound constant for the Mertens product. -/
noncomputable def paperQStyleMertensLowerConstant : ℝ :=
  Classical.choose MertensTheorem.primeProduct_lower_bound_exists

theorem paperQStyleMertensLowerConstant_pos :
    0 < paperQStyleMertensLowerConstant :=
  (Classical.choose_spec
    MertensTheorem.primeProduct_lower_bound_exists).1

theorem paperQStyleMertensLowerConstant_spec
    (N : ℕ) (hN : 3 ≤ N) :
    paperQStyleMertensLowerConstant / Real.log N ≤
      MertensTheorem.primeProduct N :=
  (Classical.choose_spec
    MertensTheorem.primeProduct_lower_bound_exists).2 N hN

/-- The fixed divisor-weight constant obtained by cubing the reciprocal of the
chosen Mertens lower-bound constant. -/
noncomputable def paperQStyleDivisorWeightLogConstant : ℝ :=
  paperQStyleMertensLowerConstant⁻¹ ^ 3

theorem paperQStyleDivisorWeightLogConstant_pos :
    0 < paperQStyleDivisorWeightLogConstant := by
  exact pow_pos
    (inv_pos.mpr paperQStyleMertensLowerConstant_pos) 3

theorem paperQStyleDivisorWeightLogConstant_nonneg :
    0 ≤ paperQStyleDivisorWeightLogConstant :=
  le_of_lt paperQStyleDivisorWeightLogConstant_pos

private lemma mertensPrimeProduct_pos (N : ℕ) :
    0 < MertensTheorem.primeProduct N := by
  unfold MertensTheorem.primeProduct
  apply Finset.prod_pos
  intro p hp
  exact paperQStyleMertensFactor_pos (Finset.mem_filter.mp hp).2

/-- The corrected full divisor weight is `O((log N)^3)`, uniformly for
`w ≤ N`, with an explicit choice-defined constant and threshold `N ≥ 3`. -/
theorem paperQStyleFullDivisorWeightSum_le_log_cube
    (N w : ℕ) (hN : 3 ≤ N) (hw : w ≤ N) :
    paperQStyleFullDivisorWeightSum N w ≤
      paperQStyleDivisorWeightLogConstant * Real.log N ^ 3 := by
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hP : 0 < MertensTheorem.primeProduct N :=
    mertensPrimeProduct_pos N
  have hc : 0 < paperQStyleMertensLowerConstant :=
    paperQStyleMertensLowerConstant_pos
  have hlower :=
    paperQStyleMertensLowerConstant_spec N hN
  have hinv : (MertensTheorem.primeProduct N)⁻¹ ≤
      (paperQStyleMertensLowerConstant / Real.log N)⁻¹ :=
    (inv_le_inv₀ hP (div_pos hc hlog)).2 hlower
  calc
    paperQStyleFullDivisorWeightSum N w ≤
        (MertensTheorem.primeProduct N)⁻¹ ^ 3 :=
      paperQStyleFullDivisorWeightSum_le_primeProduct_inv_cube N w hw
    _ ≤ (paperQStyleMertensLowerConstant / Real.log N)⁻¹ ^ 3 :=
      pow_le_pow_left₀ (le_of_lt (inv_pos.mpr hP)) hinv 3
    _ = paperQStyleDivisorWeightLogConstant * Real.log N ^ 3 := by
      unfold paperQStyleDivisorWeightLogConstant
      field_simp [ne_of_gt hc, ne_of_gt hlog]

/-- **Conditional source endpoint.** Assuming the supplied `main` satisfies the
explicit `PaperLiUpperModel` true-li boundary, the verified R1 layers give the
source majorant bound with the exact harmless constant `15 = 3 * 5`.
This theorem does not instantiate `main` or identify it with ANT's proxy. -/
theorem PaperLiUpperModel.paperQStyleSourceR1Majorant_le_log_square
    {main : ℝ → ℝ} {C : ℝ} (N w : ℕ)
    (hmain : PaperLiUpperModel main C) (hN : 8 ≤ N)
    (hwy : w ≤ liuSourceY3 N) (hwN : w ≤ N) :
    paperQStyleSourceR1Majorant main N
        (liuSourceZ10 N) w (liuSourceY3 N) (liuSourceD2 N) ≤
      15 * C * liuSourceR1P₂ReciprocalBound *
        paperQStyleDivisorWeightLogConstant *
        (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 2 := by
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (by omega : 0 < N)
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hdiv :
      paperQStyleR1DivisorWeightSum N w (liuSourceD2 N) ≤
        paperQStyleDivisorWeightLogConstant * Real.log N ^ 3 :=
    (paperQStyleR1DivisorWeightSum_le_full
      N w (liuSourceD2 N)).trans
      (paperQStyleFullDivisorWeightSum_le_log_cube
        N w (by omega) hwN)
  have hpair : 0 ≤ 5 * liuSourceR1P₂ReciprocalBound *
      (N : ℝ) ^ (-1 / 10 : ℝ) :=
    mul_nonneg
      (mul_nonneg (by norm_num)
        liuSourceR1P₂ReciprocalBound_nonneg)
      (Real.rpow_nonneg (le_of_lt hNpos) _)
  have houter : 0 ≤ 3 * C * N / Real.log N :=
    div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hmain.1)
        (le_of_lt hNpos))
      (le_of_lt hlog)
  have hNpow : (N : ℝ) * (N : ℝ) ^ (-1 / 10 : ℝ) =
      (N : ℝ) ^ (9 / 10 : ℝ) := by
    have hadd :=
      Real.rpow_add hNpos (1 : ℝ) (-1 / 10 : ℝ)
    rw [Real.rpow_one] at hadd
    calc
      (N : ℝ) * (N : ℝ) ^ (-1 / 10 : ℝ) =
          (N : ℝ) ^ (1 + (-1 / 10 : ℝ)) := hadd.symm
      _ = (N : ℝ) ^ (9 / 10 : ℝ) := by norm_num
  have hlogpow : (Real.log (N : ℝ))⁻¹ * Real.log N ^ 3 =
      Real.log N ^ 2 := by
    field_simp [ne_of_gt hlog]
  calc
    paperQStyleSourceR1Majorant main N
        (liuSourceZ10 N) w (liuSourceY3 N) (liuSourceD2 N) ≤
      (3 * C * N / Real.log N) *
        (paperQStyleR1DivisorWeightSum N w (liuSourceD2 N) *
          (5 * liuSourceR1P₂ReciprocalBound *
            (N : ℝ) ^ (-1 / 10 : ℝ))) :=
      hmain.paperQStyleSourceR1Majorant_le_source_pair_bound
        N w hN hwy
    _ ≤ (3 * C * N / Real.log N) *
        ((paperQStyleDivisorWeightLogConstant * Real.log N ^ 3) *
          (5 * liuSourceR1P₂ReciprocalBound *
            (N : ℝ) ^ (-1 / 10 : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hdiv hpair) houter
    _ = 15 * C * liuSourceR1P₂ReciprocalBound *
        paperQStyleDivisorWeightLogConstant *
        (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 2 := by
      rw [div_eq_mul_inv]
      calc
        (3 * C * ↑N * (Real.log ↑N)⁻¹) *
            (paperQStyleDivisorWeightLogConstant * Real.log ↑N ^ 3 *
              (5 * liuSourceR1P₂ReciprocalBound *
                ↑N ^ (-1 / 10 : ℝ))) =
          15 * C * liuSourceR1P₂ReciprocalBound *
            paperQStyleDivisorWeightLogConstant *
            (↑N * ↑N ^ (-1 / 10 : ℝ)) *
              ((Real.log ↑N)⁻¹ * Real.log ↑N ^ 3) := by ring
        _ = _ := by rw [hNpow, hlogpow]

/-- The finite outer non-coprime majorant from Liu 2022, `main.tex` lines
296--300, with `Y = N`, canonical residue `N % d`, and a generic support cutoff
`X`. **This legacy declaration is the ANT `x / log x` proxy specialization**, not
the paper's true-`li` layer. -/
noncomputable def paperQStyleOuterR1Majorant
    (N z w y D X : ℕ) : ℝ :=
  ∑ d ∈ paperQStyleR1Divisors N w D,
    (3 : ℝ) ^ d.primeFactors.card *
      AnalyticNumberTheory.Sieve.panDistributionNoncoprimeMajorant
        N X d (N % d) (liuWeight N z y)

/-- The corresponding finite outer signed non-coprime sum. -/
noncomputable def paperQStyleOuterR1SignedSum
    (N z w y D X : ℕ) : ℝ :=
  ∑ d ∈ paperQStyleR1Divisors N w D,
    (3 : ℝ) ^ d.primeFactors.card *
      AnalyticNumberTheory.Sieve.panDistributionNoncoprimeSum
        N X d (N % d) (liuWeight N z y)

/-- The legacy outer majorant is exactly the ANT proxy specialization. -/
theorem paperQStyleMainR1Majorant_proxy
    (N z w y D X : ℕ) :
    paperQStyleMainR1Majorant
        AnalyticNumberTheory.Sieve.logarithmicIntegral N z w y D X =
      paperQStyleOuterR1Majorant N z w y D X := by
  rfl

/-- The legacy outer signed sum is exactly the ANT proxy specialization. -/
theorem paperQStyleMainR1SignedSum_proxy
    (N z w y D X : ℕ) :
    paperQStyleMainR1SignedSum
        AnalyticNumberTheory.Sieve.logarithmicIntegral N z w y D X =
      paperQStyleOuterR1SignedSum N z w y D X := by
  rfl

/-- **Proxy specialization.** Exact outer rewrite with ANT's `x / log x`
compatibility model. It is not an identification with the paper's true `li`. -/
theorem paperQStyleOuterR1Majorant_eq_abs_li_sum
    (N z w y D X : ℕ) (hwy : w ≤ y) :
    paperQStyleOuterR1Majorant N z w y D X =
      ∑ d ∈ paperQStyleR1Divisors N w D,
        (3 : ℝ) ^ d.primeFactors.card *
          (∑ p ∈ (liuWeightPairs N z y).filter
              (fun p => p.1 * p.2 ≤ X ∧ p.1 ∣ d),
            |AnalyticNumberTheory.Sieve.logarithmicIntegral
              ((N : ℝ) / (p.1 * p.2))| / Nat.totient d) := by
  simpa [paperQStyleMainR1Majorant_proxy] using
    paperQStyleMainR1Majorant_eq_abs_main_sum
      AnalyticNumberTheory.Sieve.logarithmicIntegral N z w y D X hwy

/-- **Proxy specialization.** Outer triangle bound for the legacy signed finite
sum. This does not assert a true-`li` model or any estimate from lines 304--319. -/
theorem abs_paperQStyleOuterR1SignedSum_le_majorant
    (N z w y D X : ℕ) (_hwy : w ≤ y) :
    |paperQStyleOuterR1SignedSum N z w y D X| ≤
      paperQStyleOuterR1Majorant N z w y D X := by
  simpa [paperQStyleMainR1SignedSum_proxy, paperQStyleMainR1Majorant_proxy] using
    abs_paperQStyleMainR1SignedSum_le_majorant
      AnalyticNumberTheory.Sieve.logarithmicIntegral N z w y D X

/-- The natural cutoff obtained by flooring the paper's real exponent
`N^(1/4 - ε/2)`. -/
noncomputable def paperQSourceCutoff (N : ℕ) (ε : ℝ) : ℕ :=
  Nat.floor ((N : ℝ) ^ (1 / 4 - ε / 2 : ℝ))

/-- The source-facing finite set in Liu `main.tex` line 219: primes satisfying
the real, non-strict cutoff `p ≤ N^(1/4 - ε/2)` and not dividing `N`. The range
bound is only a finite carrier; `mem_liuPaperQPrimes` exposes the source formula. -/
noncomputable def liuPaperQPrimes (N : ℕ) (ε : ℝ) : Finset ℕ :=
  (range (paperQSourceCutoff N ε + 1)).filter fun p =>
    p.Prime ∧ ¬p ∣ N ∧
      (p : ℝ) ≤ (N : ℝ) ^ (1 / 4 - ε / 2 : ℝ)

/-- Membership in Liu's source-facing prime set is exactly the real inequality
printed in `main.tex` line 219, together with primality and `p ∤ N`. -/
theorem mem_liuPaperQPrimes {N p : ℕ} {ε : ℝ} :
    p ∈ liuPaperQPrimes N ε ↔
      p.Prime ∧ ¬p ∣ N ∧
        (p : ℝ) ≤ (N : ℝ) ^ (1 / 4 - ε / 2 : ℝ) := by
  have hpow : 0 ≤ (N : ℝ) ^ (1 / 4 - ε / 2 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  simp only [liuPaperQPrimes, mem_filter, mem_range]
  rw [show p < paperQSourceCutoff N ε + 1 ↔
      p ≤ paperQSourceCutoff N ε by omega]
  rw [show p ≤ paperQSourceCutoff N ε ↔
      (p : ℝ) ≤ (N : ℝ) ^ (1 / 4 - ε / 2 : ℝ) by
    exact Nat.le_floor_iff hpow]
  tauto

/-- Flooring the nonnegative real power loses no natural primes at the
non-strict source cutoff. -/
theorem liuPaperQPrimes_eq_paperQStylePrimes (N : ℕ) (ε : ℝ) :
    liuPaperQPrimes N ε =
      paperQStylePrimes N (paperQSourceCutoff N ε) := by
  ext p
  rw [mem_liuPaperQPrimes]
  have hpow : 0 ≤ (N : ℝ) ^ (1 / 4 - ε / 2 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  simp only [paperQStylePrimes, mem_filter, mem_range]
  rw [show p < paperQSourceCutoff N ε + 1 ↔
      p ≤ paperQSourceCutoff N ε by omega]
  rw [show p ≤ paperQSourceCutoff N ε ↔
      (p : ℝ) ≤ (N : ℝ) ^ (1 / 4 - ε / 2 : ℝ) by
    exact Nat.le_floor_iff hpow]
  tauto

/-- Liu's source modulus `Q`, defined from the real cutoff in line 219. -/
noncomputable def liuPaperQModulus (N : ℕ) (ε : ℝ) : ℕ :=
  (liuPaperQPrimes N ε).prod id

/-- Liu's real-cutoff modulus is exactly the generic floor-cutoff modulus. -/
theorem liuPaperQModulus_eq_paperQStyleModulus (N : ℕ) (ε : ℝ) :
    liuPaperQModulus N ε =
      paperQStyleModulus N (paperQSourceCutoff N ε) := by
  rw [liuPaperQModulus, paperQStyleModulus,
    liuPaperQPrimes_eq_paperQStylePrimes]

/-- The fully source-specialized finite `R₁` majorant, whose outer divisors use
the real-cutoff modulus `liuPaperQModulus` and whose weight lower cutoff remains
the distinct `liuSourceZ10`. -/
noncomputable def liuPaperQSourceR1Majorant
    (main : ℝ → ℝ) (N : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ (liuPaperQModulus N ε).divisors.filter
      (fun d => d ≤ liuSourceD2 N),
    (3 : ℝ) ^ d.primeFactors.card *
      liuMainNoncoprimeMajorant main N N d (N % d)
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))

/-- The source-Q majorant is exactly the generic floor-cutoff specialization. -/
theorem liuPaperQSourceR1Majorant_eq_paperQStyleSourceR1Majorant
    (main : ℝ → ℝ) (N : ℕ) (ε : ℝ) :
    liuPaperQSourceR1Majorant main N ε =
      paperQStyleSourceR1Majorant main N
        (liuSourceZ10 N) (paperQSourceCutoff N ε)
        (liuSourceY3 N) (liuSourceD2 N) := by
  rw [liuPaperQSourceR1Majorant, paperQStyleSourceR1Majorant,
    paperQStyleMainR1Majorant, paperQStyleR1Divisors,
    liuPaperQModulus_eq_paperQStyleModulus]

/-- Under the elementary source assumptions, the exponent cutoff is no larger
than the floored cube-root cutoff. -/
theorem paperQSourceCutoff_le_floor_cuberoot (N : ℕ) (ε : ℝ)
    (hN : 1 ≤ N) (hε : 0 ≤ ε) :
    paperQSourceCutoff N ε ≤ Nat.floor ((N : ℝ) ^ (1 / 3 : ℝ)) := by
  unfold paperQSourceCutoff
  apply Nat.floor_mono
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast hN
  · nlinarith

/-- The floored source cube-root cutoff is no larger than `N` for `N ≥ 1`. -/
theorem liuSourceY3_le (N : ℕ) (hN : 1 ≤ N) :
    liuSourceY3 N ≤ N := by
  have hbase : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow : (N : ℝ) ^ (1 / 3 : ℝ) ≤ (N : ℝ) := by
    calc
      (N : ℝ) ^ (1 / 3 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hbase (by norm_num)
      _ = (N : ℝ) := Real.rpow_one _
  have hfloor : (liuSourceY3 N : ℝ) ≤ (N : ℝ) := by
    calc
      (liuSourceY3 N : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by
        unfold liuSourceY3
        exact Nat.floor_le (Real.rpow_nonneg (by positivity) _)
      _ ≤ (N : ℝ) := hpow
  exact_mod_cast hfloor

/-- **Conditional source-cutoff endpoint.** For `ε ≥ 0`, the natural floored
paper cutoff meets both cutoff hypotheses of
`paperQStyleSourceR1Majorant_le_log_square`. The `PaperLiUpperModel` hypothesis
is retained explicitly; no unconditional R1 or true-li identification follows. -/
theorem PaperLiUpperModel.paperQStyleSourceR1Majorant_le_log_square_cutoff
    {main : ℝ → ℝ} {C : ℝ} (N : ℕ) (ε : ℝ)
    (hmain : PaperLiUpperModel main C) (hN : 8 ≤ N) (hε : 0 ≤ ε) :
    paperQStyleSourceR1Majorant main N
        (liuSourceZ10 N) (paperQSourceCutoff N ε)
        (liuSourceY3 N) (liuSourceD2 N) ≤
      15 * C * liuSourceR1P₂ReciprocalBound *
        paperQStyleDivisorWeightLogConstant *
        (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 2 := by
  have hcut : paperQSourceCutoff N ε ≤ liuSourceY3 N := by
    simpa [liuSourceY3] using
      paperQSourceCutoff_le_floor_cuberoot N ε (by omega) hε
  exact hmain.paperQStyleSourceR1Majorant_le_log_square
    N (paperQSourceCutoff N ε) hN hcut
    (hcut.trans (liuSourceY3_le N (by omega)))

end MathlibNt.SieveTheory.LiuWeight
