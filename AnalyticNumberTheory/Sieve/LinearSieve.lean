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

/-- A sequence of coefficients is lower Möbius when its divisor sums lie below
the coprimality indicator.  This is the exact finite dual of Mathlib's
`BoundingSieve.IsUpperMoebius`. -/
def IsLowerMoebius (muMinus : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, ∑ d ∈ n.divisors, muMinus d ≤ if n = 1 then 1 else 0

/-- A lower Möbius sequence gives a lower bound for the sifted sum before any
asymptotic estimate is introduced. -/
theorem sum_of_lowerMoebius_le_siftedSum {S : BoundingSieve}
    (muMinus : ℕ → ℝ) (hmu : IsLowerMoebius muMinus) :
    ∑ d ∈ S.prodPrimes.divisors, muMinus d * S.multSum d ≤ S.siftedSum := by
  calc
    ∑ d ∈ S.prodPrimes.divisors, muMinus d * S.multSum d =
        ∑ n ∈ S.support, ∑ d ∈ S.prodPrimes.divisors,
          if d ∣ n then S.weights n * muMinus d else 0 := by
      symm
      rw [Finset.sum_comm]
      simp_rw [BoundingSieve.multSum, ← Finset.sum_filter, Finset.mul_sum, mul_comm]
    _ = ∑ n ∈ S.support, S.weights n *
        ∑ d ∈ (Nat.gcd S.prodPrimes n).divisors, muMinus d := by
      symm
      simp_rw [Finset.mul_sum, ← Finset.sum_filter]
      congr with n
      congr
      · rw [← Nat.divisors_filter_dvd_of_dvd S.prodPrimes_ne_zero
          (Nat.gcd_dvd_left _ _)]
        ext x
        simp +contextual [Nat.dvd_gcd_iff]
    _ ≤ S.siftedSum := by
      rw [S.siftedSum_eq_sum_support_mul_ite]
      gcongr with n
      exact hmu (Nat.gcd S.prodPrimes n)

/-- Explicit-error lower sieve inequality.  Unlike the historical pointwise
interfaces, the loss is the concrete finite quantity `errSum muMinus`. -/
theorem mainSum_sub_errSum_le_siftedSum_of_lowerMoebius {S : BoundingSieve}
    (muMinus : ℕ → ℝ) (hmu : IsLowerMoebius muMinus) :
    S.totalMass * S.mainSum muMinus - S.errSum muMinus ≤ S.siftedSum := by
  have hrem : -S.errSum muMinus ≤
      ∑ d ∈ S.prodPrimes.divisors, muMinus d * S.rem d := by
    rw [BoundingSieve.errSum, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro d hd
    rw [← abs_mul]
    exact neg_abs_le _
  calc
    S.totalMass * S.mainSum muMinus - S.errSum muMinus ≤
        S.totalMass * S.mainSum muMinus +
          ∑ d ∈ S.prodPrimes.divisors, muMinus d * S.rem d := by
      linarith
    _ = ∑ d ∈ S.prodPrimes.divisors, muMinus d * S.multSum d := by
      rw [BoundingSieve.mainSum, Finset.mul_sum, ← Finset.sum_add_distrib]
      congr with d
      rw [BoundingSieve.rem]
      ring
    _ ≤ S.siftedSum := sum_of_lowerMoebius_le_siftedSum muMinus hmu

/-! ## 1. Euler--Mascheroni constant -/

/-- The Euler--Mascheroni constant `γ ≈ 0.5772...`, defined as the
limit of the difference between the harmonic sum and the logarithm. -/
noncomputable abbrev eulerMascheroni : ℝ :=
  -- Use mathlib's Real.eulerMascheroniConstant.
  Real.eulerMascheroniConstant

/-! ## 2. Sieve functions F(s) and f(s) -/

/-- Piecewise upper sieve function `F(s)`:
  - `s ≤ 2`: `F(s) = 1`, the trivial branch;
  - `2 < s ≤ 4`: `F(s) = 2e^γ / s`;
  - `s > 4`: an approximate extension is used here.

The full extension would require the delay-differential recursion
`(s·F(s))' = f(s-1)`; it is not defined by that recursion here. -/
noncomputable def sieveFunctionF (s : ℝ) : ℝ :=
  if s ≤ 2 then
    1
  else if s ≤ 4 then
    2 * exp eulerMascheroni / s
  else
    -- For s > 4, use an approximate extension rather than the recursive definition.
    -- An exact extension requires a Buchstab-type recursion.
    2 * exp eulerMascheroni / s * (1 + 1 / s)

/-- Lower sieve function `f(s)` of the Jurkat--Richert linear sieve.

  - s ≤ 3:  f(s) = 0
  - 3 < s ≤ 5:  f(s) = 2e^γ · log((s - 1) / 2) / s
  - s > 5:  placeholder (the Buchstab delay recursion is not yet formalized)

The formula on `(3, 5]` is the standard Jurkat--Richert value: with
`F(s) = 2e^γ / s` on `[2, 4]`, the delay equation `(s·f(s))' = F(s - 1)` and
the boundary value `f(3) = 0` give
`f(s) = (2e^γ / s) · log((s - 1) / 2)` for `3 ≤ s ≤ 5`.  This is the value
used at the Chen sieve ratio `s = D/z ≈ 5`.

For `s > 5` the recursion must continue through the Buchstab-type `F`; the
expression below is only a placeholder and must not be used to justify
Chen's classical constants. -/
noncomputable def sieveFunctionf (s : ℝ) : ℝ :=
  if s ≤ 3 then
    0
  else if s ≤ 5 then
    2 * exp eulerMascheroni / s * log ((s - 1) / 2)
  else
    -- For s > 5, use an approximate extension rather than the recursive definition.
    2 * exp eulerMascheroni / s * log ((s - 1) / 2) * (1 + 1 / s)

/-! ## 3. Basic properties of the sieve functions -/

/-- `F(s)` is positive on `[2,4]`. -/
theorem sieveF_pos_on_2_4 {s : ℝ} (_hs : 2 ≤ s) (hs' : s ≤ 4) :
    0 < sieveFunctionF s := by
  unfold sieveFunctionF
  by_cases h2 : s ≤ 2
  · rw [if_pos h2]; norm_num
  · rw [if_neg h2, if_pos hs']
    have hs_pos : 0 < s := by linarith
    exact div_pos (mul_pos (by norm_num) (exp_pos eulerMascheroni)) hs_pos

/-- `f(s)` is positive on `(3,5]`. -/
theorem sievef_pos_on_3_5 {s : ℝ} (hs : 3 < s) (hs' : s ≤ 5) :
    0 < sieveFunctionf s := by
  unfold sieveFunctionf
  have h1 : ¬ s ≤ 3 := by linarith
  rw [if_neg h1, if_pos hs']
  have hs_pos : 0 < s := by linarith
  have h_log : 0 < log ((s - 1) / 2) := by
    apply log_pos
    field_simp
    linarith
  positivity
/-- `f(s) ≤ F(s)`: the lower sieve function does not exceed the upper
one on `[2,4]`.

- For `s ≤ 2`, `F = 1` and `f = 0`.
- For `2 < s ≤ 3`, `F = 2e^γ/s > 0` and `f = 0`.
- For `3 < s ≤ 4`, `F = 2e^γ/s` and
  `f = 2e^γ/s·log((s-1)/2)`.
  By `log_le_sub_one`, `log((s-1)/2) ≤ (s-1)/2 - 1 ≤ 1`
  since `s ≤ 4`, so `f ≤ F`.

The classical range `s > 4` requires the full Buchstab-type
delay-differential analysis. -/
theorem sievef_le_sieveF {s : ℝ} (hs : 2 ≤ s) (hs' : s ≤ 4) :
    sieveFunctionf s ≤ sieveFunctionF s := by
  unfold sieveFunctionF sieveFunctionf
  by_cases h2 : s ≤ 2
  · -- s ≤ 2: F = 1 and f = 0, since s ≤ 3.
    have h3 : s ≤ (3 : ℝ) := le_trans h2 (by norm_num)
    simp only [if_pos h2, if_pos h3]
    norm_num
  · -- s > 2: F = 2e^γ/s, since s ≤ 4.
    have hs_pos : 0 < s := by linarith
    by_cases h3 : s ≤ (3 : ℝ)
    · -- 2 < s ≤ 3: F = 2e^γ/s, f = 0
      simp only [if_neg h2, if_pos hs', if_pos h3]
      positivity
    · -- 3 < s ≤ 4: F = 2e^γ/s, f = 2e^γ/s · log((s-1)/2)
      have h5 : s ≤ (5 : ℝ) := by linarith
      simp only [if_neg h2, if_pos hs', if_neg h3, if_pos h5]
      have hs2_pos : 0 < (s - 1) / 2 := by linarith
      -- log((s-1)/2) ≤ (s-1)/2 - 1 ≤ 1, since s ≤ 4.
      have h_log_le : log ((s - 1) / 2) ≤ 1 := by
        calc log ((s - 1) / 2) ≤ (s - 1) / 2 - 1 := Real.log_le_sub_one_of_pos hs2_pos
          _ ≤ 1 := by linarith
      -- 2e^γ/s · log((s-1)/2) ≤ 2e^γ/s · 1 = 2e^γ/s
      have h_factor : 0 ≤ 2 * exp eulerMascheroni / s := by positivity
      exact mul_le_of_le_one_right h_factor h_log_le

/-! ## 4. Sieve setup via Mathlib.BoundingSieve -/

/-- **Sieve problem for Chen's theorem**: extend mathlib's `BoundingSieve`
with a sifting level `z` and distribution level `D`.

The correspondence with classical notation is:
  - `support`: `A`, the set to sift, for example `{N-p : p is prime}`;
  - `totalMass`: `X`, an approximation to `|A|`, for example `N/log N`;
  - `nu`: the multiplicative density `ν`, an `ArithmeticFunction ℝ`;
  - `weights`: identically 1 in the unweighted counting specialization;
  - `prodPrimes`: the product of primes below `z`;
  - `siftedSum`: mathlib's inherited sum of weights over elements coprime
    to `prodPrimes`.

Additional fields specify `z` (removing multiples of primes below `z`),
`D` (the range of controlled remainders), and `prodPrimes_eq`
(the required prime-product representation). -/
structure SieveProblem extends BoundingSieve where
  /-- Sifting level `z`: remove multiples of primes below `z`. -/
  z : ℝ
  hz_pos : 0 < z
  /-- Distribution level `D`: the range of controlled remainders,
classically supplied by Bombieri--Vinogradov. -/
  D : ℝ
  hD_pos : 0 < D
  /-- `prodPrimes` is the product of primes below `z`. -/
  prodPrimes_eq : prodPrimes = ((Finset.range ⌈z⌉₊).filter Nat.Prime).prod id

/-- **Counting bridge**: mathlib's
`siftedSum = ∑ d ∈ support, if Coprime prodPrimes d then weights d else 0`
equals `|{a ∈ A : ∀ p prime, p < z → ¬ p ∣ a}|`
when `prodPrimes` is the product of primes below `z` and
`weights = 1` (the hypothesis `hweights`). -/
theorem siftedSum_eq_filter (SP : SieveProblem) (hweights : ∀ n, SP.weights n = 1) :
    SP.siftedSum =
      (SP.support.filter (fun a => ∀ p : ℕ, p.Prime → (p : ℝ) < SP.z → ¬ p ∣ a)).sum (fun _ => (1 : ℝ)) := by
  -- The primeFactors of a product of distinct primes equal the original prime set.
  -- By prodPrimes_eq, the prime factors are exactly (range ⌈z⌉₊).filter Prime.
  have h_ppf : SP.prodPrimes.primeFactors = (Finset.range ⌈SP.z⌉₊).filter Nat.Prime := by
    rw [SP.prodPrimes_eq]
    exact Nat.primeFactors_prod (fun p hp => (Finset.mem_filter.mp hp).2)
  -- For a prime p, p ∣ prodPrimes if and only if (p : ℝ) < z.
  --   (⇒) p ∣ prodPrimes ⇒ p ∈ primeFactors = (range ⌈z⌉₊).filter Prime ⇒ p < ⌈z⌉₊ ⇒ (p:ℝ) < z.
  --   (⇐) (p:ℝ) < z ⇒ p < ⌈z⌉₊ (Nat.lt_ceil) ⇒ p ∈ range ⇒ p ∣ prod (Finset.dvd_prod_of_mem).
  have h_dvd_iff : ∀ p : ℕ, p.Prime → (p ∣ SP.prodPrimes ↔ (p : ℝ) < SP.z) := by
    intro p hp
    refine ⟨fun hdvd => ?_, fun hpz => ?_⟩
    · -- p ∣ prodPrimes ⇒ (p : ℝ) < z
      have h_mem : p ∈ SP.prodPrimes.primeFactors :=
        Nat.Prime.mem_primeFactors hp hdvd SP.prodPrimes_ne_zero
      rw [h_ppf, Finset.mem_filter, Finset.mem_range] at h_mem
      exact Nat.lt_ceil.mp h_mem.1
    · -- (p : ℝ) < z ⇒ p ∣ prodPrimes
      have hp_range : p < ⌈SP.z⌉₊ := Nat.lt_ceil.mpr hpz
      have hp_mem : p ∈ (Finset.range ⌈SP.z⌉₊).filter Nat.Prime := by
        rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hp_range, hp⟩
      rw [SP.prodPrimes_eq]
      exact Finset.dvd_prod_of_mem id hp_mem
  -- Main equivalence: Nat.gcd prodPrimes a = 1 iff every prime p with (p:ℝ) < z fails to divide a.
  -- Forward: if p divides both prodPrimes and a, then p divides gcd = 1, contradicting primality.
  -- Reverse: by Nat.eq_one_iff_not_exists_prime_dvd, a gcd different from 1 has a prime divisor p.
  -- Then p divides prodPrimes, so (p:ℝ) < z, and p divides a, contradicting the hypothesis.
  have hkey : ∀ a : ℕ, Nat.gcd SP.prodPrimes a = 1 ↔
      ∀ p : ℕ, p.Prime → (p : ℝ) < SP.z → ¬ p ∣ a := by
    intro a
    refine ⟨fun hcop p hp hpz hpa => ?_, fun h => ?_⟩
    · have hp_dvd_PP : p ∣ SP.prodPrimes := (h_dvd_iff p hp).mpr hpz
      have hp_gcd : p ∣ Nat.gcd SP.prodPrimes a := Nat.dvd_gcd hp_dvd_PP hpa
      rw [hcop] at hp_gcd
      exact hp.not_dvd_one hp_gcd
    · rw [Nat.eq_one_iff_not_exists_prime_dvd]
      intro p hp hp_gcd
      have hp_dvd_PP : p ∣ SP.prodPrimes := hp_gcd.trans (Nat.gcd_dvd_left _ _)
      have hp_a : p ∣ a := hp_gcd.trans (Nat.gcd_dvd_right _ _)
      exact h p hp ((h_dvd_iff p hp).mp hp_dvd_PP) hp_a
  -- Expand siftedSum using siftedSum_eq_sum_support_mul_ite and substitute weights = 1.
  -- Convert the conditional to a filter with Finset.sum_filter, then simplify its predicate using hkey.
  rw [SP.siftedSum_eq_sum_support_mul_ite]
  simp_rw [hweights, one_mul]
  rw [← Finset.sum_filter]
  exact Finset.sum_congr (Finset.filter_congr fun d _ => hkey d) (fun _ _ => rfl)

/-- **Sieve product** `V(z) = Π_{p < z} (1 - ν(p))`, the product appearing
in the Jurkat--Richert main term `X·V(z)·f(s)`.

Mathlib's `selbergTerms d = ν(d)·Π_{p|d} (1 - ν(p))⁻¹`.
At `d = prodPrimes`, the product of primes below `z`, this gives
`selbergTerms prodPrimes = ν(prodPrimes)/V(z)`, hence
`V(z) = ν(prodPrimes)/selbergTerms(prodPrimes)`.
Mathlib's density is normalized as `ν(p) = ω(p)/p`, so
`1 - ν(p) = 1 - ω(p)/p` is the standard sieve factor. -/
noncomputable def sieveProduct (SP : SieveProblem) : ℝ :=
  ((Finset.range ⌈SP.z⌉₊).filter Nat.Prime).prod
    (fun p => 1 - SP.nu p)

/-- **Product bridge**:
`sieveProduct = Π_{p | prodPrimes} (1 - ν(p))`.
By `prodPrimes_eq`, for prime `p`, divisibility by `prodPrimes`
is equivalent to `p < z`. -/
theorem sieveProduct_eq_prod_one_sub_nu (SP : SieveProblem) :
    sieveProduct SP =
      ∏ p ∈ SP.prodPrimes.primeFactors, (1 - SP.nu p) := by
  -- The primeFactors of the product of a prime set equal that set.
  -- Apply this to obtain SP.prodPrimes.primeFactors = (range ⌈z⌉).filter Prime.
  have h_eq : SP.prodPrimes.primeFactors = (Finset.range ⌈SP.z⌉₊).filter Nat.Prime := by
    rw [SP.prodPrimes_eq]
    exact Nat.primeFactors_prod (fun p hp => (Finset.mem_filter.mp hp).2)
  rw [sieveProduct, h_eq]

/-- **Selberg-term bridge**:
`sieveProduct · selbergTerms(prodPrimes) = ν(prodPrimes)`.
By mathlib's `selbergTerms_apply`,
`selbergTerms d = ν(d)·Π_{p|d} (1 - ν(p))⁻¹`.
For `d = prodPrimes`, this is
`ν(prodPrimes)·Π_{p|prodPrimes} (1 - ν(p))⁻¹
 = ν(prodPrimes)/sieveProduct`; multiplying gives the identity. -/
theorem sieveProduct_mul_selbergTerms_eq_nu (SP : SieveProblem) :
    sieveProduct SP * SP.selbergTerms SP.prodPrimes = SP.nu SP.prodPrimes := by
  -- By selbergTerms_apply, selbergTerms d = nu d * ∏_{p|d} (1 - nu p)⁻¹.
  -- By sieveProduct_eq_prod_one_sub_nu, sieveProduct = ∏_{p|d} (1 - nu p).
  -- Thus sieveProduct * selbergTerms = ∏(1-nu p) * nu(PP) * ∏(1-nu p)⁻¹.
  --                                = nu(PP) * (∏(1-nu p) * ∏(1-nu p)⁻¹) = nu(PP)
  rw [SP.selbergTerms_apply, sieveProduct_eq_prod_one_sub_nu]
  -- Goal: (∏(1-nu p)) * (nu(PP) * ∏(1-nu p)⁻¹) = nu(PP)
  -- Each (1 - nu p) is nonzero, since nu_lt_one_of_prime gives nu p < 1.
  have h_nz : ∀ p ∈ SP.prodPrimes.primeFactors, (1 - SP.nu p) ≠ 0 := by
    intro p hp
    obtain ⟨hp_p, hp_dvd, _⟩ := Nat.mem_primeFactors.mp hp
    exact ne_of_gt (by linarith [SP.nu_lt_one_of_prime p hp_p hp_dvd])
  -- ∏(1-nu p)⁻¹ = (∏(1-nu p))⁻¹
  rw [Finset.prod_inv_distrib]
  -- Goal: A * (B * A⁻¹) = B, where A = ∏(1-nu p) and B = nu(PP).
  -- = A * B * A⁻¹ = B * A * A⁻¹ = B * 1 = B
  have h_A_ne_zero : (∏ p ∈ SP.prodPrimes.primeFactors, (1 - SP.nu p)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p hp => h_nz p hp)
  rw [mul_left_comm, mul_inv_cancel₀ h_A_ne_zero, mul_one]

/-- **Quotient bridge**:
`sieveProduct = ν(prodPrimes)/selbergTerms(prodPrimes)`. -/
theorem sieveProduct_eq_nu_div_selbergTerms (SP : SieveProblem) :
    sieveProduct SP = SP.nu SP.prodPrimes / SP.selbergTerms SP.prodPrimes := by
  -- By sieveProduct_mul_selbergTerms_eq_nu, sieveProduct * selbergTerms(PP) = nu(PP).
  -- Divide by the positive selbergTerms(PP) to obtain sieveProduct = nu(PP)/selbergTerms(PP).
  have h := sieveProduct_mul_selbergTerms_eq_nu SP
  -- h : sieveProduct * selbergTerms(PP) = nu(PP)
  have h_st_pos : 0 < SP.selbergTerms SP.prodPrimes :=
    SP.selbergTerms_pos (dvd_refl SP.prodPrimes)
  -- eq_div_iff: a = c / b iff a * b = c, for b ≠ 0.
  rw [eq_div_iff h_st_pos.ne']
  exact h

/-- **Distribution identity**: for `d ≤ D`, the counting specialization is
`|{a ∈ A : d | a}| = ν(d)·X + R_d`.
This is mathlib's `multSum_eq_main_err`,
`multSum d = nu d * totalMass + rem d`.
The remainder `rem d` is `R_d`; the distribution level describes the
range where it should be negligible, but this identity alone gives
no remainder estimate. -/
theorem distribution_condition (SP : SieveProblem) (d : ℕ) (_hd : (d : ℝ) ≤ SP.D) (_hd_pos : 1 ≤ d) :
    SP.multSum d = SP.nu d * SP.totalMass + SP.rem d := by
  exact SP.multSum_eq_main_err d

/-! ## 5. Fixed-parameter Jurkat--Richert-shaped bounds -/

/-- **Upper-bound remainder interface**. The classical
Jurkat--Richert upper bound has the form
`S(A,z) ≤ X·V(z)·(F(s) + O(η)) + Σ_{d ≤ D} |R_d|`.
Mathlib's `siftedSum_le_mainSum_errSum_of_upperMoebius` gives
`siftedSum ≤ totalMass·mainSum(μ⁺) + errSum(μ⁺)`.
The analytic theorem further estimates
`mainSum(μ⁺) ≤ V(z)·F(s)` and `errSum ≤ Σ |R_d|`.
These are ingredients for the upper bound on `Ω` in Chen's theorem.

The present interface only asks for an unspecified additive error for
a single `SP`; the absolute difference of the two sides supplies it.
It is not a uniform Jurkat--Richert estimate, which must relate
`C_error` to explicit bounds on `SP.rem`. -/
theorem jurkat_richert_upper_bound (SP : SieveProblem)
    (_hs : 2 ≤ SP.D / SP.z) :
    ∃ C_error : ℝ,
      SP.siftedSum ≤
        SP.totalMass * sieveProduct SP * (sieveFunctionF (SP.D / SP.z)) + C_error := by
  -- The classical argument would use the following additional estimates; the proof below only constructs an additive remainder.
  -- 1. Use siftedSum_le_mainSum_errSum_of_upperMoebius:
  --    siftedSum ≤ totalMass * mainSum(μ⁺) + errSum(μ⁺)
  -- 2. Jurkat--Richert estimates mainSum(μ⁺) ≤ V(z) * F(s).
  -- 3. Bound errSum(μ⁺) by Σ_{d≤D} |R_d|.
  -- 4. Combine to obtain siftedSum ≤ X * V(z) * F(s) + Σ |R_d|.
  refine ⟨|SP.siftedSum - SP.totalMass * sieveProduct SP *
    sieveFunctionF (SP.D / SP.z)|, ?_⟩
  have h := le_abs_self (SP.siftedSum - SP.totalMass * sieveProduct SP *
    sieveFunctionF (SP.D / SP.z))
  linarith

/-- **Lower-bound remainder interface**. The classical
Jurkat--Richert lower bound has the form
`S(A,z) ≥ X·V(z)·(f(s) - O(η)) - Σ_{d ≤ D} |R_d|`.
It is a theoretical input to the Chen estimate
`W(N) ≥ 2.6408 𝔖(N) N/log²N`.

Here the quantifiers only assert an additive remainder for each
individual `SP`; the uniform analytic lower bound is a separate input. -/
theorem jurkat_richert_lower_bound (SP : SieveProblem)
    (_hs : 3 < SP.D / SP.z) :
    ∃ C_error : ℝ,
      SP.siftedSum ≥
        SP.totalMass * sieveProduct SP * (sieveFunctionf (SP.D / SP.z)) - C_error := by
  -- A substantive lower sieve uses a lower Moebius condition, with the finite lower-sieve bridge supplied above.
  -- See Halberstam--Richert, Ch. 8.
  refine ⟨|SP.totalMass * sieveProduct SP * sieveFunctionf (SP.D / SP.z) -
    SP.siftedSum|, ?_⟩
  have h := le_abs_self (SP.totalMass * sieveProduct SP *
    sieveFunctionf (SP.D / SP.z) - SP.siftedSum)
  linarith

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

/-- The two sieve-product definitions agree for a classical `SieveProblem`. -/
theorem sieveProduct_eq_sieveProductPrimeFactors (SP : SieveProblem) :
    sieveProduct SP = sieveProductPrimeFactors SP.toBoundingSieve := by
  simpa [sieveProduct, sieveProductPrimeFactors] using sieveProduct_eq_prod_one_sub_nu SP

/-- If `|μ(d)| ≤ 1`, then `errSum μ ≤ errSum 1`.
This replaces `errSum(μ⁻)` in a uniform lower-bound argument by the
explicit `errSum(1) = Σ_{d | prodPrimes} |rem d|`, corresponding to
the classical `Σ_{d ≤ D} |R_d|`. -/
theorem errSum_le_of_abs_le_one {S : BoundingSieve} {mu : ℕ → ℝ}
    (h : ∀ d : ℕ, |mu d| ≤ 1) :
    S.errSum mu ≤ S.errSum (fun _ => 1) := by
  unfold BoundingSieve.errSum
  apply Finset.sum_le_sum
  intro d hd
  have hmul : |mu d| * |S.rem d| ≤ (1 : ℝ) * |S.rem d| :=
    mul_le_mul_of_nonneg_right (h d) (abs_nonneg (S.rem d))
  simpa using hmul

/-- **Finite lower-bound bridge**: given a lower Moebius sequence
`muMinus` with coefficients bounded in absolute value by 1, a main-term
estimate `V·(fs(t) - η) ≤ mainSum(μ⁻)`, and nonnegative total mass,
one obtains `X·V·(fs(t) - η) - errSum(1) ≤ siftedSum`.
Combine `mainSum_sub_errSum_le_siftedSum_of_lowerMoebius` with
`errSum_le_of_abs_le_one`. Classically this corresponds to
`S(A,z) ≥ X·V(z)·(f(s) - O(η)) - Σ_{d ≤ D} |R_d|`. -/
theorem siftedSum_lower_bound_of_mainTerm {S : BoundingSieve} {fs : ℝ → ℝ}
    {t η : ℝ} {muMinus : ℕ → ℝ} (hmass : 0 ≤ S.totalMass)
    (hmu : IsLowerMoebius muMinus)
    (hbnd : ∀ d : ℕ, |muMinus d| ≤ 1)
    (hmain : sieveProductPrimeFactors S * (fs t - η) ≤ S.mainSum muMinus) :
    S.totalMass * sieveProductPrimeFactors S * (fs t - η) -
        S.errSum (fun _ => 1) ≤ S.siftedSum := by
  have herr : S.errSum muMinus ≤ S.errSum (fun _ => 1) :=
    errSum_le_of_abs_le_one hbnd
  have h1 : S.totalMass * S.mainSum muMinus - S.errSum muMinus ≤ S.siftedSum :=
    mainSum_sub_errSum_le_siftedSum_of_lowerMoebius muMinus hmu
  have hmain' : S.totalMass * (sieveProductPrimeFactors S * (fs t - η)) ≤
      S.totalMass * S.mainSum muMinus :=
    mul_le_mul_of_nonneg_left hmain hmass
  have h2 : S.totalMass * sieveProductPrimeFactors S * (fs t - η) -
      S.errSum (fun _ => 1) ≤ S.totalMass * S.mainSum muMinus - S.errSum muMinus := by
    have h2a : S.totalMass * sieveProductPrimeFactors S * (fs t - η) ≤
        S.totalMass * S.mainSum muMinus := by
      simpa [mul_assoc] using hmain'
    linarith
  exact le_trans h2 h1

/-- **Uniform main-term lower-bound proposition**.
There exist `N₀` and `η₀ > 0` such that for every even `N ≥ N₀`
there is a lower Moebius sequence `muMinus`, bounded in absolute value
by 1, satisfying
`mainSum(μ⁻) ≥ V_N·(fs(D_N/z_N) - η₀)`.
Here `V_N = ∏_{p | prodPrimes_N} (1 - ν_N(p))` and `fs` is the
chosen lower sieve function.

The constants `N₀` and `η₀` precede `∀ N` and cannot depend on `N`.
This records an additive-loss version of the classical estimate
`mainSum(μ⁻) ≥ V(z)·f(s)·(1 - O(η))`.
The API uses the ratio `D_N/z_N` as its function argument; identifying
that argument with the classical logarithmic sieve ratio
`log D/log z ≈ 5` requires a compatible choice of parameters. -/
def UniformJurkatRichertMainTerm (SP : ℕ → BoundingSieve)
    (zN DN : ℕ → ℝ) (fs : ℝ → ℝ) : Prop :=
  ∃ N₀ : ℕ, ∃ η₀ : ℝ, 0 < η₀ ∧
    ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ muMinus : ℕ → ℝ,
        IsLowerMoebius muMinus ∧
        (∀ d : ℕ, |muMinus d| ≤ 1) ∧
        sieveProductPrimeFactors (SP N) * (fs (DN N / zN N) - η₀) ≤
          (SP N).mainSum muMinus

/-- **Uniform sieve lower-bound proposition**.
The classical Halberstam--Richert/Chen form is
`S(A,z) ≥ X·V(z)·(f(s) - O(η)) - Σ_{d ≤ D} |R_d|`
uniformly for all sufficiently large even `N`.
The finite formulation here asks for `N₀` and `η₀ > 0` such that,
for each even `N ≥ N₀`, there is a lower Moebius sequence `muMinus`
bounded in absolute value by 1, with
`siftedSum ≥ X_N·V_N·(fs(D_N/z_N) - η₀) - errSum(1)`.
The explicit divisor error is
`errSum(1) = Σ_{d | prodPrimes_N} |rem_N d|`.

Quantifier order is essential: `N₀` and `η₀` precede `∀ N`, unlike
a fixed-parameter remainder interface (see `CHEN_PROOF_ATLAS`).
The implication from `UniformJurkatRichertMainTerm` uses
`siftedSum_lower_bound_of_mainTerm`; see
`UniformJurkatRichertLowerBound_of_uniformMainTerm`. -/
def UniformJurkatRichertLowerBound (SP : ℕ → BoundingSieve)
    (zN DN : ℕ → ℝ) (fs : ℝ → ℝ) : Prop :=
  ∃ N₀ : ℕ, ∃ η₀ : ℝ, 0 < η₀ ∧
    ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ muMinus : ℕ → ℝ,
        IsLowerMoebius muMinus ∧
        (∀ d : ℕ, |muMinus d| ≤ 1) ∧
        (SP N).totalMass * sieveProductPrimeFactors (SP N) *
            (fs (DN N / zN N) - η₀) -
          (SP N).errSum (fun _ => 1) ≤ (SP N).siftedSum

/-- A uniform main-term estimate and nonnegative total mass imply
the uniform sieve lower bound. -/
theorem UniformJurkatRichertLowerBound_of_uniformMainTerm
    (SP : ℕ → BoundingSieve) (zN DN : ℕ → ℝ) (fs : ℝ → ℝ)
    (hmass : ∀ N : ℕ, 0 ≤ (SP N).totalMass)
    (hmain : UniformJurkatRichertMainTerm SP zN DN fs) :
    UniformJurkatRichertLowerBound SP zN DN fs := by
  rcases hmain with ⟨N₀, η₀, hη₀, hN⟩
  refine ⟨N₀, η₀, hη₀, ?_⟩
  intro N hN₀ hEven
  rcases hN N hN₀ hEven with ⟨muMinus, hmu, hbnd, hmainN⟩
  refine ⟨muMinus, hmu, hbnd, ?_⟩
  exact siftedSum_lower_bound_of_mainTerm (S := SP N) (fs := fs) (t := DN N / zN N)
    (η := η₀) (muMinus := muMinus) (hmass := hmass N) hmu hbnd hmainN

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
