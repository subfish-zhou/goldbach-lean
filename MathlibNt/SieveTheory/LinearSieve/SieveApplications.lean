import MathlibNt.SieveTheory.LinearSieve.FiniteWeights

/-!
# Elementary sieve applications and remainder interfaces

Legacy sieve functions, the weighted sieve problem, counting and product
identities, and fixed-parameter remainder interfaces.
-/

namespace MathlibNt.SieveTheory.LinearSieve

open Real BoundingSieve

open scoped Classical

/-! ## 1. The Euler-Mascheroni constant -/

/-- The Euler-Mascheroni constant γ ≈ 0.5772...

It is defined as the limit of the difference between the harmonic partial
sums and the logarithm. -/
noncomputable abbrev eulerMascheroni : ℝ :=
  -- Use Mathlib's Real.eulerMascheroniConstant.
  Real.eulerMascheroniConstant

/-! ## 2. The sieve functions F(s) and f(s) -/

/-- Legacy placeholder for an upper sieve function.

  - s ≤ 2: F(s) = 1 (the trivial-bound branch);
  - 2 < s ≤ 4: F(s) = 2e^γ / s;
  - s > 4: a placeholder approximation rather than the recursion
    from the differential-delay equation (s·F(s))' = f(s-1).

Only the indicated explicit branch is implemented; extending the intended
sieve function requires recursion. This is not the canonical dimension-one
function used by the generic Rosser density interfaces. -/
noncomputable def sieveFunctionF (s : ℝ) : ℝ :=
  if s ≤ 2 then
    1
  else if s ≤ 4 then
    2 * exp eulerMascheroni / s
  else
    -- For s > 4, this approximation stands in for the recursive definition.
    -- The intended definition requires a Buchstab-type recursion.
    2 * exp eulerMascheroni / s * (1 + 1 / s)

/-- A nonstandard working normalization for a lower sieve function.

  - s ≤ 3:  f(s) = 0
  - 3 < s ≤ 5:  a local `log (s / 2)` surrogate
  - s > 5:  a further placeholder approximation

This is **not** claimed to be the standard Jurkat--Richert/Buchstab lower
sieve function (whose normalization and differential-delay recursion must be
formalized separately).  It is used only in the fixed-parameter working
interfaces below and must not be used to justify Chen's classical constants. -/
noncomputable def sieveFunctionf (s : ℝ) : ℝ :=
  if s ≤ 3 then
    0
  else if s ≤ 5 then
    2 * exp eulerMascheroni / s * log (s / 2)
  else
    -- For s > 5, this approximation stands in for the recursive definition.
    2 * exp eulerMascheroni / s * log (s / 2) * (1 + 1 / s)

/-! ## 3. Basic properties of the sieve functions -/

/-- F(s) is positive on [2, 4]. -/
theorem sieveF_pos_on_2_4 {s : ℝ} (hs : 2 ≤ s) (hs' : s ≤ 4) :
    0 < sieveFunctionF s := by
  unfold sieveFunctionF
  by_cases h2 : s ≤ 2
  · rw [if_pos h2]; norm_num
  · rw [if_neg h2, if_pos hs']
    have hs_pos : 0 < s := by linarith
    exact div_pos (mul_pos (by norm_num) (exp_pos eulerMascheroni)) hs_pos

/-- f(s) is positive on (3, 5]. -/
theorem sievef_pos_on_3_5 {s : ℝ} (hs : 3 < s) (hs' : s ≤ 5) :
    0 < sieveFunctionf s := by
  unfold sieveFunctionf
  have h1 : ¬ s ≤ 3 := by linarith
  rw [if_neg h1, if_pos hs']
  have hs_pos : 0 < s := by linarith
  have h_log : 0 < log (s / 2) := by
    apply log_pos
    field_simp
    linarith
  positivity
/-- f(s) ≤ F(s): the lower function does not exceed the upper function.

For s ∈ [2, 4], this follows by cases:
- s ≤ 2: F = 1, f = 0, and 0 ≤ 1.
- 2 < s ≤ 3: F = 2e^γ/s > 0 and f = 0.
- 3 < s ≤ 4: F = 2e^γ/s, f = 2e^γ/s·log(s/2).
  By `log_le_sub_one`, log(s/2) ≤ s/2-1 ≤ 1 since s ≤ 4, so f ≤ F.

For the intended sieve functions beyond s = 4, a full analysis of the
Buchstab-type differential-delay recursion is required. -/
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
    · -- 3 < s ≤ 4: F = 2e^γ/s, f = 2e^γ/s · log(s/2)
      have h5 : s ≤ (5 : ℝ) := by linarith
      simp only [if_neg h2, if_pos hs', if_neg h3, if_pos h5]
      have hs2_pos : 0 < s / 2 := by positivity
      -- log(s/2) ≤ s/2 - 1 ≤ 1, since s ≤ 4.
      have h_log_le : log (s / 2) ≤ 1 := by
        calc log (s / 2) ≤ s / 2 - 1 := Real.log_le_sub_one_of_pos hs2_pos
          _ ≤ 1 := by linarith
      -- 2e^γ/s · log(s/2) ≤ 2e^γ/s · 1 = 2e^γ/s
      have h_factor : 0 ≤ 2 * exp eulerMascheroni / s := by positivity
      exact mul_le_of_le_one_right h_factor h_log_le

/-! ## 4. Sieve setup (aligned with Mathlib's `BoundingSieve`) -/

/-- **Sieve problem for Chen's theorem**: extend Mathlib's `BoundingSieve`
with a sifting level z and a level of distribution D.

Correspondence with Mathlib's `BoundingSieve`:
  - `support` ← A, the set to be sifted, such as {N - p : p prime};
  - `totalMass` ← X, an approximation to |A|, such as N / log N;
  - `nu` ← ν, a multiplicative density function of type `ArithmeticFunction ℝ`;
  - `weights` ← the constant 1 in the counting-sieve specialization;
  - `prodPrimes` ← the product of primes < z, below the sifting level;
  - `siftedSum` ← Mathlib's definition, summing weights over d coprime to prodPrimes.

Additional fields for the Jurkat-Richert setup:
  - `z`: the sifting level, removing multiples of primes < z;
  - `D`: the level of distribution, describing the range of controlled remainders;
  - `prodPrimes_eq`: prodPrimes is the product of primes < z.
The structure itself retains general weights; counting applications impose
`weights = 1` separately. -/
structure SieveProblem extends BoundingSieve where
  /-- Sifting level z: remove multiples of primes < z. -/
  z : ℝ
  hz_pos : 0 < z
  /-- Level of distribution D: the range of controlled remainders,
  supplied in applications by Bombieri-Vinogradov estimates. -/
  D : ℝ
  hD_pos : 0 < D
  /-- prodPrimes is the product of primes < z. -/
  prodPrimes_eq : prodPrimes = ((Finset.range ⌈z⌉₊).filter Nat.Prime).prod id

/-- **Bridge lemma**: Mathlib's `siftedSum` agrees with the sifted count.

Mathlib: `siftedSum = ∑ d ∈ support, if Coprime prodPrimes d then weights d else 0`
Counting formulation: `|{a ∈ A : ∀ p prime, p < z → ¬ p ∣ a}|`

The two coincide when `prodPrimes` is the product of primes < z and
`weights = 1`, as assumed by `hweights`. -/
theorem siftedSum_eq_filter (SP : SieveProblem) (hweights : ∀ n, SP.weights n = 1) :
    SP.siftedSum =
      (SP.support.filter (fun a => ∀ p : ℕ, p.Prime → (p : ℝ) < SP.z → ¬ p ∣ a)).sum (fun _ => (1 : ℝ)) := by
  -- The primeFactors of a product of distinct primes is exactly that set of primes.
  have h_pf : ∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime) → (S.prod id).primeFactors = S := by
    intro S hS
    induction S using Finset.induction_on with
    | empty => simp [Nat.primeFactors_one]
    | insert p S hp ih =>
      rw [Finset.prod_insert hp]
      -- id p is definitionally p by beta reduction; use show to align the target.
      show (p * S.prod id).primeFactors = insert p S
      have hp' := hS p (Finset.mem_insert_self _ _)
      have h0p : p ≠ 0 := hp'.ne_zero
      have h0s : (S.prod id) ≠ 0 := ne_of_gt <| Finset.prod_pos fun q hq =>
        Nat.Prime.pos (hS q (Finset.mem_insert_of_mem hq))
      rw [Nat.primeFactors_mul h0p h0s, Nat.Prime.primeFactors hp',
          ih fun q hq => hS q (Finset.mem_insert_of_mem hq)]
      rfl
  -- By prodPrimes_eq, its prime-factor set is exactly (range ⌈z⌉₊).filter Prime.
  have h_ppf : SP.prodPrimes.primeFactors = (Finset.range ⌈SP.z⌉₊).filter Nat.Prime := by
    rw [SP.prodPrimes_eq, h_pf]
    intro p hp; simp at hp; exact hp.2
  -- Key equivalence for prime p: p ∣ prodPrimes ↔ (p : ℝ) < z.
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
  -- Main equivalence: Nat.gcd prodPrimes a = 1 ↔ ∀ p prime, (p:ℝ) < z ⇒ ¬ p ∣ a.
  --   (⇒) If p ∣ prodPrimes (hence (p:ℝ) < z) and p ∣ a, then p ∣ gcd = 1,
  --       contradicting the primality of p.
  --   (⇐) By Nat.eq_one_iff_not_exists_prime_dvd, gcd ≠ 1 gives a prime p ∣ gcd.
  --       Then p ∣ prodPrimes (hence (p:ℝ) < z) and p ∣ a, contradicting the hypothesis.
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
  -- Unfold siftedSum using siftedSum_eq_sum_support_mul_ite and substitute weights = 1.
  -- Convert ite to a filter via Finset.sum_filter, then simplify its predicate with hkey.
  rw [SP.siftedSum_eq_sum_support_mul_ite]
  simp_rw [hweights, one_mul]
  rw [← Finset.sum_filter]
  exact Finset.sum_congr (Finset.filter_congr fun d _ => hkey d) (fun _ _ => rfl)

/-- **Sieve product V(z)** = Π_{p < z} (1 - ν(p)).

This is a factor in the Jurkat-Richert main term X · V(z) · f(s).

Relation to Mathlib's `selbergTerms`:
  `selbergTerms d = ν(d) · Π_{p|d} (1 - ν(p))⁻¹`.
  For d = prodPrimes, the product of primes < z:
    selbergTerms prodPrimes = ν(prodPrimes) / V(z)
  and hence V(z) = ν(prodPrimes) / selbergTerms(prodPrimes).

Mathlib's density corresponds to `ν(p) = ω(p)/p` in classical notation,
so `1 - ν(p) = 1 - ω(p)/p` is the standard sieve-density factor. -/
noncomputable def sieveProduct (SP : SieveProblem) : ℝ :=
  ((Finset.range ⌈SP.z⌉₊).filter Nat.Prime).prod
    (fun p => 1 - SP.nu p)

/-- **Bridge lemma 1**: sieveProduct equals Π_{p | prodPrimes} (1 - ν(p)).

By `prodPrimes_eq`, prodPrimes is the product of primes < z.
Thus, for a prime p, p | prodPrimes if and only if p < z. -/
theorem sieveProduct_eq_prod_one_sub_nu (SP : SieveProblem) :
    sieveProduct SP =
      ∏ p ∈ SP.prodPrimes.primeFactors, (1 - SP.nu p) := by
  -- The primeFactors of the product of a finite set of primes is that set.
  -- Apply Finset.induction_on to S.
  --   Base: S = ∅, ∏ id = 1, primeFactors 1 = ∅.
  --   Step: S = {p} ∪ S', ∏ id = p * (∏ S' id).
  --         primeFactors(p * prod) = {p} ∪ primeFactors(prod) = {p} ∪ S' = S ✓
  have h_pf : ∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime) → (S.prod id).primeFactors = S := by
    intro S hS
    induction S using Finset.induction_on with
    | empty => simp [Nat.primeFactors_one]
    | insert p S hp ih =>
      rw [Finset.prod_insert hp]
      show (p * S.prod id).primeFactors = insert p S
      have hp' := hS p (Finset.mem_insert_self _ _)
      have h0p : p ≠ 0 := hp'.ne_zero
      have h0s : (S.prod id) ≠ 0 := ne_of_gt <| Finset.prod_pos fun q hq =>
        Nat.Prime.pos (hS q (Finset.mem_insert_of_mem hq))
      rw [Nat.primeFactors_mul h0p h0s, Nat.Prime.primeFactors hp',
          ih fun q hq => hS q (Finset.mem_insert_of_mem hq)]
      rfl
  -- Apply this to obtain SP.prodPrimes.primeFactors = (range ⌈z⌉).filter Prime.
  have h_eq : SP.prodPrimes.primeFactors = (Finset.range ⌈SP.z⌉₊).filter Nat.Prime := by
    rw [SP.prodPrimes_eq, h_pf]
    intro p hp; simp at hp; exact hp.2
  rw [sieveProduct, h_eq]

/-- **Bridge lemma 2**: sieveProduct · selbergTerms(prodPrimes) = ν(prodPrimes).

By Mathlib's `selbergTerms_apply`:
  selbergTerms d = ν(d) · Π_{p|d} (1 - ν(p))⁻¹

For d = prodPrimes:
  selbergTerms prodPrimes = ν(prodPrimes) · Π_{p|prodPrimes} (1 - ν(p))⁻¹
                         = ν(prodPrimes) / sieveProduct

Hence sieveProduct · selbergTerms(prodPrimes) = ν(prodPrimes). -/
theorem sieveProduct_mul_selbergTerms_eq_nu (SP : SieveProblem) :
    sieveProduct SP * SP.selbergTerms SP.prodPrimes = SP.nu SP.prodPrimes := by
  -- By selbergTerms_apply: selbergTerms d = nu d * ∏_{p|d} (1 - nu p)⁻¹.
  -- By sieveProduct_eq_prod_one_sub_nu: sieveProduct = ∏_{p|d} (1 - nu p).
  -- Thus sieveProduct * selbergTerms = ∏(1-nu p) * nu(PP) * ∏(1-nu p)⁻¹
  --                                = nu(PP) * (∏(1-nu p) * ∏(1-nu p)⁻¹) = nu(PP)
  rw [SP.selbergTerms_apply, sieveProduct_eq_prod_one_sub_nu]
  -- Goal: (∏(1-nu p)) * (nu(PP) * ∏(1-nu p)⁻¹) = nu(PP)
  -- Each (1 - nu p) ≠ 0, since nu_lt_one_of_prime gives nu p < 1.
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
  rw [← mul_assoc, mul_comm _ (SP.nu SP.prodPrimes), mul_assoc]
  -- Align bound variables to remove the alpha-renaming discrepancy.
  show SP.nu SP.prodPrimes *
      ((∏ p ∈ SP.prodPrimes.primeFactors, (1 - SP.nu p)) *
        (∏ p ∈ SP.prodPrimes.primeFactors, (1 - SP.nu p))⁻¹) =
    SP.nu SP.prodPrimes
  -- Prove A * A⁻¹ = 1 first, then rewrite to avoid a Finset.prod matching failure.
  have h_inv : (∏ p ∈ SP.prodPrimes.primeFactors, (1 - SP.nu p)) *
               (∏ p ∈ SP.prodPrimes.primeFactors, (1 - SP.nu p))⁻¹ = 1 :=
    mul_inv_cancel₀ h_A_ne_zero
  rw [h_inv, mul_one]

/-- **Bridge corollary**: sieveProduct = ν(prodPrimes) / selbergTerms(prodPrimes). -/
theorem sieveProduct_eq_nu_div_selbergTerms (SP : SieveProblem) :
    sieveProduct SP = SP.nu SP.prodPrimes / SP.selbergTerms SP.prodPrimes := by
  -- By sieveProduct_mul_selbergTerms_eq_nu: sieveProduct * selbergTerms(PP) = nu(PP).
  -- Thus sieveProduct = nu(PP) / selbergTerms(PP), since selbergTerms(PP) > 0.
  have h := sieveProduct_mul_selbergTerms_eq_nu SP
  -- h : sieveProduct * selbergTerms(PP) = nu(PP)
  have h_st_pos : 0 < SP.selbergTerms SP.prodPrimes :=
    SP.selbergTerms_pos (dvd_refl SP.prodPrimes)
  -- eq_div_iff: a = c / b ↔ a * b = c when b ≠ 0.
  rw [eq_div_iff h_st_pos.ne']
  exact h

/-- **Distribution identity**: for d ≤ D, the counting specialization reads
|{a ∈ A : d | a}| = ν(d) · X + R_d.

This is Mathlib's `BoundingSieve.multSum_eq_main_err`:
  `multSum d = nu d * totalMass + rem d`

Here `rem d` is the remainder R_d. In applications, the level of distribution D
specifies the range of d on which |rem d| is negligible; this identity alone
does not bound the remainder. -/
theorem distribution_condition (SP : SieveProblem) (d : ℕ) (hd : (d : ℝ) ≤ SP.D) (hd_pos : 1 ≤ d) :
    SP.multSum d = SP.nu d * SP.totalMass + SP.rem d := by
  exact SP.multSum_eq_main_err d

/-! ## 5. Jurkat-Richert-shaped interfaces and Mathlib's sieve upper bound -/

/-- **Pointwise interface motivated by the Jurkat-Richert upper bound**:

  S(A, z) ≤ X · V(z) · (F(s) + O(η)) + Σ_{d ≤ D} |R_d|

Relation to Mathlib's `siftedSum_le_mainSum_errSum_of_upperMoebius`:
  Mathlib proves siftedSum ≤ totalMass · mainSum(μ⁺) + errSum(μ⁺).
  The uniform Jurkat-Richert analysis additionally controls
  mainSum(μ⁺) by V(z) · F(s), and errSum by Σ |R_d|.

This is part of the theory behind upper sieve estimates for Ω in Chen's theorem.

This interface only asks for an uncontrolled additive remainder for a single
`SP`, so the absolute difference of the two sides proves it directly.
It is not the uniform Jurkat-Richert estimate: that would additionally require
an explicit relation between `C_error` and bounds on `SP.rem`, as well as
the classical logarithmic sieve ratio rather than the quotient used here. -/
theorem jurkat_richert_upper_bound (SP : SieveProblem)
    (_hs : 2 ≤ SP.D / SP.z) :
    ∃ C_error : ℝ,
      SP.siftedSum ≤
        SP.totalMass * sieveProduct SP * (sieveFunctionF (SP.D / SP.z)) + C_error := by
  -- The uniform analytic strategy, beyond the pointwise proof below, is:
  -- 1. Apply siftedSum_le_mainSum_errSum_of_upperMoebius:
  --    siftedSum ≤ totalMass * mainSum(μ⁺) + errSum(μ⁺)
  -- 2. Jurkat-Richert: mainSum(μ⁺) ≤ V(z) * F(s) (upper sieve-function estimate).
  -- 3. Bound the remainder: errSum(μ⁺) ≤ Σ_{d≤D} |R_d|.
  -- 4. Combine: siftedSum ≤ X * V(z) * F(s) + Σ |R_d|.
  refine ⟨|SP.siftedSum - SP.totalMass * sieveProduct SP *
    sieveFunctionF (SP.D / SP.z)|, ?_⟩
  have h := le_abs_self (SP.siftedSum - SP.totalMass * sieveProduct SP *
    sieveFunctionF (SP.D / SP.z))
  linarith

/-- **Pointwise interface motivated by the Jurkat-Richert lower bound**:

  S(A, z) ≥ X · V(z) · (f(s) - O(η)) - Σ_{d ≤ D} |R_d|

The classical estimate underlies the lower bound on W(N) in Chen's theorem:
  W(N) ≥ 2.6408 𝔖(N) N/log²N

As above, these quantifiers express only the existence of an additive
remainder for each individual `SP`; they do not establish a uniform
Jurkat-Richert lower bound. -/
theorem jurkat_richert_lower_bound (SP : SieveProblem)
    (_hs : 3 < SP.D / SP.z) :
    ∃ C_error : ℝ,
      SP.siftedSum ≥
        SP.totalMass * sieveProduct SP * (sieveFunctionf (SP.D / SP.z)) - C_error := by
  -- A genuine lower sieve uses a lower Möbius condition, developed earlier in this module
  -- as the dual of Mathlib's upper condition; see Halberstam-Richert Ch. 8.
  refine ⟨|SP.totalMass * sieveProduct SP * sieveFunctionf (SP.D / SP.z) -
    SP.siftedSum|, ?_⟩
  have h := le_abs_self (SP.totalMass * sieveProduct SP *
    sieveFunctionf (SP.D / SP.z) - SP.siftedSum)
  linarith

/-! ## 6. Application to Chen's theorem -/

/-
In the classical Chen argument, the Jurkat-Richert lower bound is applied to:
  - A = {N - p : p prime, N^(1/10) < p < N}, a Goldbach-type set;
  - X ≈ N / log N, an approximation to the number of primes;
  - ν(d) = Π_{p|d} (p-1)⁻¹, the Goldbach density on squarefree sifting divisors;
  - z = N^(1/10), the sifting level;
  - D = N^(1/2 - ε), the level of distribution from Bombieri-Vinogradov;
  - s = log(D)/log(z) ≈ 5, the logarithmic sieve ratio.

The intended estimate is W(N) ≥ 2.6408 𝔖(N) N/log²N, with
V(z) ≈ 𝔖(N) / log N describing the sieve product's relation to the singular series.
The local surrogate has f(5) = 2e^γ · log(5/2) / 5. As explained above, it is
not the canonical lower sieve function and does not justify this classical
numerical constant.
-/

/-! ## 6.5 Scope of Chen's key inequality

The definitions of W(N) and Ω(N), and their conditional key inequality, are
in `SwitchingPrinciple.lean` (`chenW`, `chenOmega`, `chen_key_inequality`).
The inequality requires explicit uniform analytic bounds; the pointwise
remainder interfaces here do not supply them. In particular, replacing both
counts by zero would make the required assertion 0 - 0/2 > 0 false.
The historical counting bridge for the current definitions also has the
limitation recorded below. -/

/-! ## 7. Mathematical scope and dependencies -/

/-
**Sieve interfaces and their mathematical scope**:

1. **Singular series** (see `SingularSeries.lean`):
   - Local factors, truncated products, and positivity
   - Elementary upper and lower bounds, without Mertens' theorem or the PNT

2. **Linear-sieve / Jurkat-Richert interfaces**:
   - Finite lower-Möbius and generic Rosser density results in the first part
   - Local surrogate definitions of F(s) and f(s)
   - `SieveProblem`, extending Mathlib's `BoundingSieve`
   - Fixed-parameter remainder bounds, not the classical uniform theorem
   - Definitions of W(N) and Ω in `SwitchingPrinciple.lean`

3. **Mathlib correspondences**:
   - `SieveProblem` extends `BoundingSieve`
   - `sieveProduct_eq_prod_one_sub_nu`: V(z) = Π_{p|P} (1-ν(p))
   - `sieveProduct_mul_selbergTerms_eq_nu`: V(z)·g(P) = ν(P)
   - `sieveProduct_eq_nu_div_selbergTerms`: V(z) = ν(P)/g(P)
   - `siftedSum_eq_filter`: Mathlib's `siftedSum` equals the sifted count for unit weights
   - `distribution_condition`: directly inherited from `multSum_eq_main_err`

4. **Dependencies of the Chen endpoints**:
   chens_theorem_of_jurkat_richert_weighted_lower_bound
   ├── ChenJurkatRichertWeightedLowerBound
   │   (the candidate count minus half the prime-power penalty)
   └── LiuPanWangDingTheorem
       (the canonical upper bound for the corrected triple penalty)

   Stronger diagnostic hypothesis:
   chens_theorem_of_good_representation_lower_bound
   └── ChenGoodRepresentationLowerBound
       (a direct external lower bound on the public good-representation count)

   Historical compatibility interface:
   chens_theorem (ChenAnalyticBounds, ChenCountingBridge)
   ├── key_inequality_implies_chen (proved as an implication)
   │   ├── ChenCountingBridge (externally refuted by finite computation for the current definitions)
   │   └── chen_key_inequality (W(N) - Ω/2 > 0, conditional on the analytic bounds)
   │       └── ChenAnalyticBounds (explicit external uniform Jurkat-Richert / Selberg estimates)
   └── Pointwise remainder interfaces and bridges to Mathlib's sieve results

5. **Analytic requirements distinct from these interfaces**:
   - A uniform optimized Selberg upper bound, not just an arbitrary additive remainder
   - Distribution estimates, including Bombieri-Vinogradov and large-sieve input,
     with constants and hypotheses sufficient for the exact W(N) and Ω(N) definitions
-/


end MathlibNt.SieveTheory.LinearSieve
