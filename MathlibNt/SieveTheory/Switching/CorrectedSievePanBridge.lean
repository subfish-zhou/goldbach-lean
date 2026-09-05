import MathlibNt.SieveTheory.Switching.Weights

/-!
# The corrected sieve and the Pan counting bridge

Corrected candidate carriers, Selberg main terms, forbidden-prime products, and
Möbius/CRT identities connect finite arithmetic-progression counts to the weighted
Pan remainder. Support and truncation hypotheses remain explicit.

All declarations retain the `MathlibNt.SieveTheory.SwitchingPrinciple` namespace.
-/

open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta

set_option maxHeartbeats 6000000

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open Real Finset
open MeasureTheory intervalIntegral

open scoped Classical
open scoped Asymptotics

namespace Internal
end Internal

open Internal

/-- Corrected upper switching cutoff.  Using a ceiling makes the intended
cube-scale coverage an explicit parameter condition rather than a rounding
accident. -/
noncomputable def correctedChenY (N : ℕ) : ℕ :=
  Nat.ceil ((N : ℝ) ^ (1 / 3 : ℝ))

/-- The base candidates for a replacement switching argument.  Unlike the
historical W-candidates, the unit fibre is excluded at the definition level.
The future analytic lower bound must be proved anew for this object. -/
noncomputable def correctedChenCandidates (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun p =>
    p.Prime ∧ 2 ≤ N - p ∧
      ∀ r : ℕ, r.Prime → r < correctedChenZ N → ¬ r ∣ N - p)

/-- Complements used before the corrected sieve removes small primes not
already forced away by parity or by a prime factor of `N`. -/
noncomputable def correctedChenUnsiftedComplements (N : ℕ) : Finset ℕ :=
  ((Finset.range N).filter (fun p =>
    p.Prime ∧ 2 ≤ N - p ∧
      ∀ r : ℕ, r.Prime → r < correctedChenZ N →
        (r ≤ 2 ∨ r ∣ N) → ¬ r ∣ N - p)).image (fun p => N - p)

/-- Product of the small primes which remain to be sieved from the corrected
complement support. -/
noncomputable def correctedChenSiftingProduct (N : ℕ) : ℕ :=
  ((Finset.range (correctedChenZ N)).filter
    (fun r => r.Prime ∧ 2 < r ∧ ¬ r ∣ N)).prod id

/-- The corrected sifting product is squarefree because its factors are
distinct primes. -/
theorem correctedChenSiftingProduct_squarefree (N : ℕ) :
    Squarefree (correctedChenSiftingProduct N) := by
  unfold correctedChenSiftingProduct
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · rintro p hp q hq hpq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hp hq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes hp.2.1 hq.2.1).mpr hpq)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    exact hp.2.1.squarefree

/-- Goldbach local density for the corrected sieve: the reusable AnalyticNumberTheory density
`ν(d) = ∏_{p | d} 1/(p-1)` (`AnalyticNumberTheory.Sieve.goldbachNu`). -/
noncomputable abbrev correctedChenNu : ArithmeticFunction ℝ :=
  AnalyticNumberTheory.Sieve.goldbachNu

namespace Internal

/-- The prime factors of a product of distinct primes are exactly the set of
those primes. -/
theorem primeFactors_prod_eq_self {S : Finset ℕ}
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

end Internal

/-- The corrected sifting product is nonzero: it is a product of primes. -/
theorem correctedChenSiftingProduct_ne_zero (N : ℕ) :
    correctedChenSiftingProduct N ≠ 0 := by
  unfold correctedChenSiftingProduct
  exact ne_of_gt (Finset.prod_pos (by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    exact hr.2.1.pos))

/-- The prime divisors of the corrected sifting product are exactly its
factor primes: `2 < r < z` with `r ∤ N`. -/
theorem correctedChenSiftingProduct_primeFactors (N : ℕ) :
    (correctedChenSiftingProduct N).primeFactors =
      ((Finset.range (correctedChenZ N)).filter
        (fun r => r.Prime ∧ 2 < r ∧ ¬ r ∣ N)) := by
  unfold correctedChenSiftingProduct
  exact primeFactors_prod_eq_self (by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    exact hp.2.1)

/-- A prime divides the corrected sifting product exactly when it is one of
the sieved primes: `2 < p < z` and `p ∤ N`. -/
theorem prime_dvd_correctedChenSiftingProduct {N p : ℕ} (hp : p.Prime) :
    p ∣ correctedChenSiftingProduct N ↔
      p < correctedChenZ N ∧ 2 < p ∧ ¬ p ∣ N := by
  constructor
  · intro hdvd
    have hmem : p ∈ (correctedChenSiftingProduct N).primeFactors :=
      (Nat.mem_primeFactors_of_ne_zero (correctedChenSiftingProduct_ne_zero N)).mpr
        ⟨hp, hdvd⟩
    rw [correctedChenSiftingProduct_primeFactors N] at hmem
    rcases Finset.mem_filter.mp hmem with ⟨hp_range, hcond⟩
    exact ⟨by simpa using hp_range, hcond.2.1, hcond.2.2⟩
  · intro hmem
    have hmem' : p ∈ (correctedChenSiftingProduct N).primeFactors := by
      rw [correctedChenSiftingProduct_primeFactors N]
      exact Finset.mem_filter.mpr ⟨by simpa using hmem.1, ⟨hp, hmem.2.1, hmem.2.2⟩⟩
    exact (Nat.mem_primeFactors_of_ne_zero (correctedChenSiftingProduct_ne_zero N)).mp hmem' |>.2

/-- The corrected Chen sieve as a mathlib `BoundingSieve` record: the
unsifted complements as support, the surviving small-prime product as
`prodPrimes`, unit weights, and the Goldbach local density
`ν(p) = 1/(p-1)`.

The total mass is the analytic main term `N / log N`.  With the density
identification `ν(d) = 1/φ(d)` for squarefree `d`, the remainder
`rem d = multSum d − ν(d)·N/log N` is exactly the congruence-count error that
the averaged Pan-type distribution condition (`CorrectedChenDistributionCondition`)
controls; the difference between `N/log N` and the true support cardinality is
absorbed by the main-term constants of the analytic workline, not by the
`errSum`. -/
noncomputable def correctedChenBoundingSieve (N : ℕ) : BoundingSieve where
  support := correctedChenUnsiftedComplements N
  prodPrimes := correctedChenSiftingProduct N
  prodPrimes_squarefree := correctedChenSiftingProduct_squarefree N
  weights := fun _ => 1
  weights_nonneg := by intro n; norm_num
  totalMass := (N : ℝ) / log (N : ℝ)
  nu := correctedChenNu
  nu_mult := AnalyticNumberTheory.Sieve.goldbachNu_isMultiplicative
  nu_pos_of_prime := by
    intro p hp hdiv
    exact AnalyticNumberTheory.Sieve.goldbachNu_pos_of_prime hp
  nu_lt_one_of_prime := by
    intro p hp hdiv
    have hpcond := (prime_dvd_correctedChenSiftingProduct hp).mp hdiv
    exact AnalyticNumberTheory.Sieve.goldbachNu_lt_one_of_prime hp hpcond.2.1

/-- The corrected sieve total mass is the analytic main term `N / log N`. -/
theorem correctedChenTotalMass_eq (N : ℕ) :
    (correctedChenBoundingSieve N).totalMass = (N : ℝ) / log (N : ℝ) := rfl

/-! ## Optimal Selberg upper bound and the main-term identities -/

/-- Apply `AnalyticNumberTheory.Sieve.selberg_upper_bound_optimal`:
the sifted sum of the corrected sieve is bounded by `totalMass·(Σ selbergTerms)⁻¹ + errSum(Λ²w*)`.
This is an unconditional instance of the classical Selberg upper-bound sieve
`S ≤ X/G(z) + R` for `correctedChenBoundingSieve`. -/
theorem correctedChenSelbergUpperBound (N : ℕ) :
    ∃ w : ℕ → ℝ, w 1 = 1 ∧
      (correctedChenBoundingSieve N).siftedSum ≤
        (correctedChenBoundingSieve N).totalMass *
          (∑ l ∈ (correctedChenBoundingSieve N).prodPrimes.divisors,
            (correctedChenBoundingSieve N).selbergTerms l)⁻¹ +
        (correctedChenBoundingSieve N).errSum (BoundingSieve.lambdaSquared w) :=
  AnalyticNumberTheory.Sieve.selberg_upper_bound_optimal (correctedChenBoundingSieve N)

/-- Apply `selbergMainTerm_eq_prod_one_sub_nu`: the Selberg main term equals the sieve product
`∏_{p | P(N)} (1 − ν(p))`. -/
theorem correctedChenSelbergMainTerm_eq_prod (N : ℕ) :
    (∑ l ∈ (correctedChenBoundingSieve N).prodPrimes.divisors,
      (correctedChenBoundingSieve N).selbergTerms l)⁻¹ =
    ∏ p ∈ (correctedChenBoundingSieve N).prodPrimes.primeFactors,
      (1 - correctedChenNu p) :=
  AnalyticNumberTheory.Sieve.selbergMainTerm_eq_prod_one_sub_nu (correctedChenBoundingSieve N)

/-- The main-term sieve product equals `MertensTheorem.goldbachSieveProduct N z`.
For even N, the factor at p = 2 is excluded on both sides by `p ∤ N`. -/
theorem correctedChenSelbergMainTerm_eq_goldbachSieveProduct (N : ℕ) (hN : Even N) :
    (∑ l ∈ (correctedChenBoundingSieve N).prodPrimes.divisors,
      (correctedChenBoundingSieve N).selbergTerms l)⁻¹ =
    MertensTheorem.goldbachSieveProduct N (correctedChenZ N) := by
  rw [correctedChenSelbergMainTerm_eq_prod N]
  unfold MertensTheorem.goldbachSieveProduct
  change ∏ p ∈ (correctedChenSiftingProduct N).primeFactors, (1 - correctedChenNu p) =
    ∏ p ∈ (Finset.range (correctedChenZ N)).filter (fun p => p.Prime ∧ ¬ p ∣ N),
      (1 - 1 / ((p : ℝ) - 1))
  rw [correctedChenSiftingProduct_primeFactors N]
  have hset : ((Finset.range (correctedChenZ N)).filter (fun p => p.Prime ∧ ¬ p ∣ N)) =
      ((Finset.range (correctedChenZ N)).filter (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N)) := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hr, hc⟩
      have hpne2 : p ≠ 2 := by
        intro hp2
        have h2dvd : 2 ∣ N := by
          rcases hN with ⟨k, hk⟩
          refine ⟨k, ?_⟩
          rw [hk]
          ring
        exact hc.2 (by simpa [hp2] using h2dvd)
      refine Finset.mem_filter.mpr ⟨hr, ⟨hc.1, ?_⟩⟩
      rcases hc.1.eq_two_or_odd' with h | h
      · exact absurd h hpne2
      · have : 2 ≤ p := hc.1.two_le
        omega
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hr, hc⟩
      exact Finset.mem_filter.mpr ⟨hr, ⟨hc.1, hc.2.2⟩⟩
  rw [hset]
  apply Finset.prod_congr rfl
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨_, hc⟩
  have hp' : p.Prime := hc.1
  have hnu : correctedChenNu p = 1 / ((p : ℝ) - 1) := by
    unfold correctedChenNu
    exact AnalyticNumberTheory.Sieve.goldbachNu_apply_prime hp'
  rw [hnu]

/-- Main-term identity: `totalMass·(Σ selbergTerms)⁻¹ =
(N/log N)·primeProduct(z−1)·𝔖_trunc(N, z−1)`, the exact application
of `sieveProduct_identity` to the Selberg main term. -/
theorem correctedChenSelbergMainTerm_eq_primeProduct_mul_singularSeries (N : ℕ)
    (hN : Even N) :
    (correctedChenBoundingSieve N).totalMass *
      (∑ l ∈ (correctedChenBoundingSieve N).prodPrimes.divisors,
        (correctedChenBoundingSieve N).selbergTerms l)⁻¹ =
    ((N : ℝ) / log (N : ℝ)) * MertensTheorem.primeProduct (correctedChenZ N - 1) *
      SingularSeries.singularSeriesTruncated N (correctedChenZ N - 1) := by
  rw [correctedChenTotalMass_eq N,
    correctedChenSelbergMainTerm_eq_goldbachSieveProduct N hN]
  have hz2 : 2 ≤ correctedChenZ N := by
    unfold correctedChenZ
    exact le_max_left _ _
  rw [MertensTheorem.sieveProduct_identity N (correctedChenZ N) hz2 hN]
  ring

/-- An element is coprime to the corrected sifting product exactly when no
sieved prime (that is, no prime `2 < r < z` with `r ∤ N`) divides it. -/
theorem coprime_correctedChenSiftingProduct_iff {N a : ℕ} :
    Nat.Coprime (correctedChenSiftingProduct N) a ↔
      ∀ r : ℕ, r.Prime → r < correctedChenZ N → 2 < r → ¬ r ∣ N → ¬ r ∣ a := by
  constructor
  · intro hcop r hr hr_z hr_gt2 hr_ndvd hr_dvd
    have hr_dvd_P : r ∣ correctedChenSiftingProduct N :=
      (prime_dvd_correctedChenSiftingProduct hr).mpr ⟨hr_z, hr_gt2, hr_ndvd⟩
    exact Nat.not_coprime_of_dvd_of_dvd hr.one_lt hr_dvd_P hr_dvd hcop
  · intro hno
    apply Nat.coprime_of_dvd'
    intro r hr hr_dvd_P hr_dvd
    rcases (prime_dvd_correctedChenSiftingProduct hr).mp hr_dvd_P with ⟨hr_z, hr_gt2, hr_ndvd⟩
    exact False.elim (hno r hr hr_z hr_gt2 hr_ndvd hr_dvd)

/-- The small-prime sieve leaves exactly the corrected candidates: an
unsifted complement survives the sieve precisely when its prime partner lies
in the corrected candidate set. -/
theorem correctedChenSiftedComplements_eq_correctedCandidate_image (N : ℕ) :
    (correctedChenUnsiftedComplements N).filter
        (fun a => Nat.Coprime (correctedChenSiftingProduct N) a) =
      (correctedChenCandidates N).image (fun p => N - p) := by
  ext a
  constructor
  · intro ha
    rcases Finset.mem_filter.mp ha with ⟨ha_sup, hacop⟩
    rcases Finset.mem_image.mp ha_sup with ⟨p, hp_base, hpa⟩
    refine Finset.mem_image.mpr ⟨p, ?_, hpa⟩
    rcases Finset.mem_filter.mp hp_base with ⟨hp_range, hp_prime, hp_two, hp_small⟩
    refine Finset.mem_filter.mpr ⟨hp_range, ⟨hp_prime, hp_two, ?_⟩⟩
    intro r hr hr_z hr_dvd
    by_cases hr_le2 : r ≤ 2
    · exact False.elim (hp_small r hr hr_z (Or.inl hr_le2) hr_dvd)
    · by_cases hrN : r ∣ N
      · exact False.elim (hp_small r hr hr_z (Or.inr hrN) hr_dvd)
      · have hr_gt2 : 2 < r := by omega
        have hnot : ¬ r ∣ a :=
          (coprime_correctedChenSiftingProduct_iff.mp hacop) r hr hr_z hr_gt2 hrN
        have hnot' : ¬ r ∣ N - p := by
          rw [hpa]
          exact hnot
        exact False.elim (hnot' hr_dvd)
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨p, hp_cand, hpa⟩
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [hpa.symm]
      rcases Finset.mem_filter.mp hp_cand with ⟨hp_range, hp_prime, hp_two, hstrong⟩
      refine Finset.mem_image.mpr ⟨p, ?_, rfl⟩
      refine Finset.mem_filter.mpr ⟨hp_range, ⟨hp_prime, hp_two, ?_⟩⟩
      intro r hr hr_z hcond
      exact hstrong r hr hr_z
    · rw [hpa.symm]
      apply coprime_correctedChenSiftingProduct_iff.mpr
      intro r hr hr_z hr_gt2 hrN hr_dvd
      rcases Finset.mem_filter.mp hp_cand with ⟨hp_range, hp_prime, hp_two, hstrong⟩
      exact hstrong r hr hr_z hr_dvd

/-- The number of unsifted complements that survive the corrected sieve is
exactly the number of corrected candidates. -/
theorem correctedChenSiftedCard_eq_correctedCandidateCard (N : ℕ) :
    ((correctedChenUnsiftedComplements N).filter
        (fun a => Nat.Coprime (correctedChenSiftingProduct N) a)).card =
      (correctedChenCandidates N).card := by
  rw [correctedChenSiftedComplements_eq_correctedCandidate_image]
  apply Finset.card_image_of_injOn
  intro p hp q hq hpq
  rcases Finset.mem_filter.mp hp with ⟨hp_range, _⟩
  rcases Finset.mem_filter.mp hq with ⟨hq_range, _⟩
  have hp_lt : p < N := by simpa using hp_range
  have hq_lt : q < N := by simpa using hq_range
  change N - p = N - q at hpq
  omega

/-- The `BoundingSieve` sifted sum for the corrected Chen sieve is exactly the
corrected candidate count. -/
theorem correctedChenBoundingSieve_siftedSum_eq_card (N : ℕ) :
    (correctedChenBoundingSieve N).siftedSum = (correctedChenCandidates N).card := by
  change (∑ d ∈ correctedChenUnsiftedComplements N,
      if Nat.Coprime (correctedChenSiftingProduct N) d then (1 : ℝ) else 0) =
    ↑(correctedChenCandidates N).card
  rw [Finset.sum_boole]
  exact_mod_cast correctedChenSiftedCard_eq_correctedCandidateCard N

/-- The prime support of the unsifted complements: primes `p < N` whose
complement is at least two and carries no `r ≤ 2` or `r | N` prime divisor
below `z`.  It is the preimage of the sieve support under `p ↦ N - p`. -/
noncomputable def correctedChenUnsiftedPrimeSupport (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun p =>
    p.Prime ∧ 2 ≤ N - p ∧
      ∀ r : ℕ, r.Prime → r < correctedChenZ N →
        (r ≤ 2 ∨ r ∣ N) → ¬ r ∣ N - p)

/-- **Forbidden-prime product for the Pan bridge**: `F(N) = ∏_{r < z, r prime, r ≤ 2 ∨ r | N} r`.
The support condition `∀ r < z: (r ≤ 2 ∨ r | N) → ¬ r | N−p` is exactly
`(N−p, F(N)) = 1`. -/
noncomputable def correctedChenForbiddenProduct (N : ℕ) : ℕ :=
  ((Finset.range (correctedChenZ N)).filter
    (fun r => r.Prime ∧ (r ≤ 2 ∨ r ∣ N))).prod id

/-- The forbidden-prime product is squarefree, being a product of distinct primes. -/
theorem correctedChenForbiddenProduct_squarefree (N : ℕ) :
    Squarefree (correctedChenForbiddenProduct N) := by
  unfold correctedChenForbiddenProduct
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · rintro p hp q hq hpq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hp hq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes hp.2.1 hq.2.1).mpr hpq)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    exact hp.2.1.squarefree

/-- The forbidden-prime product is nonzero. -/
theorem correctedChenForbiddenProduct_ne_zero (N : ℕ) :
    correctedChenForbiddenProduct N ≠ 0 := by
  exact (Squarefree.ne_zero (correctedChenForbiddenProduct_squarefree N))

/-- Its set of prime factors is exactly the filtered set of primes. -/
theorem correctedChenForbiddenProduct_primeFactors (N : ℕ) :
    (correctedChenForbiddenProduct N).primeFactors =
      (Finset.range (correctedChenZ N)).filter (fun r => r.Prime ∧ (r ≤ 2 ∨ r ∣ N)) := by
  unfold correctedChenForbiddenProduct
  exact primeFactors_prod_eq_self (by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    exact hp.2.1)

/-- Characterization of `r | F(N)`: `r` is prime, `r < z`, and `(r ≤ 2 ∨ r | N)`. -/
theorem prime_dvd_correctedChenForbiddenProduct_iff {N r : ℕ} (hr : r.Prime) :
    r ∣ correctedChenForbiddenProduct N ↔
      r < correctedChenZ N ∧ (r ≤ 2 ∨ r ∣ N) := by
  constructor
  · intro hdvd
    have hmem : r ∈ (correctedChenForbiddenProduct N).primeFactors :=
      (Nat.mem_primeFactors_of_ne_zero (correctedChenForbiddenProduct_ne_zero N)).mpr
        ⟨hr, hdvd⟩
    rw [correctedChenForbiddenProduct_primeFactors N] at hmem
    rcases Finset.mem_filter.mp hmem with ⟨hrange, hcond⟩
    exact ⟨by simpa using hrange, hcond.2⟩
  · intro hmem
    have hmem' : r ∈ (correctedChenForbiddenProduct N).primeFactors := by
      rw [correctedChenForbiddenProduct_primeFactors N]
      exact Finset.mem_filter.mpr ⟨by simpa using hmem.1, ⟨hr, hmem.2⟩⟩
    exact (Nat.mem_primeFactors_of_ne_zero (correctedChenForbiddenProduct_ne_zero N)).mp hmem' |>.2

/-- **Coprimality characterization of support for the Pan bridge**: `p ∈ support ⟺ p.Prime ∧ 2 ≤ N−p ∧
∀ prime r | F(N): ¬ r | N−p`. -/
theorem mem_correctedChenUnsiftedPrimeSupport_iff_coprime (N p : ℕ) :
    p ∈ correctedChenUnsiftedPrimeSupport N ↔
      p.Prime ∧ 2 ≤ N - p ∧
        ∀ r : ℕ, r.Prime → r ∣ correctedChenForbiddenProduct N → ¬ r ∣ N - p := by
  unfold correctedChenUnsiftedPrimeSupport
  rw [Finset.mem_filter]
  constructor
  · intro hp
    rcases hp with ⟨hp_range, hbase⟩
    exact ⟨hbase.1, ⟨hbase.2.1, by
      intro r hr hrF
      have hlt : r < correctedChenZ N := (prime_dvd_correctedChenForbiddenProduct_iff hr).mp hrF |>.1
      have hcond : r ≤ 2 ∨ r ∣ N := (prime_dvd_correctedChenForbiddenProduct_iff hr).mp hrF |>.2
      exact hbase.2.2 r hr hlt hcond⟩⟩
  · intro hp
    rcases hp with ⟨hpp, h2, hcop⟩
    exact ⟨(by simpa using (show p < N by omega)), ⟨hpp, ⟨h2, by
      intro r hr hlt hcond
      have hrF : r ∣ correctedChenForbiddenProduct N :=
        (prime_dvd_correctedChenForbiddenProduct_iff hr).mpr ⟨hlt, hcond⟩
      exact hcop r hr hrF⟩⟩⟩

/-- **Möbius coprimality indicator for the Pan bridge**: `Σ_{e | F(N), e | m} μ(e) =
1_{∀ prime r | F(N): ¬ r | m}`. -/
theorem moebius_coprime_sum_forbidden (N m : ℕ) :
    (∑ e ∈ (correctedChenForbiddenProduct N).divisors, if e ∣ m then (μ e : ℝ) else 0) =
      if ∀ r : ℕ, r.Prime → r ∣ correctedChenForbiddenProduct N → ¬ r ∣ m
        then (1 : ℝ) else 0 := by
  let F : ℕ := correctedChenForbiddenProduct N
  have hdiv : F.divisors.filter (fun e => e ∣ m) = (Nat.gcd m F).divisors := by
    ext e
    constructor
    · intro he
      rw [Finset.mem_filter] at he
      rw [Nat.mem_divisors] at he ⊢
      rcases he with ⟨heF, hem⟩
      rcases heF with ⟨hed, hF0⟩
      constructor
      · exact Nat.dvd_gcd_iff.mpr ⟨hem, hed⟩
      · have hFpos : 0 < F := Nat.pos_of_ne_zero hF0
        exact ne_of_gt (Nat.gcd_pos_of_pos_right m hFpos)
    · intro he
      rw [Nat.mem_divisors] at he
      rw [Finset.mem_filter] at ⊢
      rw [Nat.mem_divisors] at ⊢
      rcases he with ⟨hg, hg0⟩
      rcases (Nat.dvd_gcd_iff.mp hg) with ⟨hem, hed⟩
      constructor
      · exact ⟨hed, correctedChenForbiddenProduct_ne_zero N⟩
      · exact hem
  have hsum : (∑ e ∈ F.divisors, if e ∣ m then (μ e : ℝ) else 0) =
      (∑ e ∈ (Nat.gcd m F).divisors, (μ e : ℝ)) := by
    rw [← Finset.sum_filter]
    rw [hdiv]
  have hsum' : (∑ e ∈ (Nat.gcd m F).divisors, (μ e : ℝ)) =
      if Nat.gcd m F = 1 then (1 : ℝ) else 0 := by
    have h := ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℝ)
    have hkey : (ζ * (μ : ArithmeticFunction ℝ)) (Nat.gcd m F) =
        (1 : ArithmeticFunction ℝ) (Nat.gcd m F) := by rw [h]
    rw [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.one_apply] at hkey
    simpa [ArithmeticFunction.intCoe_apply, mul_comm] using hkey
  have hgcd : (Nat.gcd m F = 1) ↔ ∀ r : ℕ, r.Prime → r ∣ F → ¬ r ∣ m := by
    constructor
    · intro hg r hr hrF hm
      have hrg : r ∣ Nat.gcd m F := Nat.dvd_gcd_iff.mpr ⟨hm, hrF⟩
      rw [hg] at hrg
      have hr1 : r ≤ 1 := Nat.le_of_dvd (by norm_num) hrg
      have hr2 : 2 ≤ r := hr.two_le
      omega
    · intro hcop
      by_contra hg
      have hgne : Nat.gcd m F ≠ 1 := by omega
      obtain ⟨r, hrp, hrd⟩ := Nat.exists_prime_and_dvd hgne
      have hrm : r ∣ m := (Nat.dvd_gcd_iff.mp hrd).1
      have hrF : r ∣ F := (Nat.dvd_gcd_iff.mp hrd).2
      exact hcop r hrp hrF hrm
  rw [hsum, hsum']
  by_cases hc : Nat.gcd m F = 1
  · rw [if_pos hc]
    rw [if_pos (hgcd.mp hc)]
  · rw [if_neg hc]
    rw [if_neg (mt hgcd.mpr hc)]

/-- **Möbius decomposition of the support AP count for the Pan bridge**: pointwise,
`1_{p ∈ support, p ≡ N mod d} = Σ_{e | F(N)} μ(e)·1_{base ∧ e | N−p}`. -/
private theorem support_AP_indicator_eq_moebiusSum (N p d : ℕ) (hp : p ∈ Finset.range N) :
    (if p ∈ correctedChenUnsiftedPrimeSupport N ∧ p ≡ N [MOD d] then (1 : ℝ) else 0) =
      ∑ e ∈ (correctedChenForbiddenProduct N).divisors,
        if p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD d] ∧ e ∣ N - p then (μ e : ℝ) else 0 := by
  have hcop := moebius_coprime_sum_forbidden N (N - p)
  by_cases hsupp : p ∈ correctedChenUnsiftedPrimeSupport N
  · have hbase : p.Prime ∧ 2 ≤ N - p :=
      ⟨(Finset.mem_filter.mp hsupp).2.1, (Finset.mem_filter.mp hsupp).2.2.1⟩
    by_cases hcong : p ≡ N [MOD d]
    · rw [if_pos ⟨hsupp, hcong⟩]
      have hcoprime : ∀ r : ℕ, r.Prime → r ∣ correctedChenForbiddenProduct N → ¬ r ∣ N - p := by
        rw [mem_correctedChenUnsiftedPrimeSupport_iff_coprime] at hsupp
        exact hsupp.2.2
      have hcop1 : (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
          if e ∣ N - p then (μ e : ℝ) else 0) = 1 := by
        rw [hcop]
        rw [if_pos hcoprime]
      calc
        (1 : ℝ) = ∑ e ∈ (correctedChenForbiddenProduct N).divisors,
            if e ∣ N - p then (μ e : ℝ) else 0 := hcop1.symm
        _ = ∑ e ∈ (correctedChenForbiddenProduct N).divisors,
            if p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD d] ∧ e ∣ N - p then (μ e : ℝ) else 0 := by
              apply Finset.sum_congr rfl
              intro e he
              rcases hbase with ⟨hpp, h2⟩
              by_cases hdvd : e ∣ N - p <;> simp [hpp, h2, hcong, hdvd]
    · rw [if_neg (by intro h; exact hcong h.2)]
      symm
      apply Finset.sum_eq_zero
      intro e he
      by_cases hdvd : e ∣ N - p
      · have hne : ¬ (p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD d] ∧ e ∣ N - p) := by
          intro h
          exact hcong h.2.2.1
        simp [hne]
      · simp [hdvd]
  · rw [if_neg (by intro h; exact hsupp h.1)]
    symm
    by_cases hbase : p.Prime ∧ 2 ≤ N - p
    · by_cases hcong : p ≡ N [MOD d]
      · have hcop0 : (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
            if e ∣ N - p then (μ e : ℝ) else 0) = 0 := by
          rw [hcop]
          rw [if_neg]
          intro hcoprime
          have hsupp' : p ∈ correctedChenUnsiftedPrimeSupport N := by
            rw [mem_correctedChenUnsiftedPrimeSupport_iff_coprime]
            exact ⟨hbase.1, hbase.2, hcoprime⟩
          exact hsupp hsupp'
        calc
          (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
              if p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD d] ∧ e ∣ N - p then (μ e : ℝ) else 0)
              = ∑ e ∈ (correctedChenForbiddenProduct N).divisors,
                  if e ∣ N - p then (μ e : ℝ) else 0 := by
                apply Finset.sum_congr rfl
                intro e he
                rcases hbase with ⟨hpp, h2⟩
                by_cases hdvd : e ∣ N - p <;> simp [hpp, h2, hcong, hdvd]
          _ = 0 := hcop0
      · apply Finset.sum_eq_zero
        intro e he
        by_cases hdvd : e ∣ N - p
        · have hne : ¬ (p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD d] ∧ e ∣ N - p) := by
            intro h
            exact hcong h.2.2.1
          simp [hne]
        · simp [hdvd]
    · apply Finset.sum_eq_zero
      intro e he
      by_cases hdvd : e ∣ N - p
      · have hne : ¬ (p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD d] ∧ e ∣ N - p) := by
          intro h
          exact hbase ⟨h.1, h.2.1⟩
        simp [hne]
      · simp [hdvd]

/-- **Möbius decomposition of the support AP count for the Pan bridge**: the inner count
in Chen's distribution condition expands as a Möbius-weighted sum of prime-AP base counts over
forbidden-prime divisors. Each base count is then linked to `primesInAPBelow`/`panDistributionError`. -/
theorem unsiftedPrimeSupport_AP_count_eq_moebiusSum (N d : ℕ) :
    (((correctedChenUnsiftedPrimeSupport N).filter (fun p => p ≡ N [MOD d])).card : ℝ) =
      ∑ e ∈ (correctedChenForbiddenProduct N).divisors,
        (μ e : ℝ) * (((Finset.range N).filter (fun p =>
          p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD d] ∧ e ∣ N - p)).card : ℝ) := by
  calc
    (((correctedChenUnsiftedPrimeSupport N).filter (fun p => p ≡ N [MOD d])).card : ℝ)
        = ∑ p ∈ (Finset.range N),
            if p ∈ correctedChenUnsiftedPrimeSupport N ∧ p ≡ N [MOD d] then (1 : ℝ) else 0 := by
          have h₁ : (((correctedChenUnsiftedPrimeSupport N).filter (fun p => p ≡ N [MOD d])).card : ℝ) =
              ∑ p ∈ correctedChenUnsiftedPrimeSupport N, if p ≡ N [MOD d] then (1 : ℝ) else 0 := by
            rw [Finset.sum_boole]
          rw [h₁]
          have hsub : correctedChenUnsiftedPrimeSupport N ⊆ Finset.range N := by
            intro p hp
            exact (Finset.mem_filter.mp hp).1
          have hz : ∀ p ∈ Finset.range N, p ∉ correctedChenUnsiftedPrimeSupport N →
              (if p ∈ correctedChenUnsiftedPrimeSupport N ∧ p ≡ N [MOD d] then (1 : ℝ) else 0) = 0 := by
            intro p hp hnot
            simp [hnot]
          rw [← Finset.sum_subset hsub hz]
          apply Finset.sum_congr rfl
          intro p hp
          simp [hp]
    _ = ∑ p ∈ (Finset.range N),
          (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
            if p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD d] ∧ e ∣ N - p then (μ e : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact support_AP_indicator_eq_moebiusSum N p d hp
    _ = ∑ e ∈ (correctedChenForbiddenProduct N).divisors,
          (μ e : ℝ) * (((Finset.range N).filter (fun p =>
            p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD d] ∧ e ∣ N - p)).card : ℝ) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro e he
          calc
            (∑ p ∈ (Finset.range N),
                if p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD d] ∧ e ∣ N - p then (μ e : ℝ) else 0)
                = ∑ p ∈ (Finset.range N),
                    (μ e : ℝ) * (if p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD d] ∧ e ∣ N - p
                      then (1 : ℝ) else 0) := by
                  apply Finset.sum_congr rfl
                  intro p hp
                  by_cases h : p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD d] ∧ e ∣ N - p
                  · simp [h]
                  · simp [h]
            _ = (μ e : ℝ) * (∑ p ∈ (Finset.range N),
                    if p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD d] ∧ e ∣ N - p then (1 : ℝ) else 0) := by
                  rw [← Finset.mul_sum]
            _ = (μ e : ℝ) * (((Finset.range N).filter (fun p =>
                    p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD d] ∧ e ∣ N - p)).card : ℝ) := by
                  rw [Finset.sum_boole]

/-! ## The Pan bridge: lcm merging and compatibility of congruences -/

/-- Merging congruences (the compatible CRT case): for `p < N`,
`p ≡ N [MOD d]` and `e ∣ N-p` hold exactly when `p ≡ N [MOD lcm d e]`. This justifies
replacing the inner condition of `unsiftedPrimeSupport_AP_count_eq_moebiusSum`,
`p ≡ N [MOD d] ∧ e | N-p`, by the single modulus `lcm(d,e)`:
`e | N-p` is equivalent to `p ≡ N [MOD e]` by `prime_dvd_complement_iff_modEq`.
The congruences have the same residue `N`, so they are automatically compatible; coprimality of `d,e` is unnecessary. -/
theorem modEq_and_dvd_complement_iff_modEq_lcm {N p d e : ℕ} (hp : p < N) :
    (p ≡ N [MOD d] ∧ e ∣ N - p) ↔ p ≡ N [MOD Nat.lcm d e] := by
  rw [AnalyticNumberTheory.Sieve.prime_dvd_complement_iff_modEq (N := N) (p := p) (d := e) hp]
  constructor
  · intro h
    exact Nat.mod_lcm h.1 h.2
  · intro h
    constructor
    · exact h.of_dvd (Nat.dvd_lcm_left d e)
    · exact h.of_dvd (Nat.dvd_lcm_right d e)

/-- Counting form of lcm merging: the inner count in the Möbius decomposition,
`#{p < N : p ≡ N [MOD d] ∧ e | N-p}`, becomes `#{p < N : p ≡ N [MOD lcm(d,e)]}`. -/
theorem unsiftedPrimeSupport_AP_count_lcm_merge (N d e : ℕ) :
    ((Finset.range N).filter (fun p =>
      p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD d] ∧ e ∣ N - p)).card =
    ((Finset.range N).filter (fun p =>
      p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card := by
  apply congrArg Finset.card
  ext p
  rw [Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨hp, h⟩
    rcases h with ⟨hpp, htwo, hcong, hdvd⟩
    exact ⟨hp, hpp, htwo,
      (modEq_and_dvd_complement_iff_modEq_lcm (d := d) (e := e) (Finset.mem_range.mp hp)).mp
        ⟨hcong, hdvd⟩⟩
  · rintro ⟨hp, h⟩
    rcases h with ⟨hpp, htwo, hcong⟩
    rcases (modEq_and_dvd_complement_iff_modEq_lcm (d := d) (e := e) (Finset.mem_range.mp hp)).mpr
        hcong with ⟨hcongd, hdvde⟩
    exact ⟨hp, hpp, htwo, hcongd, hdvde⟩

/-- **lcm form of the Möbius decomposition**: as in `unsiftedPrimeSupport_AP_count_eq_moebiusSum`,
but with each inner base count merged using `lcm(d,e)`. The count
`#{p < N : p ≡ N [MOD lcm(d,e)]}` is exactly the input to the a=1 Pan distribution error
via `primesInAPBelow_one`/`panDistributionError_one`. -/
theorem unsiftedPrimeSupport_AP_count_eq_moebiusSum_lcm (N d : ℕ) :
    (((correctedChenUnsiftedPrimeSupport N).filter (fun p => p ≡ N [MOD d])).card : ℝ) =
      ∑ e ∈ (correctedChenForbiddenProduct N).divisors,
        (μ e : ℝ) * (((Finset.range N).filter (fun p =>
          p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ) := by
  rw [unsiftedPrimeSupport_AP_count_eq_moebiusSum N d]
  apply Finset.sum_congr rfl
  intro e he
  congr 1
  exact_mod_cast (unsiftedPrimeSupport_AP_count_lcm_merge N d e)

/-- The unsifted complement support is definitionally the image of the prime
support under `p ↦ N - p`. -/
theorem correctedChenUnsiftedComplements_eq_image (N : ℕ) :
    correctedChenUnsiftedComplements N =
      (correctedChenUnsiftedPrimeSupport N).image (fun p => N - p) := by
  rfl

/-- The corrected sieve `multSum` is the number of support elements divisible
by `d`. -/
theorem correctedChenMultSum_eq_multiples_card (N d : ℕ) :
    (correctedChenBoundingSieve N).multSum d =
      ((correctedChenUnsiftedComplements N).filter (fun a => d ∣ a)).card := by
  unfold BoundingSieve.multSum
  change (∑ a ∈ correctedChenUnsiftedComplements N,
      if d ∣ a then (1 : ℝ) else 0) =
    ↑((correctedChenUnsiftedComplements N).filter (fun a => d ∣ a)).card
  rw [Finset.sum_boole]

/-- Counting the multiples of `d` in the sieve support is the same as
counting the prime-support partners with `d ∣ N - p`. -/
theorem correctedChenMultiples_card_eq_primeSupport (N d : ℕ) :
    ((correctedChenUnsiftedComplements N).filter (fun a => d ∣ a)).card =
      ((correctedChenUnsiftedPrimeSupport N).filter (fun p => d ∣ N - p)).card := by
  rw [correctedChenUnsiftedComplements_eq_image, Finset.filter_image]
  apply Finset.card_image_of_injOn
  intro p hp q hq hpq
  change N - p = N - q at hpq
  have hp_full : (p < N ∧ p.Prime ∧ 2 ≤ N - p ∧
      ∀ r : ℕ, r.Prime → r < correctedChenZ N → (r ≤ 2 ∨ r ∣ N) → ¬ r ∣ N - p) ∧
        d ∣ N - p := by
    simpa [correctedChenUnsiftedPrimeSupport] using hp
  have hq_full : (q < N ∧ q.Prime ∧ 2 ≤ N - q ∧
      ∀ r : ℕ, r.Prime → r < correctedChenZ N → (r ≤ 2 ∨ r ∣ N) → ¬ r ∣ N - q) ∧
        d ∣ N - q := by
    simpa [correctedChenUnsiftedPrimeSupport] using hq
  have hp_lt : p < N := hp_full.1.1
  have hq_lt : q < N := hq_full.1.1
  omega

/-- The corrected sieve distribution count is the number of prime-support
partners congruent to `N` modulo `d`.  This is the finite seam at which a
Bombieri--Vinogradov/Pan input bounds `multSum` and hence `errSum`. -/
theorem correctedChenMultSum_eq_modEq_count (N d : ℕ) :
    (correctedChenBoundingSieve N).multSum d =
      ((correctedChenUnsiftedPrimeSupport N).filter (fun p => p ≡ N [MOD d])).card := by
  rw [correctedChenMultSum_eq_multiples_card, correctedChenMultiples_card_eq_primeSupport]
  have hf :
      (correctedChenUnsiftedPrimeSupport N).filter (fun p => d ∣ N - p) =
        (correctedChenUnsiftedPrimeSupport N).filter (fun p => p ≡ N [MOD d]) := by
    apply Finset.filter_congr
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp_range, _⟩
    exact AnalyticNumberTheory.Sieve.prime_dvd_complement_iff_modEq (by simpa using hp_range)
  rw [hf]

/-- The corrected sieve remainder at `d` is the prime-support congruence
count minus the density main term. -/
theorem correctedChenRem_eq_modEq_count (N d : ℕ) :
    (correctedChenBoundingSieve N).rem d =
      ((correctedChenUnsiftedPrimeSupport N).filter (fun p => p ≡ N [MOD d])).card -
        correctedChenNu d * (correctedChenBoundingSieve N).totalMass := by
  unfold BoundingSieve.rem
  rw [correctedChenMultSum_eq_modEq_count]
  simp [correctedChenBoundingSieve]

/-- The corrected sieve `errSum` is the sum over sieve divisors of the
absolute congruence-count error.  This is the exact finite form that a
uniform distribution estimate must bound. -/
theorem correctedChenErrSum_eq_modEq (N : ℕ) (muPlus : ℕ → ℝ) :
    (correctedChenBoundingSieve N).errSum muPlus =
      ∑ d ∈ (correctedChenSiftingProduct N).divisors,
        |muPlus d| *
          |((correctedChenUnsiftedPrimeSupport N).filter (fun p => p ≡ N [MOD d])).card -
            correctedChenNu d * (correctedChenBoundingSieve N).totalMass| := by
  unfold BoundingSieve.errSum
  simp_rw [correctedChenRem_eq_modEq_count]
  rfl

/-- The uniform Bombieri--Vinogradov-style distribution condition required by
the corrected sieve: for every `A > 0` there is a uniform `C` such that the
`3^{ω(d)}`-weighted sum over sieve divisors of the congruence-count errors is
at most `C · N/log^A N`, uniformly for all sufficiently large even `N`.

This is the **averaged Pan form**, not a per-modulus bound: the individual
errors do not sum to a `log^{-A}` bound because the divisor count of the
sifting product is exponential in `z`.  The local `bombieri_vinogradov`
interface in `BombieriVinogradov.lean` is only its fixed-parameter remainder
form; this averaged target is what actually bounds the corrected sieve's
`errSum` (see `correctedChenErrSum_le_panWeighted`). -/
def CorrectedChenDistributionCondition : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 1000 ≤ N → Even N →
      ∑ d ∈ (correctedChenSiftingProduct N).divisors,
        (3 : ℝ) ^ d.primeFactors.card *
          |((correctedChenUnsiftedPrimeSupport N).filter (fun p => p ≡ N [MOD d])).card -
            correctedChenNu d * ((N : ℝ) / log (N : ℝ))| ≤
        C * (N : ℝ) / (log (N : ℝ)) ^ A

/-- The counting-sieve `errSum` is bounded by the `3^{ω(d)}`-weighted
congruence-error sum controlled by `CorrectedChenDistributionCondition`. -/
theorem correctedChenErrSum_le_panWeighted (N : ℕ) :
    (correctedChenBoundingSieve N).errSum (fun _ => 1) ≤
      ∑ d ∈ (correctedChenSiftingProduct N).divisors,
        (3 : ℝ) ^ d.primeFactors.card *
          |((correctedChenUnsiftedPrimeSupport N).filter (fun p => p ≡ N [MOD d])).card -
            correctedChenNu d * (correctedChenBoundingSieve N).totalMass| := by
  rw [correctedChenErrSum_eq_modEq]
  apply Finset.sum_le_sum
  intro d hd
  have hw : (1 : ℝ) ≤ (3 : ℝ) ^ d.primeFactors.card := by
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)
  simpa using le_mul_of_one_le_left (abs_nonneg _) hw

/-- Given the averaged Pan-type distribution condition, the counting-sieve
`errSum` of the corrected sieve is uniformly `O(N / log^A N)`.  This closes
the `errSum` line conditionally on the single analytic input
`CorrectedChenDistributionCondition`. -/
theorem correctedChenErrSum_uniform_of_distribution {A : ℝ} (hA : 0 < A)
    (N : ℕ) (hN : 1000 ≤ N) (hEven : Even N)
    (hdist : CorrectedChenDistributionCondition) :
    ∃ C : ℝ, 0 < C ∧
      (correctedChenBoundingSieve N).errSum (fun _ => 1) ≤
        C * (N : ℝ) / (log (N : ℝ)) ^ A := by
  rcases hdist A hA with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  exact le_trans (correctedChenErrSum_le_panWeighted N) (hbound N hN hEven)

/-! ## Applying the weighted Pan--Bombieri--Vinogradov input -/

/-- The reusable AnalyticNumberTheory weighted Pan-BV input
(`AnalyticNumberTheory.Sieve.WeightedPanCondition`) instantiated at the
corrected Chen sieve: `x N = N`, `S N = correctedChenBoundingSieve N`,
`w d = 3^{ω(d)}`.  This is exactly the input formalized in
analytic-number-theory-lean, issue #7. -/
def ChenWeightedPanInput : Prop :=
  AnalyticNumberTheory.Sieve.WeightedPanCondition (fun N : ℕ => (N : ℝ))
    correctedChenBoundingSieve (fun d => (3 : ℝ) ^ d.primeFactors.card)

/-- The corrected sieve's weighted Pan sum is `weightedPanRemainder`:
the congruence-count error at `d` is exactly the `BoundingSieve` remainder
`rem d = multSum d − ν(d)·N/log N`. -/
theorem correctedChenPanSum_eq_weightedPanRemainder (N : ℕ) :
    (∑ d ∈ (correctedChenSiftingProduct N).divisors,
        (3 : ℝ) ^ d.primeFactors.card *
          |((correctedChenUnsiftedPrimeSupport N).filter (fun p => p ≡ N [MOD d])).card -
            correctedChenNu d * ((N : ℝ) / log (N : ℝ))|) =
      AnalyticNumberTheory.Sieve.weightedPanRemainder (correctedChenBoundingSieve N)
        (fun d => (3 : ℝ) ^ d.primeFactors.card) := by
  unfold AnalyticNumberTheory.Sieve.weightedPanRemainder
  apply Finset.sum_congr rfl
  intro d hd
  have hrem : (correctedChenBoundingSieve N).rem d =
      ((correctedChenUnsiftedPrimeSupport N).filter (fun p => p ≡ N [MOD d])).card -
        correctedChenNu d * ((N : ℝ) / log (N : ℝ)) := by
    rw [correctedChenRem_eq_modEq_count]
    rfl
  rw [hrem]

/-- Applying the weighted Pan-BV input: the corrected sieve's
distribution condition is **exactly** `WeightedPanCondition`
instance. -/
theorem correctedChenDistributionCondition_iff_chenWeightedPanInput :
    CorrectedChenDistributionCondition ↔ ChenWeightedPanInput := by
  constructor
  · intro h A hA
    rcases h A hA with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro N hN hEven
    rw [← correctedChenPanSum_eq_weightedPanRemainder N]
    exact hbound N hN hEven
  · intro h A hA
    rcases h A hA with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro N hN hEven
    rw [correctedChenPanSum_eq_weightedPanRemainder N]
    exact hbound N hN hEven

/-- The counting-sieve `errSum` is bounded by the weighted Pan remainder:
apply the reusable `errSum_le_threeOmegaWeightedPanRemainder` at the
corrected Chen instance. -/
theorem correctedChenErrSum_le_weightedPanInput (N : ℕ) :
    (correctedChenBoundingSieve N).errSum (fun _ => 1) ≤
      AnalyticNumberTheory.Sieve.weightedPanRemainder (correctedChenBoundingSieve N)
        (fun d => (3 : ℝ) ^ d.primeFactors.card) :=
  AnalyticNumberTheory.Sieve.errSum_le_threeOmegaWeightedPanRemainder

/-- Given the weighted Pan-BV input, the corrected sieve's `errSum` is
uniformly `O(N / log^A N)`, the remainder bound formulated in
analytic-number-theory-lean, issue #7. -/
theorem correctedChenErrSum_uniform_of_weightedPanInput {A : ℝ} (hA : 0 < A)
    (N : ℕ) (hN : 1000 ≤ N) (hEven : Even N)
    (hinput : ChenWeightedPanInput) :
    ∃ C : ℝ, 0 < C ∧
      (correctedChenBoundingSieve N).errSum (fun _ => 1) ≤
        C * (N : ℝ) / (log (N : ℝ)) ^ A := by
  rcases hinput A hA with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  exact le_trans (correctedChenErrSum_le_weightedPanInput N) (hbound N hN hEven)

/-! ## Completing the Pan bridge: PanMeanValueUniform ⇒ ChenWeightedPanInput

This section proves only the finite bridge from the `a = 1` base count to `correctedChenBoundingSieve.rem`.
It does not represent the general `p₁p₂` weights in Liu's `eqn-adef`, and therefore does not treat
the noncoprime `R₁` in `eqn-r0`. At the end, the source-faithful signed API is used to assemble
`PanMeanValueUniform`; the paper's `R₁` and the signed main-term bound remain explicit analytic inputs. -/

/-- The a=1 weight for the Pan bridge: `f(1) = 1` and zero elsewhere, reducing `panDistributionSum`
to the `a = 1` distribution error `Δ(y; 1, q, l)`. -/
abbrev chenPanWeightOne (a : ℕ) : ℝ := if a = 1 then (1 : ℝ) else 0

/-- **Base count = the a=1 Pan scaled count**: `#{p < N : p prime, 2 ≤ N-p, p ≡ N [MOD q]}`
is exactly `primesInAPBelow (N-2) 1 q (N % q)`, the `a = 1` case of Liu 2022 §II,
and the input side of `primesInAPBelow_one`. -/
theorem supportAPBaseCount_eq_primesInAPBelow (N q : ℕ) (hN : 2 ≤ N) :
    ((Finset.range N).filter (fun p =>
      p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD q])).card =
      AnalyticNumberTheory.Sieve.primesInAPBelow (N - 2) 1 q (N % q) := by
  unfold AnalyticNumberTheory.Sieve.primesInAPBelow
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hpN, hpp, htwo, hcong⟩
    have hle : p ≤ N - 2 := by omega
    refine ⟨?_, hpp, ?_, ?_⟩
    · omega
    · simpa [one_mul] using hle
    · rw [Nat.ModEq] at hcong ⊢
      simpa [one_mul, Nat.mod_mod] using hcong
  · rintro ⟨hpN, hpp, hle, hcong⟩
    have hle' : p ≤ N - 2 := by simpa [one_mul] using hle
    refine ⟨?_, hpp, ?_, ?_⟩
    · omega
    · omega
    · rw [Nat.ModEq] at hcong ⊢
      simpa [Nat.mod_mod] using hcong

/-- The distribution error of the base count equals the a=1 Pan distribution error:
`(baseCount q) − li(N−2)/φ(q) = panDistributionError (N−2) 1 q (N % q)`,
namely `Δ(N-2; 1, q, N mod q) = π(N-2; q, N mod q) - li(N-2)/φ(q)`. -/
theorem supportAPBaseCount_distributionError (N q : ℕ) (hN : 2 ≤ N) :
    ((((Finset.range N).filter (fun p =>
      p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD q])).card : ℝ)) -
      AnalyticNumberTheory.Sieve.logarithmicIntegral (N - 2 : ℝ) / Nat.totient q =
      AnalyticNumberTheory.Sieve.panDistributionError (N - 2) 1 q (N % q) := by
  unfold AnalyticNumberTheory.Sieve.panDistributionError
  rw [AnalyticNumberTheory.Sieve.primesInAPBelow_one (N - 2) q (N % q)]
  congr 1
  · rw [← AnalyticNumberTheory.Sieve.primesInAPBelow_one (N - 2) q (N % q)]
    exact_mod_cast (supportAPBaseCount_eq_primesInAPBelow N q hN)
  · simp [Nat.cast_sub hN]

/-- **Exact remainder under Möbius decomposition** (factor-by-factor decomposition): for `d | P(N)`,
`rem d = Σ_{e | F(N)} μ(e)·baseCount(lcm(d,e)) − li(N)/φ(d)`,
where `baseCount(q) = #{p < N : p prime, 2 ≤ N-p, p ≡ N [MOD q]}` is the prime-AP base count.
On the main-term side, `ν(d) = 1/φ(d)` for squarefree `d | P`, and `totalMass = N/log N = li(N)`. -/
theorem correctedChenRem_eq_moebiusBaseCount (N d : ℕ)
    (hd : d ∣ correctedChenSiftingProduct N) :
    (correctedChenBoundingSieve N).rem d =
      (∑ e ∈ (correctedChenForbiddenProduct N).divisors,
        (μ e : ℝ) * (((Finset.range N).filter (fun p =>
          p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ)) -
      (1 : ℝ) / (Nat.totient d : ℝ) * ((N : ℝ) / log (N : ℝ)) := by
  rw [correctedChenRem_eq_modEq_count N d]
  rw [unsiftedPrimeSupport_AP_count_eq_moebiusSum_lcm N d]
  rw [correctedChenTotalMass_eq N]
  have hnu : correctedChenNu d = (1 : ℝ) / (Nat.totient d : ℝ) := by
    unfold correctedChenNu
    exact AnalyticNumberTheory.Sieve.goldbachNu_squarefree_eq_inv_totient
      (BoundingSieve.squarefree_of_dvd_prodPrimes (s := correctedChenBoundingSieve N) hd)
  rw [hnu]

/-- For the a=1 weight, `panDistributionSum` reduces to `panDistributionError`. -/
theorem panDistributionSum_one_eq_distributionError (y X q l : ℕ) (hX : 1 ≤ X) :
    AnalyticNumberTheory.Sieve.panDistributionSum y X q l chenPanWeightOne =
      AnalyticNumberTheory.Sieve.panDistributionError y 1 q l := by
  unfold AnalyticNumberTheory.Sieve.panDistributionSum
  rw [Finset.sum_eq_single 1]
  · have hc : (1 : ℕ).Coprime q := by
      rw [Nat.coprime_iff_gcd_eq_one]
      simp
    simp [chenPanWeightOne]
  · intro b hb hbne
    simp [chenPanWeightOne, hbne]
  · intro hnot
    exfalso
    exact hnot (by
      rw [Finset.mem_range]
      omega)

/-- The delta weight has no non-coprime contribution. This proves why the
`a = 1` bridge bypasses, rather than estimates, Liu's general-`f` `R₁`. -/
theorem chenPanWeightOne_eq_zero_of_not_coprime {a q : ℕ}
    (hcop : ¬a.Coprime q) :
    chenPanWeightOne a = 0 := by
  by_cases ha : a = 1
  · subst a
    exact (hcop (by simp)).elim
  · simp [chenPanWeightOne, ha]

/-- The entire finite non-coprime lane vanishes for `chenPanWeightOne`. -/
theorem chenPanWeightOne_noncoprimeSum_eq_zero (y X q l : ℕ) :
    (∑ a ∈ Finset.range (X + 1),
      if ¬a.Coprime q then
        chenPanWeightOne a *
          AnalyticNumberTheory.Sieve.panDistributionError y a q l
      else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro a ha
  by_cases hcop : a.Coprime q
  · simp [hcop]
  · simp [hcop, chenPanWeightOne_eq_zero_of_not_coprime hcop]

/-- The unrestricted finite sum also collapses to the `a = 1` base-count
error. Together with the preceding theorem, this is the exact scope of the
delta-weight bridge. -/
theorem chenPanWeightOne_fullSum_eq_distributionError
    (y X q l : ℕ) (hX : 1 ≤ X) :
    (∑ a ∈ Finset.range (X + 1),
      chenPanWeightOne a *
        AnalyticNumberTheory.Sieve.panDistributionError y a q l) =
      AnalyticNumberTheory.Sieve.panDistributionError y 1 q l := by
  classical
  rw [Finset.sum_eq_single 1]
  · simp [chenPanWeightOne]
  · intro b hb hbne
    simp [chenPanWeightOne, hbne]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (by omega))).elim

/-- The sifting product is coprime to `N`: each prime factor of `P(N)` satisfies `r ∤ N`. -/
theorem coprime_siftingProduct_N (N : ℕ) :
    Nat.Coprime (correctedChenSiftingProduct N) N := by
  apply Nat.coprime_of_dvd'
  intro r hr hrP hrN
  rcases (prime_dvd_correctedChenSiftingProduct hr).mp hrP with ⟨_, _, hrN'⟩
  exact False.elim (hrN' hrN)

/-- For a squarefree modulus, `μ(d)² = 1`, since `μ(d) = ±1`. -/
theorem moebius_sq_eq_one_of_squarefree {d : ℕ} (hd : Squarefree d) :
    (((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2) = 1 := by
  have hz : (ArithmeticFunction.moebius d : ℤ) ^ 2 = 1 := by
    rw [ArithmeticFunction.moebius_sq, if_pos hd]
  exact_mod_cast hz

/-- `panMaxL` is nonnegative: it is a maximum of absolute values, or zero. -/
theorem panMaxL_nonneg (y X q : ℕ) (f : ℕ → ℝ) :
    0 ≤ AnalyticNumberTheory.Sieve.panMaxL y X q f := by
  unfold AnalyticNumberTheory.Sieve.panMaxL
  dsimp only
  by_cases hS : (AnalyticNumberTheory.Sieve.unitResidues q).Nonempty
  · rw [dif_pos hS]
    have hmem : (Finset.image (fun l => |AnalyticNumberTheory.Sieve.panDistributionSum y X q l f|)
          (AnalyticNumberTheory.Sieve.unitResidues q)).max'
          (Finset.image_nonempty.mpr hS) ∈
        (Finset.image (fun l => |AnalyticNumberTheory.Sieve.panDistributionSum y X q l f|)
          (AnalyticNumberTheory.Sieve.unitResidues q)) :=
      Finset.max'_mem _ _
    rcases Finset.mem_image.mp hmem with ⟨l, hl, heq⟩
    rw [← heq]
    exact abs_nonneg _
  · rw [dif_neg hS]

/-- `panMaxY` is nonnegative. -/
theorem panMaxY_nonneg (X q x : ℕ) (f : ℕ → ℝ) :
    0 ≤ AnalyticNumberTheory.Sieve.panMaxY X q x f := by
  unfold AnalyticNumberTheory.Sieve.panMaxY
  have hmem : AnalyticNumberTheory.Sieve.panMaxL 0 X q f ∈
      (Finset.range (x + 1)).image (fun y => AnalyticNumberTheory.Sieve.panMaxL y X q f) := by
    exact Finset.mem_image.mpr ⟨0, by simp, rfl⟩
  exact le_trans (panMaxL_nonneg 0 X q f) (Finset.le_max' _ _ hmem)

/-- The delta-one distribution error at any reduced residue is bounded by
Pan's two nested maxima. -/
theorem abs_distributionError_le_panMaxY_of_coprime (N d : ℕ)
    (hN : 2 ≤ N) (hd0 : d ≠ 0) (hcop : (N % d).Coprime d) :
    |AnalyticNumberTheory.Sieve.panDistributionError (N - 2) 1 d (N % d)| ≤
      AnalyticNumberTheory.Sieve.panMaxY N d (Nat.floor (N : ℝ)) chenPanWeightOne := by
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  have hde : |AnalyticNumberTheory.Sieve.panDistributionError (N - 2) 1 d (N % d)| =
      |AnalyticNumberTheory.Sieve.panDistributionSum (N - 2) N d (N % d) chenPanWeightOne| := by
    rw [panDistributionSum_one_eq_distributionError (N - 2) N d (N % d) (by omega : 1 ≤ N)]
  rw [hde]
  have hmodlt : N % d < d := Nat.mod_lt _ hdpos
  have hleMY : AnalyticNumberTheory.Sieve.panMaxL (N - 2) N d chenPanWeightOne ≤
      AnalyticNumberTheory.Sieve.panMaxY N d (Nat.floor (N : ℝ)) chenPanWeightOne := by
    unfold AnalyticNumberTheory.Sieve.panMaxY
    exact Finset.le_max' (Finset.image (fun y => AnalyticNumberTheory.Sieve.panMaxL y N d chenPanWeightOne)
      (Finset.range (Nat.floor (N : ℝ) + 1)))
      (AnalyticNumberTheory.Sieve.panMaxL (N - 2) N d chenPanWeightOne) (by
      exact Finset.mem_image.mpr ⟨N - 2, by
        change N - 2 ∈ Finset.range (Nat.floor (N : ℝ) + 1)
        have hfl : Nat.floor (N : ℝ) = N := Nat.floor_natCast N
        rw [hfl]
        exact Finset.mem_range.mpr (by omega), rfl⟩)
  exact le_trans (by
    unfold AnalyticNumberTheory.Sieve.panMaxL
    dsimp only
    have hlS : N % d ∈ AnalyticNumberTheory.Sieve.unitResidues d := by
      rw [AnalyticNumberTheory.Sieve.unitResidues]
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hmodlt, hcop⟩
    have hS : (AnalyticNumberTheory.Sieve.unitResidues d).Nonempty := ⟨N % d, hlS⟩
    rw [dif_pos hS]
    exact Finset.le_max' (Finset.image (fun l => |AnalyticNumberTheory.Sieve.panDistributionSum (N - 2) N d l chenPanWeightOne|)
      (AnalyticNumberTheory.Sieve.unitResidues d))
      |AnalyticNumberTheory.Sieve.panDistributionSum (N - 2) N d (N % d) chenPanWeightOne| (by
      exact Finset.mem_image.mpr ⟨N % d, hlS, rfl⟩)
    ) hleMY

/-- Pan control of the distribution error: for `d | P(N)`,
`|Δ(N-2; 1, d, N mod d)| ≤ panMaxY N d N (a=1 weight)`.
The modulus `d` is coprime to `N`, since its prime factors divide `P` and do not divide `N`.
Thus `(N mod d, d) = 1` places the residue in `unitResidues d`, the range of the `panMaxL` maximum.
This statement also covers `d = 1`, whose unique canonical residue is `0`. -/
theorem abs_distributionError_le_panMaxY (N d : ℕ)
    (hd : d ∣ correctedChenSiftingProduct N) (hN : 2 ≤ N) :
    |AnalyticNumberTheory.Sieve.panDistributionError (N - 2) 1 d (N % d)| ≤
     AnalyticNumberTheory.Sieve.panMaxY N d (Nat.floor (N : ℝ)) chenPanWeightOne := by
  have hd0 : d ≠ 0 := by
    intro hd0
    subst d
    have hP0 : correctedChenSiftingProduct N = 0 := by simpa using hd
    exact correctedChenSiftingProduct_ne_zero N hP0
  have hPN : Nat.Coprime (correctedChenSiftingProduct N) N := coprime_siftingProduct_N N
  have hdN : Nat.Coprime d N := Nat.Coprime.coprime_dvd_left hd hPN
  have hcop : (N % d).Coprime d := by
    apply Nat.coprime_of_dvd'
    intro k hk hk1 hk2
    have hkN : k ∣ N := by
     have hkdiv : k ∣ d * (N / d) + N % d :=
       Nat.dvd_add (by simpa [mul_comm] using (dvd_mul_of_dvd_right hk2 (N / d))) hk1
     have hNdef : d * (N / d) + N % d = N := by
       simpa [Nat.add_comm] using (Nat.mod_add_div N d)
     rw [← hNdef]
     exact hkdiv
    exact False.elim (Nat.not_coprime_of_dvd_of_dvd (Nat.Prime.one_lt hk) hk2 hkN hdN)
  exact abs_distributionError_le_panMaxY_of_coprime N d hN hd0 hcop


/-- **Support/truncation input**: the part of Chen's remainder not covered by the modulus sum
`q ≤ x^{1/2}/log^B x` in the weighted Pan mean-value theorem consists of the errors
`|Δ'(d)|` for large moduli `d > D` and for `d = 1`, together with `|rem d - Δ'(d)|`.
The latter includes the Möbius correction `Σ_{1≠e|F} μ(e)·baseCount(lcm(d,e))` and the main-term difference `(li(N)-li(N-2))/φ(d)`.
These are uniformly bounded by `C·N/log^A N`. Classical sources: the support truncation in Pan 1963 / Halberstam--Richert
Ch. 10. This is the Möbius support correction for the `a = 1` base count, **not**
the `R₁` for general `p₁p₂` weights in Liu 2022 `eqn-r0`; the latter remains a separate open input.
Its proof, involving Titchmarsh-type averages and prime-AP counts for large moduli, is a research-level input. -/
def CorrectedChenPanTruncationInput : Prop :=
  ∀ A : ℝ, 0 < A → ∀ B : ℝ, ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℕ,
    ∀ N : ℕ, x₀ ≤ N → Even N →
      (∑ d ∈ (correctedChenSiftingProduct N).divisors,
        (3 : ℝ) ^ d.primeFactors.card *
          |(correctedChenBoundingSieve N).rem d -
            AnalyticNumberTheory.Sieve.panDistributionError (N - 2) 1 d (N % d)|) +
      (∑ d ∈ (correctedChenSiftingProduct N).divisors.filter (fun d =>
          ¬ (2 ≤ d ∧ d ≤ Nat.floor ((N : ℝ) ^ (1 / 2 : ℝ) / (log (N : ℝ)) ^ B))),
        (3 : ℝ) ^ d.primeFactors.card *
          |AnalyticNumberTheory.Sieve.panDistributionError (N - 2) 1 d (N % d)|) ≤
        C * (N : ℝ) / (log (N : ℝ)) ^ A

/-- Reduction of Chen's weighted remainder sum: for `N ≥ 1000` and any `B`,
`Σ_{d | P(N)} 3^{ω(d)}·|rem d| ≤ PanSum(N,B) + Trunc(N,B)`,
where `PanSum` is the `panMaxY`-weighted modulus sum in `PanMeanValueUniform`, controlled by `hpan`,
and `Trunc` comprises the two remainder terms controlled by `CorrectedChenPanTruncationInput`:
`|rem d - Δ'(d)|` and `|Δ'(d)|` for uncovered moduli. -/
theorem correctedChenPanSum_reduction (N : ℕ) (hN : 1000 ≤ N) (B : ℝ) :
    (∑ d ∈ (correctedChenSiftingProduct N).divisors,
      (3 : ℝ) ^ d.primeFactors.card *
        |(correctedChenBoundingSieve N).rem d|) ≤
      (∑ q ∈ Finset.range (Nat.floor ((N : ℝ) ^ (1 / 2 : ℝ) / (log (N : ℝ)) ^ B) + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          AnalyticNumberTheory.Sieve.panMaxY N q (Nat.floor (N : ℝ)) chenPanWeightOne) +
      (∑ d ∈ (correctedChenSiftingProduct N).divisors,
        (3 : ℝ) ^ d.primeFactors.card *
          |(correctedChenBoundingSieve N).rem d -
            AnalyticNumberTheory.Sieve.panDistributionError (N - 2) 1 d (N % d)|) +
      (∑ d ∈ (correctedChenSiftingProduct N).divisors.filter (fun d =>
          ¬ (2 ≤ d ∧ d ≤ Nat.floor ((N : ℝ) ^ (1 / 2 : ℝ) / (log (N : ℝ)) ^ B))),
        (3 : ℝ) ^ d.primeFactors.card *
          |AnalyticNumberTheory.Sieve.panDistributionError (N - 2) 1 d (N % d)|) := by
  classical
  let D : ℕ := Nat.floor ((N : ℝ) ^ (1 / 2 : ℝ) / (log (N : ℝ)) ^ B)
  let Δ' : ℕ → ℝ := fun d => AnalyticNumberTheory.Sieve.panDistributionError (N - 2) 1 d (N % d)
  let covered : Finset ℕ := (correctedChenSiftingProduct N).divisors.filter (fun d => 2 ≤ d ∧ d ≤ D)
  have hN2 : 2 ≤ N := by omega
  have htri : ∀ d ∈ (correctedChenSiftingProduct N).divisors,
      (3 : ℝ) ^ d.primeFactors.card * |(correctedChenBoundingSieve N).rem d| ≤
        (3 : ℝ) ^ d.primeFactors.card * (|Δ' d| + |(correctedChenBoundingSieve N).rem d - Δ' d|) := by
    intro d hd
    have hle : |(correctedChenBoundingSieve N).rem d| ≤ |Δ' d| + |(correctedChenBoundingSieve N).rem d - Δ' d| := by
      have hsub : (correctedChenBoundingSieve N).rem d = Δ' d + ((correctedChenBoundingSieve N).rem d - Δ' d) := by
        ring
      nth_rewrite 1 [hsub]
      rw [abs_le]
      constructor
      · have h1 : -|Δ' d| ≤ Δ' d := by
          have h := neg_le_abs (Δ' d)
          linarith
        have h2 : -|(correctedChenBoundingSieve N).rem d - Δ' d| ≤
            (correctedChenBoundingSieve N).rem d - Δ' d := by
          have h := neg_le_abs ((correctedChenBoundingSieve N).rem d - Δ' d)
          linarith
        linarith
      · have h1 : Δ' d ≤ |Δ' d| := le_abs_self (Δ' d)
        have h2 : (correctedChenBoundingSieve N).rem d - Δ' d ≤
            |(correctedChenBoundingSieve N).rem d - Δ' d| :=
          le_abs_self ((correctedChenBoundingSieve N).rem d - Δ' d)
        linarith
    exact mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ (3 : ℝ) ^ d.primeFactors.card)
  have hsum1 : (∑ d ∈ (correctedChenSiftingProduct N).divisors,
      (3 : ℝ) ^ d.primeFactors.card * |(correctedChenBoundingSieve N).rem d|) ≤
    (∑ d ∈ (correctedChenSiftingProduct N).divisors,
      (3 : ℝ) ^ d.primeFactors.card * (|Δ' d| + |(correctedChenBoundingSieve N).rem d - Δ' d|)) := by
    exact Finset.sum_le_sum htri
  have hsum2 : (∑ d ∈ (correctedChenSiftingProduct N).divisors,
      (3 : ℝ) ^ d.primeFactors.card * (|Δ' d| + |(correctedChenBoundingSieve N).rem d - Δ' d|)) =
    (∑ d ∈ (correctedChenSiftingProduct N).divisors,
      (3 : ℝ) ^ d.primeFactors.card * |Δ' d|) +
    (∑ d ∈ (correctedChenSiftingProduct N).divisors,
      (3 : ℝ) ^ d.primeFactors.card * |(correctedChenBoundingSieve N).rem d - Δ' d|) := by
    calc
      (∑ d ∈ (correctedChenSiftingProduct N).divisors,
          (3 : ℝ) ^ d.primeFactors.card * (|Δ' d| + |(correctedChenBoundingSieve N).rem d - Δ' d|))
          = (∑ d ∈ (correctedChenSiftingProduct N).divisors,
              ((3 : ℝ) ^ d.primeFactors.card * |Δ' d| +
                (3 : ℝ) ^ d.primeFactors.card * |(correctedChenBoundingSieve N).rem d - Δ' d|)) := by
            apply Finset.sum_congr rfl
            intro d hd
            ring
      _ = (∑ d ∈ (correctedChenSiftingProduct N).divisors, (3 : ℝ) ^ d.primeFactors.card * |Δ' d|) +
            (∑ d ∈ (correctedChenSiftingProduct N).divisors,
              (3 : ℝ) ^ d.primeFactors.card * |(correctedChenBoundingSieve N).rem d - Δ' d|) := by
            rw [Finset.sum_add_distrib]
  have hcov : (∑ d ∈ covered, (3 : ℝ) ^ d.primeFactors.card * |Δ' d|) ≤
      (∑ q ∈ Finset.range (D + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          AnalyticNumberTheory.Sieve.panMaxY N q (Nat.floor (N : ℝ)) chenPanWeightOne) := by
    have hterm : ∀ d ∈ covered,
        (3 : ℝ) ^ d.primeFactors.card * |Δ' d| ≤
          ((μ d : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ d.primeFactors.card *
            AnalyticNumberTheory.Sieve.panMaxY N d (Nat.floor (N : ℝ)) chenPanWeightOne := by
      intro d hd
      rcases Finset.mem_filter.mp hd with ⟨hdmem, hcond⟩
      have hdvd : d ∣ correctedChenSiftingProduct N := (Nat.mem_divisors.mp hdmem).1
      have hle1 := abs_distributionError_le_panMaxY N d hdvd hN2
      have hsq : Squarefree d :=
        BoundingSieve.squarefree_of_dvd_prodPrimes (s := correctedChenBoundingSieve N) hdvd
      have hmu2 : ((μ d : ℤ) : ℝ) ^ 2 = 1 := moebius_sq_eq_one_of_squarefree hsq
      calc
        (3 : ℝ) ^ d.primeFactors.card * |Δ' d|
            ≤ (3 : ℝ) ^ d.primeFactors.card *
                AnalyticNumberTheory.Sieve.panMaxY N d (Nat.floor (N : ℝ)) chenPanWeightOne := by
              exact mul_le_mul_of_nonneg_left hle1 (by positivity : 0 ≤ (3 : ℝ) ^ d.primeFactors.card)
        _ = ((μ d : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ d.primeFactors.card *
              AnalyticNumberTheory.Sieve.panMaxY N d (Nat.floor (N : ℝ)) chenPanWeightOne := by
              rw [hmu2]
              ring
    have hsumcov : (∑ d ∈ covered, (3 : ℝ) ^ d.primeFactors.card * |Δ' d|) ≤
        (∑ d ∈ covered, ((μ d : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ d.primeFactors.card *
          AnalyticNumberTheory.Sieve.panMaxY N d (Nat.floor (N : ℝ)) chenPanWeightOne) := by
      exact Finset.sum_le_sum hterm
    have hsubset : covered ⊆ Finset.range (D + 1) := by
      intro d hd
      rw [Finset.mem_range]
      rcases Finset.mem_filter.mp hd with ⟨hdmem, hcond⟩
      omega
    have hnonneg : ∀ q ∈ Finset.range (D + 1), q ∉ covered →
        0 ≤ ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          AnalyticNumberTheory.Sieve.panMaxY N q (Nat.floor (N : ℝ)) chenPanWeightOne := by
      intro q hq hnot
      exact mul_nonneg (mul_nonneg (by positivity : 0 ≤ ((μ q : ℤ) : ℝ) ^ 2)
        (by positivity : 0 ≤ (3 : ℝ) ^ q.primeFactors.card))
        (panMaxY_nonneg N q (Nat.floor (N : ℝ)) chenPanWeightOne)
    exact le_trans hsumcov (Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg)
  have hsplit : (∑ d ∈ (correctedChenSiftingProduct N).divisors, (3 : ℝ) ^ d.primeFactors.card * |Δ' d|) =
      (∑ d ∈ covered, (3 : ℝ) ^ d.primeFactors.card * |Δ' d|) +
      (∑ d ∈ (correctedChenSiftingProduct N).divisors.filter (fun d => ¬ (2 ≤ d ∧ d ≤ D)),
        (3 : ℝ) ^ d.primeFactors.card * |Δ' d|) := by
    rw [← Finset.sum_filter_add_sum_filter_not (correctedChenSiftingProduct N).divisors
      (fun d => 2 ≤ d ∧ d ≤ D) (fun d => (3 : ℝ) ^ d.primeFactors.card * |Δ' d|)]
  calc
    (∑ d ∈ (correctedChenSiftingProduct N).divisors,
      (3 : ℝ) ^ d.primeFactors.card * |(correctedChenBoundingSieve N).rem d|)
        ≤ (∑ d ∈ (correctedChenSiftingProduct N).divisors,
            (3 : ℝ) ^ d.primeFactors.card * (|Δ' d| + |(correctedChenBoundingSieve N).rem d - Δ' d|)) := hsum1
    _ = (∑ d ∈ (correctedChenSiftingProduct N).divisors, (3 : ℝ) ^ d.primeFactors.card * |Δ' d|) +
          (∑ d ∈ (correctedChenSiftingProduct N).divisors,
            (3 : ℝ) ^ d.primeFactors.card * |(correctedChenBoundingSieve N).rem d - Δ' d|) := hsum2
    _ = ((∑ d ∈ covered, (3 : ℝ) ^ d.primeFactors.card * |Δ' d|) +
          (∑ d ∈ (correctedChenSiftingProduct N).divisors.filter (fun d => ¬ (2 ≤ d ∧ d ≤ D)),
            (3 : ℝ) ^ d.primeFactors.card * |Δ' d|)) +
          (∑ d ∈ (correctedChenSiftingProduct N).divisors,
            (3 : ℝ) ^ d.primeFactors.card * |(correctedChenBoundingSieve N).rem d - Δ' d|) := by
            rw [hsplit]
    _ ≤ ((∑ q ∈ Finset.range (D + 1), ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
              AnalyticNumberTheory.Sieve.panMaxY N q (Nat.floor (N : ℝ)) chenPanWeightOne) +
          (∑ d ∈ (correctedChenSiftingProduct N).divisors.filter (fun d => ¬ (2 ≤ d ∧ d ≤ D)),
            (3 : ℝ) ^ d.primeFactors.card * |Δ' d|)) +
          (∑ d ∈ (correctedChenSiftingProduct N).divisors,
            (3 : ℝ) ^ d.primeFactors.card * |(correctedChenBoundingSieve N).rem d - Δ' d|) := by
            nlinarith [hcov]
    _ = (∑ q ∈ Finset.range (D + 1), ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
              AnalyticNumberTheory.Sieve.panMaxY N q (Nat.floor (N : ℝ)) chenPanWeightOne) +
          (∑ d ∈ (correctedChenSiftingProduct N).divisors,
            (3 : ℝ) ^ d.primeFactors.card * |(correctedChenBoundingSieve N).rem d - Δ' d|) +
          (∑ d ∈ (correctedChenSiftingProduct N).divisors.filter (fun d =>
              ¬ (2 ≤ d ∧ d ≤ Nat.floor ((N : ℝ) ^ (1 / 2 : ℝ) / (log (N : ℝ)) ^ B))),
            (3 : ℝ) ^ d.primeFactors.card *
              |AnalyticNumberTheory.Sieve.panDistributionError (N - 2) 1 d (N % d)|) := by
            ring


/-- Trivial remainder bound: for `d | P(N)` and `N ≥ 1000`,
`|rem d| ≤ (1 + 1/log 1000)·N`, using support cardinality ≤ N and `ν(d) = 1/φ(d) ≤ 1`,
`N/logN ≤ N/log 1000`). -/
theorem abs_rem_le_const_mul_N (N d : ℕ) (hN : 1000 ≤ N) (hd : d ∣ correctedChenSiftingProduct N) :
    |(correctedChenBoundingSieve N).rem d| ≤ (1 + 1 / Real.log 1000) * (N : ℝ) := by
  have hlog1000 : 0 < Real.log 1000 := Real.log_pos (by norm_num : (1 : ℝ) < (1000 : ℝ))
  have hlogN : Real.log 1000 ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by norm_num : 0 < (1000 : ℝ)) (by exact_mod_cast hN)
  have hsq : Squarefree d := BoundingSieve.squarefree_of_dvd_prodPrimes (s := correctedChenBoundingSieve N) hd
  have hnu : correctedChenNu d = (1 : ℝ) / (Nat.totient d : ℝ) := by
    unfold correctedChenNu
    exact AnalyticNumberTheory.Sieve.goldbachNu_squarefree_eq_inv_totient hsq
  have hφ0 : 0 < Nat.totient d := by
    have hP0 : 0 < correctedChenSiftingProduct N := by
      unfold correctedChenSiftingProduct
      exact Finset.prod_pos (by intro r hr; exact (Finset.mem_filter.mp hr).2.1.pos)
    exact (Nat.totient_pos).mpr (Nat.pos_of_dvd_of_pos hd hP0)
  have hφr : (0 : ℝ) < (Nat.totient d : ℝ) := by exact_mod_cast hφ0
  have hX0 : 0 ≤ (correctedChenBoundingSieve N).totalMass := by
    rw [correctedChenTotalMass_eq N]
    exact div_nonneg (by positivity : 0 ≤ (N : ℝ)) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N)))
  have h1 : (correctedChenBoundingSieve N).multSum d ≤ (N : ℝ) := by
    unfold BoundingSieve.multSum
    have hw : (correctedChenBoundingSieve N).weights = fun _ => 1 := rfl
    have hc2 : (correctedChenUnsiftedComplements N).card ≤ N := by
      calc
        (correctedChenUnsiftedComplements N).card
            ≤ ((Finset.range N).filter (fun p => p.Prime ∧ 2 ≤ N - p ∧
                ∀ r : ℕ, r.Prime → r < correctedChenZ N → (r ≤ 2 ∨ r ∣ N) → ¬ r ∣ N - p)).card :=
              Finset.card_image_le
        _ ≤ (Finset.range N).card := Finset.card_le_card (Finset.filter_subset _ _)
        _ = N := Finset.card_range N
    calc
      (∑ n ∈ (correctedChenBoundingSieve N).support, if d ∣ n then (correctedChenBoundingSieve N).weights n else 0)
          = (∑ n ∈ (correctedChenBoundingSieve N).support, if d ∣ n then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [hw]
      _ = ({n ∈ (correctedChenBoundingSieve N).support | d ∣ n}.card : ℝ) := by
            rw [Finset.sum_boole]
      _ = ({n ∈ correctedChenUnsiftedComplements N | d ∣ n}.card : ℝ) := rfl
      _ ≤ ((correctedChenUnsiftedComplements N).card : ℝ) := by
            exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _))
      _ ≤ (N : ℝ) := by
            exact_mod_cast hc2
  have h2 : correctedChenNu d * (correctedChenBoundingSieve N).totalMass ≤ (N : ℝ) / Real.log 1000 := by
    have hnu1 : correctedChenNu d ≤ 1 := by
      rw [hnu]
      have hφ1 : (1 : ℝ) ≤ (Nat.totient d : ℝ) := by exact_mod_cast (show 1 ≤ Nat.totient d by omega)
      exact (div_le_iff₀ hφr).mpr (by nlinarith)
    have hX : (correctedChenBoundingSieve N).totalMass ≤ (N : ℝ) / Real.log 1000 := by
      rw [correctedChenTotalMass_eq N]
      rw [div_le_div_iff₀ (Real.log_pos (by exact_mod_cast (by omega : 1 < N))) hlog1000]
      have hposN : 0 ≤ (N : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left hlogN hposN
    exact le_trans (by simpa using (mul_le_mul_of_nonneg_right hnu1 hX0)) hX
  have hle : |(correctedChenBoundingSieve N).rem d| ≤
      (correctedChenBoundingSieve N).multSum d + correctedChenNu d * (correctedChenBoundingSieve N).totalMass := by
    unfold BoundingSieve.rem
    change |(correctedChenBoundingSieve N).multSum d - correctedChenNu d * (correctedChenBoundingSieve N).totalMass| ≤
      (correctedChenBoundingSieve N).multSum d + correctedChenNu d * (correctedChenBoundingSieve N).totalMass
    have hnon1 : 0 ≤ (correctedChenBoundingSieve N).multSum d := by
      unfold BoundingSieve.multSum
      apply Finset.sum_nonneg
      intro n hn
      by_cases h : d ∣ n
      · simpa [h] using (correctedChenBoundingSieve N).weights_nonneg n
      · simp [h]
    have hnon2 : 0 ≤ correctedChenNu d * (correctedChenBoundingSieve N).totalMass := by
      have hnu0 : 0 ≤ correctedChenNu d := by
        rw [hnu]
        exact div_nonneg (by norm_num) (by exact_mod_cast (le_of_lt hφ0))
      exact mul_nonneg hnu0 hX0
    rw [abs_le]
    constructor
    · nlinarith [hnon1]
    · nlinarith [hnon2]
  calc
    |(correctedChenBoundingSieve N).rem d|
        ≤ (correctedChenBoundingSieve N).multSum d + correctedChenNu d * (correctedChenBoundingSieve N).totalMass := hle
    _ ≤ (N : ℝ) + (N : ℝ) / Real.log 1000 := add_le_add h1 h2
    _ = (1 + 1 / Real.log 1000) * (N : ℝ) := by ring

/-- Divisor sum: for squarefree `P`, `Σ_{d | P} 3^{ω(d)} ≤ 6^{ω(P)}`. -/
theorem threeOmegaDivisorSum_le_sixOmega (P : ℕ) (hP : Squarefree P) (hP0 : P ≠ 0) :
    (∑ d ∈ P.divisors, (3 : ℝ) ^ d.primeFactors.card) ≤ (6 : ℝ) ^ P.primeFactors.card := by
  have hωle : ∀ d ∈ P.divisors, d.primeFactors.card ≤ P.primeFactors.card := by
    intro d hd
    exact Finset.card_le_card (Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hP0)
  have hτ : P.divisors.card = 2 ^ P.primeFactors.card := by
    have hc := Nat.card_divisors hP0
    rw [hc]
    have hfac : ∀ p ∈ P.primeFactors, P.factorization p + 1 = 2 := by
      intro p hp
      have hf : P.factorization p = 1 :=
        Nat.factorization_eq_one_of_squarefree hP (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
      omega
    rw [Finset.prod_congr rfl (by intro p hp; rw [hfac p hp])]
    exact Finset.prod_eq_pow_card (by intro p hp; norm_num)
  calc
    (∑ d ∈ P.divisors, (3 : ℝ) ^ d.primeFactors.card)
        ≤ (∑ d ∈ P.divisors, (3 : ℝ) ^ P.primeFactors.card) := by
          apply Finset.sum_le_sum
          intro d hd
          exact pow_le_pow_right₀ (by norm_num : 1 ≤ (3 : ℝ)) (hωle d hd)
    _ = (P.divisors.card : ℝ) * (3 : ℝ) ^ P.primeFactors.card := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = (2 : ℝ) ^ P.primeFactors.card * (3 : ℝ) ^ P.primeFactors.card := by
          have hτr : (P.divisors.card : ℝ) = (2 : ℝ) ^ P.primeFactors.card := by exact_mod_cast hτ
          rw [hτr]
    _ = (6 : ℝ) ^ P.primeFactors.card := by
          rw [← mul_pow]
          norm_num

/-- Weighted divisor sum for the sifting product: `Σ_{d | P(N)} 3^{ω(d)} ≤ 6^{z(N)}`. -/
theorem threeOmegaDivisorSum_siftingProduct_le_sixPowZ (N : ℕ) :
    (∑ d ∈ (correctedChenSiftingProduct N).divisors, (3 : ℝ) ^ d.primeFactors.card) ≤
      (6 : ℝ) ^ correctedChenZ N := by
  have hle1 := threeOmegaDivisorSum_le_sixOmega (correctedChenSiftingProduct N)
    (correctedChenSiftingProduct_squarefree N) (correctedChenSiftingProduct_ne_zero N)
  have hω : (correctedChenSiftingProduct N).primeFactors.card ≤ correctedChenZ N := by
    rw [correctedChenSiftingProduct_primeFactors N]
    exact le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by simp)
  exact le_trans hle1 (pow_le_pow_right₀ (by norm_num : 1 ≤ (6 : ℝ)) hω)

/-- `z(N) ≤ z(x₀)` for `N ≤ x₀`, by monotonicity of the real power and the floor. -/
theorem correctedChenZ_le_of_le (N x₀ : ℕ) (hNx : N ≤ x₀) :
    correctedChenZ N ≤ correctedChenZ x₀ := by
  unfold correctedChenZ
  exact max_le_max le_rfl (Nat.floor_le_floor (Real.rpow_le_rpow (by positivity : 0 ≤ (N : ℝ))
    (by exact_mod_cast hNx) (by norm_num : 0 ≤ (1 / 10 : ℝ))))

/-- Trivial remainder-sum bound on the small-`N` interval `1000 ≤ N < x₀`:
`Σ_{d | P(N)} 3^{ω(d)}·|rem d| ≤ 6^{z(x₀)}·(1 + 1/log 1000)·N`. -/
theorem correctedChenPanSum_small_bound (N x₀ : ℕ) (hN : 1000 ≤ N) (hNx : N ≤ x₀) :
    (∑ d ∈ (correctedChenSiftingProduct N).divisors,
      (3 : ℝ) ^ d.primeFactors.card * |(correctedChenBoundingSieve N).rem d|) ≤
      (6 : ℝ) ^ correctedChenZ x₀ * ((1 + 1 / Real.log 1000) * (N : ℝ)) := by
  have hrem : ∀ d ∈ (correctedChenSiftingProduct N).divisors,
      (3 : ℝ) ^ d.primeFactors.card * |(correctedChenBoundingSieve N).rem d| ≤
        (3 : ℝ) ^ d.primeFactors.card * ((1 + 1 / Real.log 1000) * (N : ℝ)) := by
    intro d hd
    exact mul_le_mul_of_nonneg_left (abs_rem_le_const_mul_N N d hN (Nat.dvd_of_mem_divisors hd))
      (by positivity : 0 ≤ (3 : ℝ) ^ d.primeFactors.card)
  have hsum : (∑ d ∈ (correctedChenSiftingProduct N).divisors,
      (3 : ℝ) ^ d.primeFactors.card * |(correctedChenBoundingSieve N).rem d|) ≤
    (∑ d ∈ (correctedChenSiftingProduct N).divisors,
      (3 : ℝ) ^ d.primeFactors.card * ((1 + 1 / Real.log 1000) * (N : ℝ))) := by
    exact Finset.sum_le_sum hrem
  have h6 : (∑ d ∈ (correctedChenSiftingProduct N).divisors,
      (3 : ℝ) ^ d.primeFactors.card * ((1 + 1 / Real.log 1000) * (N : ℝ))) ≤
      (6 : ℝ) ^ correctedChenZ N * ((1 + 1 / Real.log 1000) * (N : ℝ)) := by
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (threeOmegaDivisorSum_siftingProduct_le_sixPowZ N)
      (by positivity : 0 ≤ (1 + 1 / Real.log 1000) * (N : ℝ))
  have hz : correctedChenZ N ≤ correctedChenZ x₀ := correctedChenZ_le_of_le N x₀ hNx
  have h6z : (6 : ℝ) ^ correctedChenZ N * ((1 + 1 / Real.log 1000) * (N : ℝ)) ≤
      (6 : ℝ) ^ correctedChenZ x₀ * ((1 + 1 / Real.log 1000) * (N : ℝ)) := by
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : 1 ≤ (6 : ℝ)) hz)
      (by positivity : 0 ≤ (1 + 1 / Real.log 1000) * (N : ℝ))
  exact le_trans hsum (le_trans h6 h6z)

/-- **The `a = 1` base-count bridge**: the delta-weight instance of the classical weighted Pan
mean-value theorem, together with the support/truncation input, implies `ChenWeightedPanInput` for the current sieve.
This theorem does not identify this remainder with Liu's general-`f` paper `R`.
The reduction `correctedChenPanSum_reduction` gives Chen's remainder sum
`Σ_d 3^{ω(d)}|rem d| ≤ PanSum + Trunc`. The term `PanSum` is controlled by `hpan`
(`PanMeanValueUniform`), while `Trunc` is controlled by `htrunc`
(`CorrectedChenPanTruncationInput`); the finite range `N < x₀` is absorbed using the trivial bound.
The source-faithful assembly is
`PanMeanValueUniform.of_sourceFaithfulSignedInputs`, which explicitly takes
`PanSourceFaithfulSignedMainBound`; the exact signed pointwise decomposition is already proved in AnalyticNumberTheory.
Here only the statement `PanMeanValueUniform` is used directly. -/
theorem correctedChenPanInput_of_panMeanValueUniform
    (hpan : AnalyticNumberTheory.Sieve.PanMeanValueUniform (fun N : ℕ => (N : ℝ)) chenPanWeightOne)
    (htrunc : CorrectedChenPanTruncationInput) :
    ChenWeightedPanInput := by
  intro A hA
  rcases hpan A hA with ⟨Cpan, hCpan, Bpan, x₀pan, hpanN⟩
  rcases htrunc A hA Bpan with ⟨Ctr, hCtr, x₀tr, htruncN⟩
  let x₀ : ℕ := max x₀pan x₀tr
  let z₀ : ℕ := max 2 (Nat.floor ((x₀ : ℝ) ^ (1 / 10 : ℝ)))
  let Csmall : ℝ := (6 : ℝ) ^ z₀ * (1 + 1 / Real.log 1000) * (Real.log (x₀ : ℝ)) ^ A
  let C : ℝ := Cpan + Ctr + Csmall
  refine ⟨C, ?_, ?_⟩
  · have hz₀ : 0 ≤ (6 : ℝ) ^ z₀ := by positivity
    have hc : 0 ≤ 1 + 1 / Real.log 1000 := by
      have hlog1000 : 0 < Real.log 1000 := Real.log_pos (by norm_num : (1 : ℝ) < (1000 : ℝ))
      positivity
    have hlogx₀ : 0 ≤ (Real.log (x₀ : ℝ)) ^ A := by
      apply Real.rpow_nonneg
      by_cases h : (x₀ : ℕ) = 0
      · simp [h, Real.log_zero, Real.zero_rpow (ne_of_gt hA)]
      · have hx₀ : 1 ≤ (x₀ : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero h))
        exact Real.log_nonneg hx₀
    have hcs : 0 ≤ Csmall := by
      dsimp [Csmall]
      exact mul_nonneg (mul_nonneg hz₀ hc) hlogx₀
    dsimp [C]
    nlinarith
  · intro N hN1000 hEven
    by_cases hbig : x₀ ≤ N
    · have hred := correctedChenPanSum_reduction N hN1000 Bpan
      have hpanN' : (∑ q ∈ Finset.range (Nat.floor ((N : ℝ) ^ (1 / 2 : ℝ) / (log (N : ℝ)) ^ Bpan) + 1),
            ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
              AnalyticNumberTheory.Sieve.panMaxY N q (Nat.floor (N : ℝ)) chenPanWeightOne) ≤
          Cpan * (N : ℝ) / (log (N : ℝ)) ^ A := by
        exact hpanN N (le_trans (le_max_left x₀pan x₀tr) hbig)
      have htruncN' : (∑ d ∈ (correctedChenSiftingProduct N).divisors,
            (3 : ℝ) ^ d.primeFactors.card *
              |(correctedChenBoundingSieve N).rem d -
                AnalyticNumberTheory.Sieve.panDistributionError (N - 2) 1 d (N % d)|) +
            (∑ d ∈ (correctedChenSiftingProduct N).divisors.filter (fun d =>
                ¬ (2 ≤ d ∧ d ≤ Nat.floor ((N : ℝ) ^ (1 / 2 : ℝ) / (log (N : ℝ)) ^ Bpan))),
              (3 : ℝ) ^ d.primeFactors.card *
                |AnalyticNumberTheory.Sieve.panDistributionError (N - 2) 1 d (N % d)|) ≤
          Ctr * (N : ℝ) / (log (N : ℝ)) ^ A := by
        exact htruncN N (le_trans (le_max_right x₀pan x₀tr) hbig) hEven
      have hbound : AnalyticNumberTheory.Sieve.weightedPanRemainder (correctedChenBoundingSieve N)
            (fun d => (3 : ℝ) ^ d.primeFactors.card) ≤ C * (N : ℝ) / (log (N : ℝ)) ^ A := by
        calc
          AnalyticNumberTheory.Sieve.weightedPanRemainder (correctedChenBoundingSieve N)
              (fun d => (3 : ℝ) ^ d.primeFactors.card)
              = (∑ d ∈ (correctedChenSiftingProduct N).divisors,
                  (3 : ℝ) ^ d.primeFactors.card * |(correctedChenBoundingSieve N).rem d|) := by
                  rfl
          _ ≤ (∑ q ∈ Finset.range (Nat.floor ((N : ℝ) ^ (1 / 2 : ℝ) / (log (N : ℝ)) ^ Bpan) + 1),
                  ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
                    AnalyticNumberTheory.Sieve.panMaxY N q (Nat.floor (N : ℝ)) chenPanWeightOne) +
                (∑ d ∈ (correctedChenSiftingProduct N).divisors,
                  (3 : ℝ) ^ d.primeFactors.card *
                    |(correctedChenBoundingSieve N).rem d -
                      AnalyticNumberTheory.Sieve.panDistributionError (N - 2) 1 d (N % d)|) +
                (∑ d ∈ (correctedChenSiftingProduct N).divisors.filter (fun d =>
                    ¬ (2 ≤ d ∧ d ≤ Nat.floor ((N : ℝ) ^ (1 / 2 : ℝ) / (log (N : ℝ)) ^ Bpan))),
                  (3 : ℝ) ^ d.primeFactors.card *
                    |AnalyticNumberTheory.Sieve.panDistributionError (N - 2) 1 d (N % d)|) := hred
          _ ≤ Cpan * (N : ℝ) / (log (N : ℝ)) ^ A + Ctr * (N : ℝ) / (log (N : ℝ)) ^ A := by
                nlinarith [hpanN', htruncN']
          _ = (Cpan + Ctr) * (N : ℝ) / (log (N : ℝ)) ^ A := by ring
          _ ≤ C * (N : ℝ) / (log (N : ℝ)) ^ A := by
                have hcs : 0 ≤ Csmall := by
                  have hz₀ : 0 ≤ (6 : ℝ) ^ z₀ := by positivity
                  have hc : 0 ≤ 1 + 1 / Real.log 1000 := by
                    have hlog1000 : 0 < Real.log 1000 := Real.log_pos (by norm_num : (1 : ℝ) < (1000 : ℝ))
                    positivity
                  have hlogx₀ : 0 ≤ (Real.log (x₀ : ℝ)) ^ A := by
                    apply Real.rpow_nonneg
                    by_cases h : (x₀ : ℕ) = 0
                    · simp [h, Real.log_zero, Real.zero_rpow (ne_of_gt hA)]
                    · exact Real.log_nonneg (by exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero h)))
                  dsimp [Csmall]
                  exact mul_nonneg (mul_nonneg hz₀ hc) hlogx₀
                have hcle : Cpan + Ctr ≤ C := by
                  dsimp [C]
                  nlinarith
                have hNdiv : 0 ≤ (N : ℝ) / (log (N : ℝ)) ^ A := by
                  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
                  exact div_nonneg (by positivity : 0 ≤ (N : ℝ)) (Real.rpow_nonneg hlogN0 A)
                have hle2 : (Cpan + Ctr) * ((N : ℝ) / (log (N : ℝ)) ^ A) ≤ C * ((N : ℝ) / (log (N : ℝ)) ^ A) :=
                  mul_le_mul_of_nonneg_right hcle hNdiv
                simpa [div_eq_mul_inv, mul_assoc] using hle2
      exact hbound
    · have hNlt : N < x₀ := by omega
      have hNle : N ≤ x₀ := by omega
      have hsmall := correctedChenPanSum_small_bound N x₀ hN1000 hNle
      have hz₀ : (6 : ℝ) ^ correctedChenZ x₀ = (6 : ℝ) ^ z₀ := rfl
      have hmain : (6 : ℝ) ^ correctedChenZ x₀ * ((1 + 1 / Real.log 1000) * (N : ℝ)) ≤
          C * (N : ℝ) / (log (N : ℝ)) ^ A := by
        have hlog1000 : 0 < Real.log 1000 := Real.log_pos (by norm_num : (1 : ℝ) < (1000 : ℝ))
        have hcpos : 0 < 1 + 1 / Real.log 1000 := by positivity
        have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
        have hlogN0 : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
        have hlogx0 : 0 < Real.log (x₀ : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x₀))
        have hpowle : (Real.log (N : ℝ)) ^ A ≤ (Real.log (x₀ : ℝ)) ^ A :=
          Real.rpow_le_rpow (le_of_lt hlogN0) (Real.log_le_log hNpos (by exact_mod_cast hNle)) (le_of_lt hA)
        have hb : 1 ≤ (Real.log (x₀ : ℝ)) ^ A / (Real.log (N : ℝ)) ^ A := by
          rw [le_div_iff₀ (Real.rpow_pos_of_pos hlogN0 A)]
          simpa using hpowle
        calc
          (6 : ℝ) ^ correctedChenZ x₀ * ((1 + 1 / Real.log 1000) * (N : ℝ))
              = (6 : ℝ) ^ z₀ * ((1 + 1 / Real.log 1000) * (N : ℝ)) := by rw [hz₀]
          _ = (6 : ℝ) ^ z₀ * (1 + 1 / Real.log 1000) * (N : ℝ) := by ring
          _ = (6 : ℝ) ^ z₀ * (1 + 1 / Real.log 1000) * (N : ℝ) * 1 := by ring
          _ ≤ (6 : ℝ) ^ z₀ * (1 + 1 / Real.log 1000) * (N : ℝ) *
                ((Real.log (x₀ : ℝ)) ^ A / (Real.log (N : ℝ)) ^ A) := by
                have hnon : 0 ≤ (6 : ℝ) ^ z₀ * (1 + 1 / Real.log 1000) * (N : ℝ) := by positivity
                exact mul_le_mul_of_nonneg_left hb hnon
          _ = Csmall * (N : ℝ) / (log (N : ℝ)) ^ A := by
                dsimp [Csmall]
                ring
          _ ≤ C * (N : ℝ) / (log (N : ℝ)) ^ A := by
                have hcs : 0 ≤ Csmall := by
                  have hz₀n : 0 ≤ (6 : ℝ) ^ z₀ := by positivity
                  have hcn : 0 ≤ 1 + 1 / Real.log 1000 := le_of_lt hcpos
                  have hlogx₀n : 0 ≤ (Real.log (x₀ : ℝ)) ^ A := le_of_lt (Real.rpow_pos_of_pos hlogx0 A)
                  dsimp [Csmall]
                  exact mul_nonneg (mul_nonneg hz₀n hcn) hlogx₀n
                have hcle : Csmall ≤ C := by
                  dsimp [C]
                  nlinarith [hCpan, hCtr, hcs]
                have hNdiv : 0 ≤ (N : ℝ) / (log (N : ℝ)) ^ A := by
                  exact div_nonneg (le_of_lt hNpos) (Real.rpow_nonneg (le_of_lt hlogN0) A)
                have hle2 : Csmall * ((N : ℝ) / (log (N : ℝ)) ^ A) ≤ C * ((N : ℝ) / (log (N : ℝ)) ^ A) :=
                  mul_le_mul_of_nonneg_right hcle hNdiv
                simpa [div_eq_mul_inv, mul_assoc] using hle2
      have hbound : AnalyticNumberTheory.Sieve.weightedPanRemainder (correctedChenBoundingSieve N)
            (fun d => (3 : ℝ) ^ d.primeFactors.card) ≤ C * (N : ℝ) / (log (N : ℝ)) ^ A := by
        calc
          AnalyticNumberTheory.Sieve.weightedPanRemainder (correctedChenBoundingSieve N)
              (fun d => (3 : ℝ) ^ d.primeFactors.card)
              = ∑ d ∈ (correctedChenSiftingProduct N).divisors,
                  (3 : ℝ) ^ d.primeFactors.card * |(correctedChenBoundingSieve N).rem d| := by
                  rfl
          _ ≤ (6 : ℝ) ^ correctedChenZ x₀ * ((1 + 1 / Real.log 1000) * (N : ℝ)) := hsmall
          _ ≤ C * (N : ℝ) / (log (N : ℝ)) ^ A := hmain
      exact hbound

/-- **Source-faithful Pan wrapper**:
`PanMeanValueUniform.of_sourceFaithfulSignedInputs` combines two character mean-value bounds,
the signed-main inverse-log bound with explicit `u,v`, the proved logarithmic growth estimate,
and `δ₁(0)=0` into `PanMeanValueUniform`. Adding support truncation yields `ChenWeightedPanInput`.
The exact signed pointwise decomposition is an internal theorem of AnalyticNumberTheory, not a hypothesis;
the paper's `R₁` and `PanSourceFaithfulSignedMainBound` remain open inputs. -/
theorem chenPanInput_of_sourceFaithfulSignedInputs
    {u v : ℕ}
    (hI : AnalyticNumberTheory.Sieve.PanTypeICharacterMeanValue
      (fun N : ℕ => (N : ℝ)) chenPanWeightOne u)
    (hII : AnalyticNumberTheory.Sieve.PanTypeIICharacterMeanValue
      (fun N : ℕ => (N : ℝ)) chenPanWeightOne u v)
    (hM : AnalyticNumberTheory.Sieve.PanSourceFaithfulSignedMainBound
      (fun N : ℕ => (N : ℝ)) chenPanWeightOne u v)
    (htrunc : CorrectedChenPanTruncationInput) :
    ChenWeightedPanInput := by
  exact correctedChenPanInput_of_panMeanValueUniform
    (AnalyticNumberTheory.Sieve.PanMeanValueUniform.of_sourceFaithfulSignedInputs
      hI hII hM AnalyticNumberTheory.Sieve.panLogEventuallyLarge_natCast
      (by simp [chenPanWeightOne]))
    htrunc

/-- The corrected candidate count is at least the lower-sieve main term minus
the explicit `errSum`: the finite seam through which a uniform
Jurkat--Richert lower bound for `mainSum μ⁻` (with the closed `N / log N`
total mass) proves `CorrectedChenAnalyticPositivity`. -/
theorem correctedChenCandidates_card_ge_mainSum_sub_errSum (N : ℕ)
    (muMinus : ℕ → ℝ) (hmu : AnalyticNumberTheory.Sieve.IsLowerMoebius muMinus) :
    (correctedChenBoundingSieve N).totalMass *
        (correctedChenBoundingSieve N).mainSum muMinus -
      (correctedChenBoundingSieve N).errSum muMinus ≤
      (correctedChenCandidates N).card := by
  calc
    (correctedChenBoundingSieve N).totalMass *
          (correctedChenBoundingSieve N).mainSum muMinus -
        (correctedChenBoundingSieve N).errSum muMinus
        ≤ (correctedChenBoundingSieve N).siftedSum :=
          AnalyticNumberTheory.Sieve.mainSum_sub_errSum_le_siftedSum_of_lowerMoebius
            muMinus hmu
    _ = (correctedChenCandidates N).card :=
      correctedChenBoundingSieve_siftedSum_eq_card N

end MathlibNt.SieveTheory.SwitchingPrinciple
