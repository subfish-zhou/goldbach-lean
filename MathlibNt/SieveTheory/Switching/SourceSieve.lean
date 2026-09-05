import MathlibNt.SieveTheory.Switching.WeightedCounting

/-!
# Source sieve carriers and Jurkat--Richert factors

The literal source cutoffs define sieve carriers and arithmetic-progression
remainders, including exceptional endpoints. Conditioned carriers and explicit
upper linear-sieve factors retain their precise boundary conventions.

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

/-- The distinct-medium-prime count in Chen's Lemma 9.  Each prime
`q ∈ [correctedChenZ N, correctedChenY N)` dividing `N - p` contributes once,
regardless of its valuation. -/
noncomputable def jurkatRichertDistinctWeightedCount (N : ℕ) : ℝ :=
  ((correctedChenCandidates N).card : ℝ) - correctedChenQ1Count N / 2

/-- Chen's literal `P_N(N, N^(1/10))` carrier: primes `p ≤ N` for which no odd
prime through the real cutoff `N^(1/10)` divides `N - p`. -/
noncomputable def jurkatRichertSourceCandidates (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun p =>
    p.Prime ∧ ∀ r : ℕ, r.Prime → 2 < r →
      (r : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ¬r ∣ N - p)

/-- The integer endpoint whose strict range is Chen's literal real cutoff
`r ≤ N^(1/10)`. -/
noncomputable def jurkatRichertSourceZ (N : ℕ) : ℕ :=
  Nat.floor ((N : ℝ) ^ (1 / 10 : ℝ)) + 1

/-- Odd cutoff primes not dividing `N`; these are the primes treated by the
Goldbach density `1 / (p - 1)`. -/
noncomputable def jurkatRichertSourceSiftingProduct (N : ℕ) : ℕ :=
  ((Finset.range (jurkatRichertSourceZ N)).filter
    (fun r => r.Prime ∧ 2 < r ∧ ¬r ∣ N)).prod id

theorem jurkatRichertSourceSiftingProduct_squarefree (N : ℕ) :
    Squarefree (jurkatRichertSourceSiftingProduct N) := by
  unfold jurkatRichertSourceSiftingProduct
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · rintro p hp q hq hpq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hp hq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes hp.2.1 hq.2.1).mpr hpq)
  · intro p hp
    exact (Finset.mem_filter.mp hp).2.1.squarefree

theorem jurkatRichertSourceSiftingProduct_ne_zero (N : ℕ) :
    jurkatRichertSourceSiftingProduct N ≠ 0 := by
  unfold jurkatRichertSourceSiftingProduct
  exact ne_of_gt (Finset.prod_pos (by
    intro r hr
    exact (Finset.mem_filter.mp hr).2.1.pos))

theorem jurkatRichertSourceSiftingProduct_primeFactors (N : ℕ) :
    (jurkatRichertSourceSiftingProduct N).primeFactors =
      (Finset.range (jurkatRichertSourceZ N)).filter
        (fun r => r.Prime ∧ 2 < r ∧ ¬r ∣ N) := by
  unfold jurkatRichertSourceSiftingProduct
  exact primeFactors_prod_eq_self (by
    intro p hp
    exact (Finset.mem_filter.mp hp).2.1)

theorem prime_dvd_jurkatRichertSourceSiftingProduct {N r : ℕ}
    (hr : r.Prime) :
    r ∣ jurkatRichertSourceSiftingProduct N ↔
      2 < r ∧ (r : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) ∧ ¬r ∣ N := by
  constructor
  · intro hrDvd
    have hrMem :
        r ∈ (jurkatRichertSourceSiftingProduct N).primeFactors :=
      (Nat.mem_primeFactors_of_ne_zero
        (jurkatRichertSourceSiftingProduct_ne_zero N)).mpr ⟨hr, hrDvd⟩
    rw [jurkatRichertSourceSiftingProduct_primeFactors, Finset.mem_filter,
      Finset.mem_range] at hrMem
    rcases hrMem with ⟨hrz, _, hr2, hrN⟩
    refine ⟨hr2, ?_, hrN⟩
    change r < Nat.floor ((N : ℝ) ^ (1 / 10 : ℝ)) + 1 at hrz
    have hrFloor : r ≤ Nat.floor ((N : ℝ) ^ (1 / 10 : ℝ)) := by omega
    have hrFloor' :
        (r : ℝ) ≤ (Nat.floor ((N : ℝ) ^ (1 / 10 : ℝ)) : ℝ) := by
      exact_mod_cast hrFloor
    exact hrFloor'.trans (Nat.floor_le (by positivity))
  · rintro ⟨hr2, hrz, hrN⟩
    have hfloor : r ≤ Nat.floor ((N : ℝ) ^ (1 / 10 : ℝ)) :=
      Nat.le_floor hrz
    have hrMem :
        r ∈ (jurkatRichertSourceSiftingProduct N).primeFactors := by
      rw [jurkatRichertSourceSiftingProduct_primeFactors, Finset.mem_filter,
        Finset.mem_range]
      exact ⟨by
        change r < Nat.floor ((N : ℝ) ^ (1 / 10 : ℝ)) + 1
        omega, hr, hr2, hrN⟩
    exact (Nat.mem_primeFactors_of_ne_zero
      (jurkatRichertSourceSiftingProduct_ne_zero N)).mp hrMem |>.2

/-- Before the Goldbach sieve, primes whose complement is divisible by an odd
cutoff prime dividing `N` are removed.  Such a prime is the exceptional prime
itself; separating it is what makes every remaining local density
`1 / (r - 1)`. -/
noncomputable def jurkatRichertSourceUnsiftedPrimeSupport (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun p =>
    p.Prime ∧ ∀ r : ℕ, r.Prime → 2 < r →
      (r : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → r ∣ N → ¬r ∣ N - p)

/-- The source Goldbach sequence `A = {N - p : p ≤ N, p prime}`, after only
the exceptional residue-zero cutoff primes have been removed. -/
noncomputable def jurkatRichertSourceUnsiftedComplements (N : ℕ) : Finset ℕ :=
  (jurkatRichertSourceUnsiftedPrimeSupport N).image (fun p => N - p)

/-- Chen's literal base sequence as a `BoundingSieve`. -/
noncomputable def jurkatRichertSourceBoundingSieve (N : ℕ) : BoundingSieve where
  support := jurkatRichertSourceUnsiftedComplements N
  prodPrimes := jurkatRichertSourceSiftingProduct N
  prodPrimes_squarefree := jurkatRichertSourceSiftingProduct_squarefree N
  weights := fun _ => 1
  weights_nonneg := by intro n; norm_num
  totalMass := LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N
  nu := AnalyticNumberTheory.Sieve.goldbachNu
  nu_mult := AnalyticNumberTheory.Sieve.goldbachNu_isMultiplicative
  nu_pos_of_prime := by
    intro p hp _
    exact AnalyticNumberTheory.Sieve.goldbachNu_pos_of_prime hp
  nu_lt_one_of_prime := by
    intro p hp hdiv
    have hp2 :=
      (prime_dvd_jurkatRichertSourceSiftingProduct hp).mp hdiv |>.1
    exact AnalyticNumberTheory.Sieve.goldbachNu_lt_one_of_prime hp hp2

/-- The source support survives the remaining odd-prime sieve exactly when its
prime partner belongs to Chen's literal carrier. -/
theorem jurkatRichertSourceSiftedComplements_eq_candidate_image (N : ℕ) :
    (jurkatRichertSourceUnsiftedComplements N).filter
        (fun a => Nat.Coprime (jurkatRichertSourceSiftingProduct N) a) =
      (jurkatRichertSourceCandidates N).image (fun p => N - p) := by
  ext a
  constructor
  · intro ha
    rcases Finset.mem_filter.mp ha with ⟨haSupport, haCoprime⟩
    rcases Finset.mem_image.mp haSupport with ⟨p, hpSupport, rfl⟩
    rcases Finset.mem_filter.mp hpSupport with ⟨hpRange, hpPrime, hpExceptional⟩
    refine Finset.mem_image.mpr ⟨p, ?_, rfl⟩
    refine Finset.mem_filter.mpr ⟨hpRange, hpPrime, ?_⟩
    intro r hrPrime hr2 hrCutoff hrDvd
    by_cases hrN : r ∣ N
    · exact hpExceptional r hrPrime hr2 hrCutoff hrN hrDvd
    · have hrProduct : r ∣ jurkatRichertSourceSiftingProduct N :=
        (prime_dvd_jurkatRichertSourceSiftingProduct hrPrime).mpr
          ⟨hr2, hrCutoff, hrN⟩
      exact Nat.not_coprime_of_dvd_of_dvd hrPrime.one_lt hrProduct hrDvd haCoprime
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨p, hpCandidate, rfl⟩
    rcases Finset.mem_filter.mp hpCandidate with ⟨hpRange, hpPrime, hpSifted⟩
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr
        ⟨hpRange, hpPrime, fun r hrPrime hr2 hrCutoff _ =>
          hpSifted r hrPrime hr2 hrCutoff⟩, rfl⟩
    · apply Nat.coprime_of_dvd'
      intro r hrPrime hrProduct hrDvd
      rcases (prime_dvd_jurkatRichertSourceSiftingProduct hrPrime).mp hrProduct with
        ⟨hr2, hrCutoff, _⟩
      exact (hpSifted r hrPrime hr2 hrCutoff hrDvd).elim

/-- Exact finite identification of the source `BoundingSieve` with
`P_N(N, N^(1/10))`.  The range is `p ≤ N`; hence both `p = 2` and the unit
complement `N - p = 1` are retained exactly when the literal source admits
them. -/
theorem jurkatRichertSourceBoundingSieve_siftedSum_eq_card (N : ℕ) :
    (jurkatRichertSourceBoundingSieve N).siftedSum =
      (jurkatRichertSourceCandidates N).card := by
  change (∑ a ∈ jurkatRichertSourceUnsiftedComplements N,
      if Nat.Coprime (jurkatRichertSourceSiftingProduct N) a then (1 : ℝ) else 0) =
    ((jurkatRichertSourceCandidates N).card : ℝ)
  rw [Finset.sum_boole, jurkatRichertSourceSiftedComplements_eq_candidate_image]
  have hcard :
      ((jurkatRichertSourceCandidates N).image (fun p => N - p)).card =
        (jurkatRichertSourceCandidates N).card :=
    Finset.card_image_of_injOn (s := jurkatRichertSourceCandidates N)
      (f := fun p => N - p) (by
      intro p hp q hq hpq
      have hpN : p ≤ N := by
        simpa [jurkatRichertSourceCandidates] using
          (Finset.mem_filter.mp hp).1
      have hqN : q ≤ N := by
        simpa [jurkatRichertSourceCandidates] using
          (Finset.mem_filter.mp hq).1
      change N - p = N - q at hpq
      omega)
  exact_mod_cast hcard

/-- For even `N`, the source sieve product is the standard Goldbach product at
the literal real cutoff.  Equation (25), not equation (26), supplies the
Mertens normalization of this product. -/
theorem jurkatRichertSourceSieveProduct_eq_goldbachSieveProduct
    (N : ℕ) (hEven : Even N) :
    AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
        (jurkatRichertSourceBoundingSieve N) =
      MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) := by
  unfold AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
    MertensTheorem.goldbachSieveProduct
  change (∏ p ∈ (jurkatRichertSourceSiftingProduct N).primeFactors,
      (1 - AnalyticNumberTheory.Sieve.goldbachNu p)) =
    ∏ p ∈ (Finset.range (jurkatRichertSourceZ N)).filter
      (fun p => p.Prime ∧ ¬p ∣ N), (1 - 1 / ((p : ℝ) - 1))
  rw [jurkatRichertSourceSiftingProduct_primeFactors]
  have hset :
      (Finset.range (jurkatRichertSourceZ N)).filter
          (fun p => p.Prime ∧ ¬p ∣ N) =
        (Finset.range (jurkatRichertSourceZ N)).filter
          (fun p => p.Prime ∧ 2 < p ∧ ¬p ∣ N) := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpRange, hpPrime, hpN⟩
      refine Finset.mem_filter.mpr ⟨hpRange, hpPrime, ?_, hpN⟩
      have hpNeTwo : p ≠ 2 := by
        intro hpTwo
        apply hpN
        subst p
        exact even_iff_two_dvd.mp hEven
      have hpTwoLe : 2 ≤ p := hpPrime.two_le
      omega
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpRange, hpPrime, _, hpN⟩
      exact Finset.mem_filter.mpr ⟨hpRange, hpPrime, hpN⟩
  rw [hset]
  apply Finset.prod_congr rfl
  intro p hp
  rw [AnalyticNumberTheory.Sieve.goldbachNu_apply_prime
    (Finset.mem_filter.mp hp).2.1]

/-- Multiples in the source complement support are counted by their unique
prime partners. -/
theorem jurkatRichertSourceMultiples_card_eq_primeSupport (N d : ℕ) :
    ((jurkatRichertSourceUnsiftedComplements N).filter
        (fun a => d ∣ a)).card =
      ((jurkatRichertSourceUnsiftedPrimeSupport N).filter
        (fun p => d ∣ N - p)).card := by
  unfold jurkatRichertSourceUnsiftedComplements
  rw [Finset.filter_image]
  apply Finset.card_image_of_injOn
  intro p hp q hq hpq
  have hpSupport := (Finset.mem_filter.mp hp).1
  have hqSupport := (Finset.mem_filter.mp hq).1
  have hpN : p ≤ N := by
    have := (Finset.mem_filter.mp hpSupport).1
    simpa using this
  have hqN : q ≤ N := by
    have := (Finset.mem_filter.mp hqSupport).1
    simpa using this
  change N - p = N - q at hpq
  omega

/-- On even `N > 2`, the source sieve `multSum` is exactly the Goldbach
arithmetic-progression count `p ≡ N (mod d)`.  The `p ≤ N` endpoint causes no
exception because such an `N` is not prime. -/
theorem jurkatRichertSourceMultSum_eq_modEq_count
    (N d : ℕ) (hEven : Even N) (hN : 2 < N) :
    (jurkatRichertSourceBoundingSieve N).multSum d =
      (((jurkatRichertSourceUnsiftedPrimeSupport N).filter
        (fun p => p ≡ N [MOD d])).card : ℝ) := by
  unfold BoundingSieve.multSum
  change (∑ a ∈ jurkatRichertSourceUnsiftedComplements N,
      if d ∣ a then (1 : ℝ) else 0) =
    (((jurkatRichertSourceUnsiftedPrimeSupport N).filter
      (fun p => p ≡ N [MOD d])).card : ℝ)
  rw [Finset.sum_boole, jurkatRichertSourceMultiples_card_eq_primeSupport]
  apply congrArg (fun s : Finset ℕ => (s.card : ℝ))
  apply Finset.filter_congr
  intro p hp
  have hpData := Finset.mem_filter.mp hp
  have hpLe : p ≤ N := by
    simpa using hpData.1
  have hpPrime : p.Prime := hpData.2.1
  have hpLt : p < N := by
    apply lt_of_le_of_ne hpLe
    intro hpEq
    have hNPrime : N.Prime := hpEq ▸ hpPrime
    have hN2 : N = 2 := hNPrime.even_iff.mp hEven
    omega
  exact AnalyticNumberTheory.Sieve.prime_dvd_complement_iff_modEq hpLt

/-- The source sieve remainder is the exact Goldbach AP discrepancy. -/
theorem jurkatRichertSourceRem_eq_modEq_count
    (N d : ℕ) (hEven : Even N) (hN : 2 < N) :
    (jurkatRichertSourceBoundingSieve N).rem d =
      (((jurkatRichertSourceUnsiftedPrimeSupport N).filter
          (fun p => p ≡ N [MOD d])).card : ℝ) -
        AnalyticNumberTheory.Sieve.goldbachNu d *
        LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N := by
  unfold BoundingSieve.rem
  rw [jurkatRichertSourceMultSum_eq_modEq_count N d hEven hN]
  rfl

/-- The level-restricted Goldbach remainder sum used by the source lower sieve.
Only squarefree divisors of the odd cutoff product with
`d ≤ N^(1/2-ε)` occur. -/
noncomputable def jurkatRichertSourceRemainderSum (N : ℕ) (ε : ℝ) : ℝ :=
  ∑ d ∈ (jurkatRichertSourceSiftingProduct N).divisors.filter
      (fun d : ℕ => (d : ℝ) ≤ (N : ℝ) ^ (1 / 2 - ε)),
    |(jurkatRichertSourceBoundingSieve N).rem d|

/-- The level-restricted remainder is literally a sum of Goldbach AP
discrepancies. -/
theorem jurkatRichertSourceRemainderSum_eq_AP
    (N : ℕ) (ε : ℝ) (hEven : Even N) (hN : 2 < N) :
    jurkatRichertSourceRemainderSum N ε =
      ∑ d ∈ (jurkatRichertSourceSiftingProduct N).divisors.filter
          (fun d : ℕ => (d : ℝ) ≤ (N : ℝ) ^ (1 / 2 - ε)),
        |(((jurkatRichertSourceUnsiftedPrimeSupport N).filter
              (fun p => p ≡ N [MOD d])).card : ℝ) -
          AnalyticNumberTheory.Sieve.goldbachNu d *
            LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N| := by
  unfold jurkatRichertSourceRemainderSum
  apply Finset.sum_congr rfl
  intro d hd
  rw [jurkatRichertSourceRem_eq_modEq_count N d hEven hN]

/-- Every source modulus is coprime to the Goldbach integer: the source
product omits precisely the cutoff primes dividing `N`. -/
theorem jurkatRichertSourceSiftingProduct_coprime_N (N : ℕ) :
    Nat.Coprime (jurkatRichertSourceSiftingProduct N) N := by
  apply Nat.coprime_of_dvd'
  intro r hr hrP hrN
  rcases (prime_dvd_jurkatRichertSourceSiftingProduct hr).mp hrP with
    ⟨_, _, hrN'⟩
  exact False.elim (hrN' hrN)

/-- On the squarefree source-divisor carrier the Goldbach local density is
exactly the reduced-residue density `1 / φ(d)`. -/
theorem jurkatRichertSource_goldbachNu_eq_inv_totient {N d : ℕ}
    (hd : d ∣ jurkatRichertSourceSiftingProduct N) :
    AnalyticNumberTheory.Sieve.goldbachNu d = (1 : ℝ) / Nat.totient d := by
  exact AnalyticNumberTheory.Sieve.goldbachNu_squarefree_eq_inv_totient
    (BoundingSieve.squarefree_of_dvd_prodPrimes
      (s := jurkatRichertSourceBoundingSieve N) hd)

/-- The residue `N mod d` is a canonical reduced residue for every source
modulus, including the canonical residue `0` at `d = 1`. -/
theorem jurkatRichertSource_mod_coprime {N d : ℕ}
    (hd : d ∣ jurkatRichertSourceSiftingProduct N) :
    (N % d).Coprime d := by
  have hd0 : d ≠ 0 := by
    intro hd0
    subst d
    have hP0 : jurkatRichertSourceSiftingProduct N = 0 := by simpa using hd
    exact jurkatRichertSourceSiftingProduct_ne_zero N hP0
  have hPN : Nat.Coprime (jurkatRichertSourceSiftingProduct N) N :=
    jurkatRichertSourceSiftingProduct_coprime_N N
  have hdN : Nat.Coprime d N := Nat.Coprime.coprime_dvd_left hd hPN
  apply Nat.coprime_of_dvd'
  intro k hk hk1 hk2
  have hkN : k ∣ N := by
    have hkdiv : k ∣ d * (N / d) + N % d :=
      Nat.dvd_add
        (by simpa [mul_comm] using (dvd_mul_of_dvd_right hk2 (N / d))) hk1
    have hNdef : d * (N / d) + N % d = N := by
      simpa [Nat.add_comm] using (Nat.mod_add_div N d)
    rw [← hNdef]
    exact hkdiv
  exact False.elim
    (Nat.not_coprime_of_dvd_of_dvd (Nat.Prime.one_lt hk) hk2 hkN hdN)

/-- The finitely many prime partners removed before sifting: they are exactly
the odd cutoff primes already dividing `N`. -/
noncomputable def jurkatRichertSourceExceptionalPrimes (N : ℕ) : Finset ℕ :=
  (Finset.range (jurkatRichertSourceZ N)).filter
    (fun r => r.Prime ∧ 2 < r ∧ r ∣ N)

/-- Outside the source support, a standard prime can only be one of the
exceptional cutoff primes dividing `N`.  This is the finite correction that
must be retained when comparing the source AP count to standard primes. -/
theorem jurkatRichertSource_full_not_support_subset_exceptional (N : ℕ) :
    ((Finset.range (N + 1)).filter Nat.Prime \
      jurkatRichertSourceUnsiftedPrimeSupport N) ⊆
      jurkatRichertSourceExceptionalPrimes N := by
  intro p hp
  rcases Finset.mem_sdiff.mp hp with ⟨hpFull, hpNotSupport⟩
  rcases Finset.mem_filter.mp hpFull with ⟨hpRange, hpPrime⟩
  have hnot : ¬ ∀ r : ℕ, r.Prime → 2 < r →
      (r : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → r ∣ N → ¬r ∣ N - p := by
    intro hall
    apply hpNotSupport
    exact Finset.mem_filter.mpr ⟨hpRange, hpPrime, hall⟩
  push Not at hnot
  rcases hnot with ⟨r, hrPrime, hrTwo, hrCutoff, hrN, hrComplement⟩
  have hpLe : p ≤ N := by
    simpa [Finset.mem_range] using hpRange
  have hmod : p ≡ N [MOD r] :=
    (Nat.modEq_iff_dvd' hpLe).mpr hrComplement
  have hrp : r ∣ p := (hmod.dvd_iff (dvd_refl r)).mpr hrN
  rcases (Nat.dvd_prime hpPrime).mp hrp with hrOne | hrEq
  · exact (hrPrime.ne_one hrOne).elim
  subst p
  unfold jurkatRichertSourceExceptionalPrimes
  refine Finset.mem_filter.mpr ⟨?_, hrPrime, hrTwo, hrN⟩
  unfold jurkatRichertSourceZ
  have hfloor : r ≤ Nat.floor ((N : ℝ) ^ (1 / 10 : ℝ)) :=
    Nat.le_floor hrCutoff
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le hfloor)

/-- Removing the exceptional source fibres changes every Goldbach AP count by
at most the total number of exceptional cutoff primes. -/
theorem jurkatRichertSource_AP_correction_le_exceptional (N d : ℕ) :
    (((Finset.range (N + 1)).filter
        (fun p => p.Prime ∧ p ≡ N [MOD d])).card : ℝ) -
      (((jurkatRichertSourceUnsiftedPrimeSupport N).filter
        (fun p => p ≡ N [MOD d])).card : ℝ) ≤
      (jurkatRichertSourceExceptionalPrimes N).card := by
  let F : Finset ℕ := (Finset.range (N + 1)).filter
    (fun p => p.Prime ∧ p ≡ N [MOD d])
  let S : Finset ℕ := (jurkatRichertSourceUnsiftedPrimeSupport N).filter
    (fun p => p ≡ N [MOD d])
  let E : Finset ℕ := jurkatRichertSourceExceptionalPrimes N
  have hSF : S ⊆ F := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpS, hpMod⟩
    rcases Finset.mem_filter.mp hpS with ⟨hpRange, hpPrime, _⟩
    exact Finset.mem_filter.mpr ⟨hpRange, hpPrime, hpMod⟩
  have hdiff : F \ S ⊆ E := by
    intro p hp
    apply jurkatRichertSource_full_not_support_subset_exceptional N
    rcases Finset.mem_sdiff.mp hp with ⟨hpF, hpNotS⟩
    rcases Finset.mem_filter.mp hpF with ⟨hpRange, hpPrime, _⟩
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hpRange, hpPrime⟩, ?_⟩
    intro hpSupport
    apply hpNotS
    exact Finset.mem_filter.mpr ⟨hpSupport, (Finset.mem_filter.mp hpF).2.2⟩
  have hcard : F.card - S.card = (F \ S).card :=
    (Finset.card_sdiff_of_subset hSF).symm
  have hle : (F \ S).card ≤ E.card := Finset.card_le_card hdiff
  have hSFcard : S.card ≤ F.card := Finset.card_le_card hSF
  change (F.card : ℝ) - S.card ≤ E.card
  calc
    (F.card : ℝ) - S.card = ((F.card - S.card : ℕ) : ℝ) :=
      (Nat.cast_sub hSFcard).symm
    _ = ((F \ S).card : ℝ) := by rw [hcard]
    _ ≤ E.card := by exact_mod_cast hle

/-- The source AP discrepancy is bounded by the standard reduced-residue
discrepancy plus the honest exceptional-fibre correction. -/
theorem abs_jurkatRichertSource_AP_sub_trueLi_div_totient_le
    (N d : ℕ) :
    |(((jurkatRichertSourceUnsiftedPrimeSupport N).filter
          (fun p => p ≡ N [MOD d])).card : ℝ) -
        BombieriVinogradov.trueLogarithmicIntegral N / Nat.totient d| ≤
      |BombieriVinogradov.standardPrimeAPError N d (N % d)| +
        (jurkatRichertSourceExceptionalPrimes N).card := by
  let F : Finset ℕ := (Finset.range (N + 1)).filter
    (fun p => p.Prime ∧ p ≡ N [MOD d])
  let S : Finset ℕ := (jurkatRichertSourceUnsiftedPrimeSupport N).filter
    (fun p => p ≡ N [MOD d])
  let E : Finset ℕ := jurkatRichertSourceExceptionalPrimes N
  have hSF : S ⊆ F := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpS, hpMod⟩
    rcases Finset.mem_filter.mp hpS with ⟨hpRange, hpPrime, _⟩
    exact Finset.mem_filter.mpr ⟨hpRange, hpPrime, hpMod⟩
  have hSFcard : S.card ≤ F.card := Finset.card_le_card hSF
  have hcorrection : (F.card : ℝ) - S.card ≤ E.card := by
    simpa [F, S, E] using jurkatRichertSource_AP_correction_le_exceptional N d
  have hstandard :
      (F.card : ℝ) - BombieriVinogradov.trueLogarithmicIntegral N / Nat.totient d =
        BombieriVinogradov.standardPrimeAPError N d (N % d) := by
    rw [← BombieriVinogradov.primesInAP_modEq_N_eq]
    rfl
  have hrewrite :
      (S.card : ℝ) - BombieriVinogradov.trueLogarithmicIntegral N / Nat.totient d =
        ((F.card : ℝ) - BombieriVinogradov.trueLogarithmicIntegral N /
          Nat.totient d) - ((F.card : ℝ) - S.card) := by
    ring
  rw [hrewrite, hstandard]
  calc
    |BombieriVinogradov.standardPrimeAPError N d (N % d) -
        ((F.card : ℝ) - S.card)| ≤
      |BombieriVinogradov.standardPrimeAPError N d (N % d) - 0| +
        |0 - ((F.card : ℝ) - S.card)| :=
      abs_sub_le _ _ _
    _ = |BombieriVinogradov.standardPrimeAPError N d (N % d)| +
        ((F.card : ℝ) - S.card) := by
      have hDiff : 0 ≤ (F.card : ℝ) - S.card := by
        apply sub_nonneg.mpr
        exact_mod_cast hSFcard
      rw [sub_zero, zero_sub, abs_neg, abs_of_nonneg hDiff]
    _ ≤ |BombieriVinogradov.standardPrimeAPError N d (N % d)| + E.card :=
      by linarith

/-- The exact source sieve remainder is controlled by the standard prime-AP
error plus the retained exceptional-fibre correction. -/
theorem abs_jurkatRichertSource_rem_le_standardError_add_exceptional
    (N d : ℕ) (hEven : Even N) (hN : 2 < N)
    (hd : d ∣ jurkatRichertSourceSiftingProduct N) :
    |(jurkatRichertSourceBoundingSieve N).rem d| ≤
      |BombieriVinogradov.standardPrimeAPError N d (N % d)| +
        (jurkatRichertSourceExceptionalPrimes N).card := by
  rw [jurkatRichertSourceRem_eq_modEq_count N d hEven hN,
    jurkatRichertSource_goldbachNu_eq_inv_totient hd]
  have hmain :
      (1 : ℝ) / Nat.totient d *
          LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N =
        BombieriVinogradov.trueLogarithmicIntegral N / Nat.totient d := by
    simp only [BombieriVinogradov.trueLogarithmicIntegral, div_eq_mul_inv]
    ring
  rw [hmain]
  exact abs_jurkatRichertSource_AP_sub_trueLi_div_totient_le N d

/-- Before any asymptotics, the source remainder sum splits into the standard
BV maximum on its divisor carrier and the explicit exceptional-fibre endpoint
term. -/
theorem jurkatRichertSourceRemainderSum_le_standardMax_add_exceptional
    (N : ℕ) (ε : ℝ) (hEven : Even N) (hN : 2 < N) :
    jurkatRichertSourceRemainderSum N ε ≤
      (∑ d ∈ (jurkatRichertSourceSiftingProduct N).divisors.filter
          (fun d : ℕ => (d : ℝ) ≤ (N : ℝ) ^ (1 / 2 - ε)),
        BombieriVinogradov.standardPrimeAPMaxError N d) +
      (((jurkatRichertSourceSiftingProduct N).divisors.filter
          (fun d : ℕ => (d : ℝ) ≤ (N : ℝ) ^ (1 / 2 - ε))).card : ℝ) *
        (jurkatRichertSourceExceptionalPrimes N).card := by
  let D := (jurkatRichertSourceSiftingProduct N).divisors.filter
    (fun d : ℕ => (d : ℝ) ≤ (N : ℝ) ^ (1 / 2 - ε))
  let E := jurkatRichertSourceExceptionalPrimes N
  have hpoint : ∀ d ∈ D, |(jurkatRichertSourceBoundingSieve N).rem d| ≤
      BombieriVinogradov.standardPrimeAPMaxError N d + E.card := by
    intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hdDiv, _⟩
    have hdvd : d ∣ jurkatRichertSourceSiftingProduct N :=
      Nat.dvd_of_mem_divisors hdDiv
    have hd0 : d ≠ 0 := by
      intro hd0
      subst d
      have hP0 : jurkatRichertSourceSiftingProduct N = 0 := by simpa using hdvd
      exact jurkatRichertSourceSiftingProduct_ne_zero N hP0
    have hunit : N % d ∈ AnalyticNumberTheory.Sieve.unitResidues d := by
      rw [AnalyticNumberTheory.Sieve.unitResidues]
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.mod_lt _ (Nat.pos_of_ne_zero hd0)),
          jurkatRichertSource_mod_coprime hdvd⟩
    calc
      |(jurkatRichertSourceBoundingSieve N).rem d| ≤
          |BombieriVinogradov.standardPrimeAPError N d (N % d)| + E.card := by
        simpa [E] using
          abs_jurkatRichertSource_rem_le_standardError_add_exceptional
            N d hEven hN hdvd
      _ ≤ BombieriVinogradov.standardPrimeAPMaxError N d + E.card :=
        calc
          |BombieriVinogradov.standardPrimeAPError N d (N % d)| + E.card =
              E.card + |BombieriVinogradov.standardPrimeAPError N d (N % d)| :=
            add_comm _ _
          _ ≤ E.card + BombieriVinogradov.standardPrimeAPMaxError N d :=
            add_le_add_right
              (BombieriVinogradov.abs_standardPrimeAPError_le_max hunit) _
          _ = BombieriVinogradov.standardPrimeAPMaxError N d + E.card :=
            add_comm _ _
  unfold jurkatRichertSourceRemainderSum
  change (∑ d ∈ D, |(jurkatRichertSourceBoundingSieve N).rem d|) ≤ _
  calc
    (∑ d ∈ D, |(jurkatRichertSourceBoundingSieve N).rem d|) ≤
        ∑ d ∈ D, (BombieriVinogradov.standardPrimeAPMaxError N d + E.card) :=
      Finset.sum_le_sum fun d hd => hpoint d hd
    _ = (∑ d ∈ D, BombieriVinogradov.standardPrimeAPMaxError N d) +
        (D.card : ℝ) * E.card := by
      rw [Finset.sum_add_distrib]
      simp [nsmul_eq_mul]

/-- Exceptional source primes are distinct prime divisors of `N`, so their
cardinality is bounded by the elementary `ω(N)` logarithmic bound. -/
theorem jurkatRichertSourceExceptionalPrimes_card_le_log
    (N : ℕ) (hN : 2 ≤ N) :
    ((jurkatRichertSourceExceptionalPrimes N).card : ℝ) ≤
      Real.log (N : ℝ) / Real.log 2 := by
  have hN0 : N ≠ 0 := by omega
  have hsubset :
      jurkatRichertSourceExceptionalPrimes N ⊆ N.primeFactors := by
    intro r hr
    rcases Finset.mem_filter.mp hr with ⟨_, hrPrime, _, hrN⟩
    exact (Nat.mem_primeFactors_of_ne_zero hN0).mpr ⟨hrPrime, hrN⟩
  have hcard := Finset.card_le_card hsubset
  calc
    ((jurkatRichertSourceExceptionalPrimes N).card : ℝ) ≤
        (N.primeFactors.card : ℝ) := by exact_mod_cast hcard
    _ ≤ Real.log (N : ℝ) / Real.log 2 :=
      LiuWeight.primeFactors_card_cast_le_log hN

/-- The level-restricted source divisor carrier has no more elements than its
real cutoff interval. -/
theorem jurkatRichertSource_remainderCarrier_card_le
    (N : ℕ) (ε : ℝ) :
    ((jurkatRichertSourceSiftingProduct N).divisors.filter
        (fun d : ℕ => (d : ℝ) ≤ (N : ℝ) ^ (1 / 2 - ε))).card ≤
      Nat.floor ((N : ℝ) ^ (1 / 2 - ε)) + 1 := by
  calc
    ((jurkatRichertSourceSiftingProduct N).divisors.filter
        (fun d : ℕ => (d : ℝ) ≤ (N : ℝ) ^ (1 / 2 - ε))).card ≤
        (Finset.range (Nat.floor ((N : ℝ) ^ (1 / 2 - ε)) + 1)).card := by
      apply Finset.card_le_card
      intro d hd
      rcases Finset.mem_filter.mp hd with ⟨_, hdLevel⟩
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hdLevel))
    _ = Nat.floor ((N : ℝ) ^ (1 / 2 - ε)) + 1 := Finset.card_range _

/-- The correction in the finite source-to-standard comparison has the
power-saving majorant `2 N^(1/2-ε) log N / log 2`. -/
theorem jurkatRichertSource_exceptional_endpoint_le
    (N : ℕ) (ε : ℝ) (hN : 2 ≤ N) (_hε : 0 < ε) (hεHalf : ε < 1 / 2) :
    (((jurkatRichertSourceSiftingProduct N).divisors.filter
        (fun d : ℕ => (d : ℝ) ≤ (N : ℝ) ^ (1 / 2 - ε))).card : ℝ) *
        (jurkatRichertSourceExceptionalPrimes N).card ≤
      2 * (N : ℝ) ^ (1 / 2 - ε) * Real.log N / Real.log 2 := by
  let D := (jurkatRichertSourceSiftingProduct N).divisors.filter
    (fun d : ℕ => (d : ℝ) ≤ (N : ℝ) ^ (1 / 2 - ε))
  let E := jurkatRichertSourceExceptionalPrimes N
  have hDnat : D.card ≤ Nat.floor ((N : ℝ) ^ (1 / 2 - ε)) + 1 :=
    jurkatRichertSource_remainderCarrier_card_le N ε
  have hpow : 0 ≤ (N : ℝ) ^ (1 / 2 - ε) := by positivity
  have hfloor :
      (Nat.floor ((N : ℝ) ^ (1 / 2 - ε)) : ℝ) ≤
        (N : ℝ) ^ (1 / 2 - ε) :=
    Nat.floor_le hpow
  have hD : (D.card : ℝ) ≤ 2 * (N : ℝ) ^ (1 / 2 - ε) := by
    have hcast : (D.card : ℝ) ≤
        (Nat.floor ((N : ℝ) ^ (1 / 2 - ε)) + 1 : ℕ) := by
      exact_mod_cast hDnat
    have hpowone : 1 ≤ (N : ℝ) ^ (1 / 2 - ε) := by
      apply Real.one_le_rpow
      · exact_mod_cast (show 1 ≤ N by omega)
      · linarith
    norm_num at hcast ⊢
    nlinarith
  have hE : (E.card : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
    simpa [E] using jurkatRichertSourceExceptionalPrimes_card_le_log N hN
  have hDnonneg : 0 ≤ (D.card : ℝ) := Nat.cast_nonneg _
  have hEnonneg : 0 ≤ (E.card : ℝ) := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log (N : ℝ) / Real.log 2 :=
    div_nonneg
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))
      (Real.log_nonneg (by norm_num))
  calc
    (D.card : ℝ) * E.card ≤
        (2 * (N : ℝ) ^ (1 / 2 - ε)) * (Real.log (N : ℝ) / Real.log 2) :=
      mul_le_mul hD hE hEnonneg (by positivity)
    _ = 2 * (N : ℝ) ^ (1 / 2 - ε) * Real.log N / Real.log 2 := by ring

namespace Internal

/-- The exceptional-fibre majorant is genuinely power-saving relative to the
Goldbach `N / log² N` scale. -/
theorem eventually_jurkatRichertSource_exceptional_endpoint_small
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      2 * (N : ℝ) ^ (1 / 2 - ε) * Real.log N / Real.log 2 ≤
        δ * SingularSeries.liuUniversalProduct * (N : ℝ) /
          Real.log N ^ (2 : ℕ) := by
  let U := SingularSeries.liuUniversalProduct
  have hU : 0 < U := by
    simpa [U] using SingularSeries.liuUniversalProduct_pos
  let K := δ * U * Real.log 2 / 2
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hsmall :
      ∀ᶠ x : ℝ in Filter.atTop,
        ‖Real.log x ^ (3 : ℝ)‖ ≤ K * ‖x ^ (1 / 2 + ε : ℝ)‖ :=
    (isLittleO_log_rpow_rpow_atTop (3 : ℝ) (by linarith)).bound hK
  have hsmallNat :
      ∀ᶠ N : ℕ in Filter.atTop,
        ‖Real.log (N : ℝ) ^ (3 : ℝ)‖ ≤
          K * ‖(N : ℝ) ^ (1 / 2 + ε : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually hsmall
  filter_upwards [hsmallNat, Filter.eventually_ge_atTop 2] with N hsmallN hN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hsmallN' :
      Real.log (N : ℝ) ^ (3 : ℕ) ≤
        K * (N : ℝ) ^ (1 / 2 + ε : ℝ) := by
    simpa [Real.norm_eq_abs, abs_of_pos hlog,
      Real.norm_of_nonneg (Real.rpow_nonneg hNpos.le _), Real.rpow_natCast] using hsmallN
  apply (div_le_div_iff₀ hlog2 (sq_pos_of_pos hlog)).2
  have hmul := mul_le_mul_of_nonneg_left hsmallN'
    (show 0 ≤ 2 * (N : ℝ) ^ (1 / 2 - ε) by positivity)
  dsimp [K, U] at hmul ⊢
  calc
    2 * (N : ℝ) ^ (1 / 2 - ε) * Real.log N * Real.log N ^ (2 : ℕ) =
        2 * (N : ℝ) ^ (1 / 2 - ε) * Real.log N ^ (3 : ℕ) := by ring
    _ ≤ 2 * (N : ℝ) ^ (1 / 2 - ε) *
        (δ * SingularSeries.liuUniversalProduct * Real.log 2 / 2 *
          (N : ℝ) ^ (1 / 2 + ε : ℝ)) := hmul
    _ = δ * SingularSeries.liuUniversalProduct * Real.log 2 *
        ((N : ℝ) ^ (1 / 2 - ε) * (N : ℝ) ^ (1 / 2 + ε : ℝ)) := by ring
    _ = δ * SingularSeries.liuUniversalProduct * Real.log 2 *
        (N : ℝ) ^ ((1 / 2 - ε) + (1 / 2 + ε) : ℝ) := by
      rw [← Real.rpow_add hNpos]
    _ = δ * SingularSeries.liuUniversalProduct * (N : ℝ) * Real.log 2 := by
      have hexp : (1 / 2 - ε) + (1 / 2 + ε : ℝ) = 1 := by ring
      rw [hexp, Real.rpow_one]
      ring

end Internal

/-- The literal medium-prime divisor count in Chen's Lemma 9:
`N^(1/10) < q ≤ N^(1/3)`.  Divisors are distinct because this is a cardinality,
not a valuation sum. -/
noncomputable def jurkatRichertSourceMediumPrimeCount (N p : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (fun q : ℕ =>
    q.Prime ∧ (N : ℝ) ^ (1 / 10 : ℝ) < (q : ℝ) ∧
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) ∧ q ∣ N - p)).card

/-- The literal medium-prime range `N^(1/10) < q ≤ N^(1/3)` from Chen's
Lemma 9. -/
noncomputable def jurkatRichertSourceMediumPrimes (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun q : ℕ =>
    q.Prime ∧ (N : ℝ) ^ (1 / 10 : ℝ) < (q : ℝ) ∧
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ))

/-- The real inequalities in the source range are represented exactly by
floored half-open power cutoffs. -/
theorem jurkatRichertSourceMediumPrimes_eq_Ioc_rpowFloor
    {N : ℕ} (hN : 1 ≤ N) :
    jurkatRichertSourceMediumPrimes N =
      (Finset.Ioc
        (MertensTheorem.rpowFloor N (1 / 10 : ℝ))
        (MertensTheorem.rpowFloor N (1 / 3 : ℝ))).filter Nat.Prime := by
  ext q
  unfold jurkatRichertSourceMediumPrimes
  rw [Finset.mem_filter, Finset.mem_filter,
    MertensTheorem.mem_Ioc_rpowFloor_iff]
  constructor
  · rintro ⟨hqN, hqPrime, hlo, hhi⟩
    exact ⟨⟨hlo, hhi⟩, hqPrime⟩
  · rintro ⟨⟨hlo, hhi⟩, hqPrime⟩
    have hpowN : (N : ℝ) ^ (1 / 3 : ℝ) ≤ N :=
      Real.rpow_le_self_of_one_le (by exact_mod_cast hN) (by norm_num)
    have hqNreal : (q : ℝ) ≤ N := hhi.trans hpowN
    have hqN : q ≤ N := by exact_mod_cast hqNreal
    exact ⟨Finset.mem_range.mpr (by omega), hqPrime, hlo, hhi⟩

/-- Chen's exact finite Lemma 9 producer
`P_N(N,z) - (1/2) * Σ_{z<q≤y} P_N(N,q,z)`, expanded as a sum over candidates. -/
noncomputable def jurkatRichertSourceWeightedCount (N : ℕ) : ℝ :=
  (jurkatRichertSourceCandidates N).sum (fun p =>
    1 - (jurkatRichertSourceMediumPrimeCount N p : ℝ) / 2)

/-- Chen's displayed `q`-outer sum of conditioned source counts in equation
(26). -/
noncomputable def jurkatRichertSourceMediumPrimeAggregate (N : ℕ) : ℝ :=
  (jurkatRichertSourceMediumPrimes N).sum (fun q =>
    (((jurkatRichertSourceCandidates N).filter (fun p => q ∣ N - p)).card : ℝ))

/-- The unsifted Goldbach-complement carrier conditioned by `q ∣ N - p`.
No coprimality assumption between `q` and `N` is imposed here. -/
noncomputable def jurkatRichertSourceConditionedSupport (N q : ℕ) : Finset ℕ :=
  (jurkatRichertSourceUnsiftedComplements N).filter (fun a => q ∣ a)

/-- Chen's finite `P_N(N,q,z)` sieve.  Its main mass retains the local
`1 / (q - 1)` factor, while its remainder is the exact discrepancy of the
conditioned finite carrier. -/
noncomputable def jurkatRichertSourceConditionedBoundingSieve
    (N q : ℕ) : BoundingSieve where
  support := jurkatRichertSourceConditionedSupport N q
  prodPrimes := jurkatRichertSourceSiftingProduct N
  prodPrimes_squarefree := jurkatRichertSourceSiftingProduct_squarefree N
  weights := fun _ => 1
  weights_nonneg := by intro n; norm_num
  totalMass :=
    LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N / ((q : ℝ) - 1)
  nu := AnalyticNumberTheory.Sieve.goldbachNu
  nu_mult := AnalyticNumberTheory.Sieve.goldbachNu_isMultiplicative
  nu_pos_of_prime := by
    intro p hp _
    exact AnalyticNumberTheory.Sieve.goldbachNu_pos_of_prime hp
  nu_lt_one_of_prime := by
    intro p hp hdiv
    have hp2 :=
      (prime_dvd_jurkatRichertSourceSiftingProduct hp).mp hdiv |>.1
    exact AnalyticNumberTheory.Sieve.goldbachNu_lt_one_of_prime hp hp2

/-- Exact finite identification of the conditioned sieve with
`P_N(N,q,N^(1/10))`.  In particular, the exceptional lane `q ∣ N` has not been
discarded or replaced by a reduced-residue approximation. -/
theorem jurkatRichertSourceConditionedBoundingSieve_siftedSum_eq_card
    (N q : ℕ) :
    (jurkatRichertSourceConditionedBoundingSieve N q).siftedSum =
      ((jurkatRichertSourceCandidates N).filter (fun p => q ∣ N - p)).card := by
  change (∑ a ∈ jurkatRichertSourceConditionedSupport N q,
      if Nat.Coprime (jurkatRichertSourceSiftingProduct N) a then (1 : ℝ) else 0) =
    (((jurkatRichertSourceCandidates N).filter (fun p => q ∣ N - p)).card : ℝ)
  rw [Finset.sum_boole]
  have hset :
      (jurkatRichertSourceConditionedSupport N q).filter
          (fun a => Nat.Coprime (jurkatRichertSourceSiftingProduct N) a) =
        ((jurkatRichertSourceCandidates N).filter
          (fun p => q ∣ N - p)).image (fun p => N - p) := by
    ext a
    constructor
    · intro ha
      rcases Finset.mem_filter.mp ha with ⟨haConditioned, haCoprime⟩
      rcases Finset.mem_filter.mp haConditioned with ⟨haSupport, hqa⟩
      have haBase :
          a ∈ (jurkatRichertSourceUnsiftedComplements N).filter
            (fun b => Nat.Coprime (jurkatRichertSourceSiftingProduct N) b) :=
        Finset.mem_filter.mpr ⟨haSupport, haCoprime⟩
      rw [jurkatRichertSourceSiftedComplements_eq_candidate_image] at haBase
      rcases Finset.mem_image.mp haBase with ⟨p, hp, rfl⟩
      exact Finset.mem_image.mpr
        ⟨p, Finset.mem_filter.mpr ⟨hp, hqa⟩, rfl⟩
    · intro ha
      rcases Finset.mem_image.mp ha with ⟨p, hp, rfl⟩
      rcases Finset.mem_filter.mp hp with ⟨hpCandidate, hqp⟩
      have hpBase :
          N - p ∈ (jurkatRichertSourceUnsiftedComplements N).filter
            (fun a => Nat.Coprime (jurkatRichertSourceSiftingProduct N) a) := by
        rw [jurkatRichertSourceSiftedComplements_eq_candidate_image]
        exact Finset.mem_image.mpr ⟨p, hpCandidate, rfl⟩
      rcases Finset.mem_filter.mp hpBase with ⟨hpSupport, hpCoprime⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hpSupport, hqp⟩, hpCoprime⟩
  rw [hset]
  have hcard :
      (((jurkatRichertSourceCandidates N).filter
        (fun p => q ∣ N - p)).image (fun p => N - p)).card =
        ((jurkatRichertSourceCandidates N).filter
          (fun p => q ∣ N - p)).card :=
    Finset.card_image_of_injOn (by
      intro p hp r hr hpr
      have hpN : p ≤ N := by
        simpa [jurkatRichertSourceCandidates] using
          (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
      have hrN : r ≤ N := by
        simpa [jurkatRichertSourceCandidates] using
          (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
      change N - p = N - r at hpr
      omega)
  exact_mod_cast hcard

/-- The integer level corresponding exactly to the varying real level
`N^(1/2-epsilon) / q`. -/
noncomputable def jurkatRichertSourceUpperLevel
    (N q : ℕ) (ε : ℝ) : ℕ :=
  Nat.floor ((N : ℝ) ^ (1 / 2 - ε) / q) + 1

/-- The logarithmic ratio for the upper sieve at the varying level
`N^(1/2-epsilon) / q` and sifting threshold `N^(1/10)`. -/
noncomputable def jurkatRichertSourceUpperSieveRatio
    (N q : ℕ) (ε : ℝ) : ℝ :=
  Real.log ((N : ℝ) ^ (1 / 2 - ε) / q) /
    Real.log ((N : ℝ) ^ (1 / 10 : ℝ))

/-- At zero level loss, the varying sieve ratio is exactly affine in the
logarithmic prime coordinate. -/
theorem jurkatRichertSourceUpperSieveRatio_zero
    {N q : ℕ} (hN : 1 < N) (hq : 0 < q) :
    jurkatRichertSourceUpperSieveRatio N q 0 =
      5 - 10 * (Real.log (q : ℝ) / Real.log (N : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  unfold jurkatRichertSourceUpperSieveRatio
  rw [Real.log_div (Real.rpow_pos_of_pos hNr _).ne' hqr.ne',
    Real.log_rpow hNr, Real.log_rpow hNr]
  field_simp [hlogN]
  ring

/-- An epsilon loss in the level lowers every sieve ratio by exactly
`10 * epsilon`. -/
theorem jurkatRichertSourceUpperSieveRatio_eq_zero_sub
    {N q : ℕ} (hN : 1 < N) (hq : 0 < q) (ε : ℝ) :
    jurkatRichertSourceUpperSieveRatio N q ε =
      jurkatRichertSourceUpperSieveRatio N q 0 - 10 * ε := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  unfold jurkatRichertSourceUpperSieveRatio
  rw [Real.log_div (Real.rpow_pos_of_pos hNr _).ne' hqr.ne',
    Real.log_div (Real.rpow_pos_of_pos hNr _).ne' hqr.ne',
    Real.log_rpow hNr, Real.log_rpow hNr, Real.log_rpow hNr]
  field_simp [hlogN]
  ring

/-- Every source medium prime has logarithmic coordinate in the exact interval
`[1/10, 1/3]`. -/
theorem jurkatRichertSourceMediumPrime_log_mem
    {N q : ℕ} (hN : 1 < N)
    (hq : q ∈ jurkatRichertSourceMediumPrimes N) :
    Real.log (q : ℝ) / Real.log (N : ℝ) ∈
      Set.Icc (1 / 10 : ℝ) (1 / 3 : ℝ) := by
  rcases Finset.mem_filter.mp hq with ⟨_, hqPrime, hqLower, hqUpper⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hqr : (0 : ℝ) < q := by exact_mod_cast hqPrime.pos
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hlogLower := Real.strictMonoOn_log.monotoneOn
    (Real.rpow_pos_of_pos hNr _) hqr hqLower.le
  have hlogUpper := Real.strictMonoOn_log.monotoneOn
    hqr (Real.rpow_pos_of_pos hNr _) hqUpper
  rw [Real.log_rpow hNr] at hlogLower hlogUpper
  exact ⟨(le_div_iff₀ hlogN).2 hlogLower,
    (div_le_iff₀ hlogN).2 hlogUpper⟩

/-- The dimension-one upper linear-sieve factor on the range used in Chen's
q-sum.  The integral branch is the one whose partial summation contributes
`K / 2`. -/
noncomputable def jurkatRichertUpperLinearSieveFactor (s : ℝ) : ℝ :=
  if s ≤ 3 then
    2 * Real.exp Real.eulerMascheroniConstant / s
  else
    2 * Real.exp Real.eulerMascheroniConstant / s *
      (1 + jurkatRichertInnerIntegral s)

private lemma jurkatRichertInnerIntegral_three :
    jurkatRichertInnerIntegral 3 = 0 := by
  norm_num [jurkatRichertInnerIntegral]

private lemma jurkatRichertUpperLinearSieveFactor_integral_branch {a : ℝ}
    (ha : a ∈ Set.Icc (1 / 10 : ℝ) (1 / 5 : ℝ)) :
    jurkatRichertUpperLinearSieveFactor (5 - 10 * a) =
      2 * Real.exp Real.eulerMascheroniConstant / (5 - 10 * a) *
        (1 + jurkatRichertInnerIntegral (5 - 10 * a)) := by
  unfold jurkatRichertUpperLinearSieveFactor
  split_ifs with h
  · have hs : 5 - 10 * a = 3 := by linarith [ha.2]
    rw [hs, jurkatRichertInnerIntegral_three]
    ring
  · rfl

private lemma jurkatRichertUpperLinearSieveFactor_base_branch {a : ℝ}
    (ha : a ∈ Set.Icc (1 / 5 : ℝ) (1 / 3 : ℝ)) :
    jurkatRichertUpperLinearSieveFactor (5 - 10 * a) =
      2 * Real.exp Real.eulerMascheroniConstant / (5 - 10 * a) := by
  unfold jurkatRichertUpperLinearSieveFactor
  rw [if_pos (by linarith [ha.1])]

/-- The zero-epsilon Jurkat--Richert weight is continuous on the medium-prime
exponent interval. -/
theorem jurkatRichertUpperLinearSieveFactor_zeroEpsilon_continuousOn :
    ContinuousOn (fun a : ℝ => jurkatRichertUpperLinearSieveFactor (5 - 10 * a))
      (Set.Icc (1 / 10 : ℝ) (1 / 3 : ℝ)) := by
  have hleft : ContinuousOn
      (fun a : ℝ => jurkatRichertUpperLinearSieveFactor (5 - 10 * a))
      (Set.Icc (1 / 10 : ℝ) (1 / 5 : ℝ)) := by
    have hinner : ContinuousOn (fun a : ℝ =>
        jurkatRichertInnerIntegral (5 - 10 * a))
        (Set.Icc (1 / 10 : ℝ) (1 / 5 : ℝ)) := by
      apply continuousOn_jurkatRichertInnerIntegral.comp
        (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
      intro a ha
      change 3 ≤ 5 - 10 * a ∧ 5 - 10 * a ≤ 4
      constructor <;> linarith [ha.1, ha.2]
    have hbranch : ContinuousOn (fun a : ℝ =>
        2 * Real.exp Real.eulerMascheroniConstant / (5 - 10 * a) *
          (1 + jurkatRichertInnerIntegral (5 - 10 * a)))
        (Set.Icc (1 / 10 : ℝ) (1 / 5 : ℝ)) := by
      apply (continuousOn_const.div
        (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)) ?_).mul
          (continuousOn_const.add hinner)
      intro a ha
      change 5 - 10 * a ≠ 0
      linarith [ha.2]
    exact hbranch.congr
      (fun a ha => jurkatRichertUpperLinearSieveFactor_integral_branch ha)
  have hright : ContinuousOn
      (fun a : ℝ => jurkatRichertUpperLinearSieveFactor (5 - 10 * a))
      (Set.Icc (1 / 5 : ℝ) (1 / 3 : ℝ)) := by
    have hbranch : ContinuousOn (fun a : ℝ =>
        2 * Real.exp Real.eulerMascheroniConstant / (5 - 10 * a))
        (Set.Icc (1 / 5 : ℝ) (1 / 3 : ℝ)) := by
      apply continuousOn_const.div
        (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
      intro a ha
      change 5 - 10 * a ≠ 0
      linarith [ha.2]
    exact hbranch.congr
      (fun a ha => jurkatRichertUpperLinearSieveFactor_base_branch ha)
  rw [← Set.Icc_union_Icc_eq_Icc (by norm_num : (1 / 10 : ℝ) ≤ 1 / 5)
    (by norm_num : (1 / 5 : ℝ) ≤ 1 / 3)]
  exact hleft.union_of_isClosed hright isClosed_Icc isClosed_Icc

/-- The zero-epsilon Jurkat--Richert weight is nonnegative on the medium-prime
exponent interval. -/
theorem jurkatRichertUpperLinearSieveFactor_zeroEpsilon_nonneg
    {a : ℝ} (ha : a ∈ Set.Icc (1 / 10 : ℝ) (1 / 3 : ℝ)) :
    0 ≤ jurkatRichertUpperLinearSieveFactor (5 - 10 * a) := by
  have hs : 0 < 5 - 10 * a := by linarith [ha.2]
  unfold jurkatRichertUpperLinearSieveFactor
  split_ifs with h
  · exact div_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) hs.le
  · exact mul_nonneg
      (div_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) hs.le)
      (by
        have hi := jurkatRichertInnerIntegral_nonneg (le_of_not_ge h)
        linarith)

private lemma jurkatRichertInnerIntegral_mono
    {u v : ℝ} (hu : 3 ≤ u) (huv : u ≤ v) (hv : v ≤ 4) :
    jurkatRichertInnerIntegral u ≤ jurkatRichertInnerIntegral v := by
  let f : ℝ → ℝ := fun t => Real.log (t - 1) / t
  have hint : ∀ {x y : ℝ}, 2 ≤ x → x ≤ y → y ≤ 3 →
      IntervalIntegrable f volume x y := by
    intro x y hx hxy hy
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hxy]
    apply ContinuousOn.div
    · apply ContinuousOn.log (continuousOn_id.sub continuousOn_const)
      intro t ht
      change t - 1 ≠ 0
      linarith [ht.1]
    · exact continuousOn_id
    · intro t ht
      change t ≠ 0
      linarith [ht.1]
  have h₁ : IntervalIntegrable f volume 2 (u - 1) :=
    hint (by norm_num) (by linarith) (by linarith)
  have h₂ : IntervalIntegrable f volume (u - 1) (v - 1) :=
    hint (by linarith) (by linarith) (by linarith)
  unfold jurkatRichertInnerIntegral
  change (∫ t in (2 : ℝ)..u - 1, f t) ≤ ∫ t in (2 : ℝ)..v - 1, f t
  calc
    (∫ t in (2 : ℝ)..u - 1, f t) ≤
        (∫ t in (2 : ℝ)..u - 1, f t) + ∫ t in u - 1..v - 1, f t := by
      apply le_add_of_nonneg_right
      apply intervalIntegral.integral_nonneg (by linarith)
      intro t ht
      exact div_nonneg (Real.log_nonneg (by linarith [ht.1])) (by linarith [ht.1])
    _ = ∫ t in (2 : ℝ)..v - 1, f t :=
      intervalIntegral.integral_add_adjacent_intervals h₁ h₂

/-- Moving the sieve argument by `10 * ε` costs at most the uniform factor
`(1 - 6 * ε)⁻¹` throughout the medium-prime exponent interval. -/
theorem jurkatRichertUpperLinearSieveFactor_perturbation
    {ε a : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 60)
    (ha : a ∈ Set.Icc (1 / 10 : ℝ) (1 / 3 : ℝ)) :
    jurkatRichertUpperLinearSieveFactor (5 - 10 * ε - 10 * a) ≤
      (1 / (1 - 6 * ε)) *
        jurkatRichertUpperLinearSieveFactor (5 - 10 * a) := by
  let s : ℝ := 5 - 10 * a
  let t : ℝ := s - 10 * ε
  have hslo : 5 / 3 ≤ s := by dsimp [s]; linarith [ha.2]
  have hshi : s ≤ 4 := by dsimp [s]; linarith [ha.1]
  have hspos : 0 < s := lt_of_lt_of_le (by norm_num) hslo
  have htpos : 0 < t := by
    dsimp [t]
    linarith
  have hts : t ≤ s := by dsimp [t]; linarith
  have hden : 0 < 1 - 6 * ε := by linarith
  have hC : 0 ≤ 2 * Real.exp Real.eulerMascheroniConstant :=
    mul_nonneg (by norm_num) (Real.exp_pos _).le
  have hratio : s / t ≤ 1 / (1 - 6 * ε) := by
    rw [div_le_div_iff₀ htpos hden]
    have haux : 0 ≤ ε * (6 * s - 10) :=
      mul_nonneg hε0.le (by nlinarith [hslo])
    dsimp [t]
    nlinarith
  have hbase :
      2 * Real.exp Real.eulerMascheroniConstant / t ≤
        (1 / (1 - 6 * ε)) *
          (2 * Real.exp Real.eulerMascheroniConstant / s) := by
    calc
      2 * Real.exp Real.eulerMascheroniConstant / t =
          (s / t) * (2 * Real.exp Real.eulerMascheroniConstant / s) := by
            field_simp [ne_of_gt htpos, ne_of_gt hspos]
      _ ≤ (1 / (1 - 6 * ε)) *
          (2 * Real.exp Real.eulerMascheroniConstant / s) :=
        mul_le_mul_of_nonneg_right hratio (div_nonneg hC hspos.le)
  have harg : 5 - 10 * ε - 10 * a = t := by
    dsimp [t, s]
    ring
  rw [harg]
  change jurkatRichertUpperLinearSieveFactor t ≤
    (1 / (1 - 6 * ε)) * jurkatRichertUpperLinearSieveFactor s
  unfold jurkatRichertUpperLinearSieveFactor
  by_cases ht3 : t ≤ 3
  · rw [if_pos ht3]
    by_cases hs3 : s ≤ 3
    · rw [if_pos hs3]
      exact hbase
    · rw [if_neg hs3]
      have hI : 0 ≤ jurkatRichertInnerIntegral s :=
        jurkatRichertInnerIntegral_nonneg (le_of_not_ge hs3)
      have hfactor : 2 * Real.exp Real.eulerMascheroniConstant / s ≤
          2 * Real.exp Real.eulerMascheroniConstant / s *
            (1 + jurkatRichertInnerIntegral s) := by
        nlinarith [mul_nonneg (div_nonneg hC hspos.le) hI]
      exact hbase.trans
        (mul_le_mul_of_nonneg_left hfactor (one_div_pos.mpr hden).le)
  · rw [if_neg ht3]
    have hs3 : ¬s ≤ 3 := fun hs3 => ht3 (le_trans hts hs3)
    rw [if_neg hs3]
    have ht3' : 3 ≤ t := le_of_not_ge ht3
    have hIt : 0 ≤ jurkatRichertInnerIntegral t :=
      jurkatRichertInnerIntegral_nonneg ht3'
    have hI : jurkatRichertInnerIntegral t ≤ jurkatRichertInnerIntegral s :=
      jurkatRichertInnerIntegral_mono ht3' hts hshi
    calc
      2 * Real.exp Real.eulerMascheroniConstant / t *
          (1 + jurkatRichertInnerIntegral t) ≤
          ((1 / (1 - 6 * ε)) *
            (2 * Real.exp Real.eulerMascheroniConstant / s)) *
              (1 + jurkatRichertInnerIntegral t) :=
        mul_le_mul_of_nonneg_right hbase (by linarith)
      _ ≤ ((1 / (1 - 6 * ε)) *
            (2 * Real.exp Real.eulerMascheroniConstant / s)) *
              (1 + jurkatRichertInnerIntegral s) := by
        apply mul_le_mul_of_nonneg_left (by linarith)
        exact mul_nonneg (one_div_pos.mpr hden).le (div_nonneg hC hspos.le)
      _ = (1 / (1 - 6 * ε)) *
          (2 * Real.exp Real.eulerMascheroniConstant / s *
            (1 + jurkatRichertInnerIntegral s)) := by ring

private lemma jurkatRichertUpperLinearSieveFactor_base_integral :
    (∫ a in (1 / 10 : ℝ)..1 / 3,
        (2 * Real.exp Real.eulerMascheroniConstant / (5 - 10 * a)) / a) =
      (2 * Real.exp Real.eulerMascheroniConstant / 5) * Real.log 8 := by
  let C : ℝ := 2 * Real.exp Real.eulerMascheroniConstant
  let G : ℝ → ℝ := fun a =>
    (C / 5) * (Real.log a - Real.log (1 - 2 * a))
  have hint : IntervalIntegrable
      (fun a : ℝ => (C / (5 - 10 * a)) / a) volume (1 / 10) (1 / 3) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (1 / 10 : ℝ) ≤ 1 / 3)]
    apply ContinuousOn.div
    · apply continuousOn_const.div
        (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
      intro a ha
      change 5 - 10 * a ≠ 0
      linarith [ha.2]
    · exact continuousOn_id
    · intro a ha
      change a ≠ 0
      linarith [ha.1]
  have hG : ∀ a ∈ Set.uIcc (1 / 10 : ℝ) (1 / 3),
      HasDerivAt G ((C / (5 - 10 * a)) / a) a := by
    intro a ha
    rw [Set.uIcc_of_le (by norm_num : (1 / 10 : ℝ) ≤ 1 / 3)] at ha
    have ha0 : a ≠ 0 := by linarith [ha.1]
    have hlin0 : 1 - 2 * a ≠ 0 := by linarith [ha.2]
    have hlin : HasDerivAt (fun x : ℝ => 1 - 2 * x) (-2) a := by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id a).const_mul (2 : ℝ)).const_sub (1 : ℝ)
    have h := ((Real.hasDerivAt_log ha0).sub
      ((Real.hasDerivAt_log hlin0).comp a hlin)).const_mul (C / 5)
    have hderiv :
        C / (5 - 10 * a) / a =
          C / 5 * (a⁻¹ - (1 - 2 * a)⁻¹ * (-2)) := by
      rw [show 5 - 10 * a = 5 * (1 - 2 * a) by ring]
      field_simp [ha0, hlin0]
      ring
    dsimp [G]
    rw [hderiv]
    exact h
  have heval :
      G (1 / 3) - G (1 / 10) = (C / 5) * Real.log 8 := by
    dsimp [G]
    rw [show (1 : ℝ) - 2 * (1 / 3) = 1 / 3 by norm_num]
    rw [sub_self, mul_zero, zero_sub]
    rw [← Real.log_div (by norm_num : (1 / 10 : ℝ) ≠ 0)
      (by norm_num : (1 : ℝ) - 2 * (1 / 10) ≠ 0)]
    norm_num
    rw [show (1 / 8 : ℝ) = (8 : ℝ)⁻¹ by norm_num, Real.log_inv]
    ring
  change (∫ a in (1 / 10 : ℝ)..1 / 3, (C / (5 - 10 * a)) / a) =
    (C / 5) * Real.log 8
  calc
    (∫ a in (1 / 10 : ℝ)..1 / 3, (C / (5 - 10 * a)) / a) =
        G (1 / 3) - G (1 / 10) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hG hint
    _ = (C / 5) * Real.log 8 := heval

private lemma jurkatRichertUpperLinearSieveFactor_inner_correction_integral :
    (∫ a in (1 / 10 : ℝ)..1 / 5,
        ((2 * Real.exp Real.eulerMascheroniConstant / (5 - 10 * a)) *
          jurkatRichertInnerIntegral (5 - 10 * a)) / a) =
      (Real.exp Real.eulerMascheroniConstant / 5) * jurkatRichertK := by
  let C : ℝ := 2 * Real.exp Real.eulerMascheroniConstant
  let g : ℝ → ℝ := fun u =>
    (10 * C / (u * (5 - u))) * jurkatRichertInnerIntegral u
  have hpoint : Set.EqOn
      (fun a : ℝ => ((C / (5 - 10 * a)) *
        jurkatRichertInnerIntegral (5 - 10 * a)) / a)
      (fun a : ℝ => g (5 - 10 * a))
      (Set.uIcc (1 / 10 : ℝ) (1 / 5 : ℝ)) := by
    intro a ha
    rw [Set.uIcc_of_le (by norm_num : (1 / 10 : ℝ) ≤ 1 / 5)] at ha
    have ha0 : a ≠ 0 := by linarith [ha.1]
    have hs0 : 5 - 10 * a ≠ 0 := by linarith [ha.2]
    have h5s0 : 5 - (5 - 10 * a) ≠ 0 := by linarith [ha.1]
    dsimp [g]
    field_simp [ha0, hs0, h5s0]
    ring
  have hchange :
      (∫ a in (1 / 10 : ℝ)..1 / 5, g (5 - 10 * a)) =
        (1 / 10 : ℝ) * ∫ u in (3 : ℝ)..4, g u := by
    have h := intervalIntegral.integral_comp_sub_mul
      (f := g) (a := (1 / 10 : ℝ)) (b := (1 / 5 : ℝ))
      (c := (10 : ℝ)) (by norm_num) (5 : ℝ)
    norm_num at h ⊢
  have hg :
      (∫ u in (3 : ℝ)..4, g u) = C * jurkatRichertK := by
    unfold jurkatRichertK
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp [g]
    ring
  change (∫ a in (1 / 10 : ℝ)..1 / 5,
      ((C / (5 - 10 * a)) * jurkatRichertInnerIntegral (5 - 10 * a)) / a) =
    (Real.exp Real.eulerMascheroniConstant / 5) * jurkatRichertK
  calc
    (∫ a in (1 / 10 : ℝ)..1 / 5,
        ((C / (5 - 10 * a)) * jurkatRichertInnerIntegral (5 - 10 * a)) / a) =
        ∫ a in (1 / 10 : ℝ)..1 / 5, g (5 - 10 * a) :=
      intervalIntegral.integral_congr hpoint
    _ = (1 / 10 : ℝ) * ∫ u in (3 : ℝ)..4, g u := hchange
    _ = (1 / 10 : ℝ) * (C * jurkatRichertK) := by rw [hg]
    _ = (Real.exp Real.eulerMascheroniConstant / 5) * jurkatRichertK := by
      dsimp [C]
      ring

/-- Exact zero-epsilon weighted integral used in the varying-`q` prime sum. -/
theorem jurkatRichertUpperLinearSieveFactor_zeroEpsilon_integral :
    (∫ a in (1 / 10 : ℝ)..1 / 3,
        jurkatRichertUpperLinearSieveFactor (5 - 10 * a) / a) =
      (2 * Real.exp Real.eulerMascheroniConstant / 5) *
        (Real.log 8 + jurkatRichertK / 2) := by
  let C : ℝ := 2 * Real.exp Real.eulerMascheroniConstant
  let w : ℝ → ℝ := fun a =>
    jurkatRichertUpperLinearSieveFactor (5 - 10 * a) / a
  let b : ℝ → ℝ := fun a => (C / (5 - 10 * a)) / a
  let c : ℝ → ℝ := fun a =>
    ((C / (5 - 10 * a)) * jurkatRichertInnerIntegral (5 - 10 * a)) / a
  have hwcont : ContinuousOn w (Set.Icc (1 / 10 : ℝ) (1 / 3 : ℝ)) := by
    dsimp [w]
    apply jurkatRichertUpperLinearSieveFactor_zeroEpsilon_continuousOn.div
      continuousOn_id
    intro a ha
    change a ≠ 0
    linarith [ha.1]
  have hbcont : ContinuousOn b (Set.Icc (1 / 10 : ℝ) (1 / 3 : ℝ)) := by
    dsimp [b]
    apply (continuousOn_const.div
      (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)) ?_).div
        continuousOn_id
    · intro a ha
      change a ≠ 0
      linarith [ha.1]
    · intro a ha
      change 5 - 10 * a ≠ 0
      linarith [ha.2]
  have hccont : ContinuousOn c (Set.Icc (1 / 10 : ℝ) (1 / 5 : ℝ)) := by
    have hinner : ContinuousOn (fun a : ℝ =>
        jurkatRichertInnerIntegral (5 - 10 * a))
        (Set.Icc (1 / 10 : ℝ) (1 / 5 : ℝ)) := by
      apply continuousOn_jurkatRichertInnerIntegral.comp
        (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
      intro a ha
      change 3 ≤ 5 - 10 * a ∧ 5 - 10 * a ≤ 4
      constructor <;> linarith [ha.1, ha.2]
    dsimp [c]
    apply ((continuousOn_const.div
      (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)) ?_).mul
        hinner).div continuousOn_id
    · intro a ha
      change a ≠ 0
      linarith [ha.1]
    · intro a ha
      change 5 - 10 * a ≠ 0
      linarith [ha.2]
  have hw : IntervalIntegrable w volume (1 / 10) (1 / 3) := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le (by norm_num : (1 / 10 : ℝ) ≤ 1 / 3)]
  have hb : IntervalIntegrable b volume (1 / 10) (1 / 3) := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le (by norm_num : (1 / 10 : ℝ) ≤ 1 / 3)]
  have hwl : IntervalIntegrable w volume (1 / 10) (1 / 5) := by
    apply hw.mono_set
    rw [Set.uIcc_of_le (by norm_num : (1 / 10 : ℝ) ≤ 1 / 5),
      Set.uIcc_of_le (by norm_num : (1 / 10 : ℝ) ≤ 1 / 3)]
    intro a ha
    exact ⟨ha.1, le_trans ha.2 (by norm_num)⟩
  have hwr : IntervalIntegrable w volume (1 / 5) (1 / 3) := by
    apply hw.mono_set
    rw [Set.uIcc_of_le (by norm_num : (1 / 5 : ℝ) ≤ 1 / 3),
      Set.uIcc_of_le (by norm_num : (1 / 10 : ℝ) ≤ 1 / 3)]
    intro a ha
    exact ⟨le_trans (by norm_num) ha.1, ha.2⟩
  have hbl : IntervalIntegrable b volume (1 / 10) (1 / 5) := by
    apply hb.mono_set
    rw [Set.uIcc_of_le (by norm_num : (1 / 10 : ℝ) ≤ 1 / 5),
      Set.uIcc_of_le (by norm_num : (1 / 10 : ℝ) ≤ 1 / 3)]
    intro a ha
    exact ⟨ha.1, le_trans ha.2 (by norm_num)⟩
  have hbr : IntervalIntegrable b volume (1 / 5) (1 / 3) := by
    apply hb.mono_set
    rw [Set.uIcc_of_le (by norm_num : (1 / 5 : ℝ) ≤ 1 / 3),
      Set.uIcc_of_le (by norm_num : (1 / 10 : ℝ) ≤ 1 / 3)]
    intro a ha
    exact ⟨le_trans (by norm_num) ha.1, ha.2⟩
  have hc : IntervalIntegrable c volume (1 / 10) (1 / 5) := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le (by norm_num : (1 / 10 : ℝ) ≤ 1 / 5)]
  have hleft : Set.EqOn w (fun a => b a + c a)
      (Set.uIcc (1 / 10 : ℝ) (1 / 5 : ℝ)) := by
    intro a ha
    rw [Set.uIcc_of_le (by norm_num : (1 / 10 : ℝ) ≤ 1 / 5)] at ha
    dsimp [w, b, c]
    rw [jurkatRichertUpperLinearSieveFactor_integral_branch ha]
    ring
  have hright : Set.EqOn w b
      (Set.uIcc (1 / 5 : ℝ) (1 / 3 : ℝ)) := by
    intro a ha
    rw [Set.uIcc_of_le (by norm_num : (1 / 5 : ℝ) ≤ 1 / 3)] at ha
    dsimp [w, b]
    rw [jurkatRichertUpperLinearSieveFactor_base_branch ha]
  change (∫ a in (1 / 10 : ℝ)..1 / 3, w a) =
    (C / 5) * (Real.log 8 + jurkatRichertK / 2)
  calc
    (∫ a in (1 / 10 : ℝ)..1 / 3, w a) =
        (∫ a in (1 / 10 : ℝ)..1 / 5, w a) +
          ∫ a in (1 / 5 : ℝ)..1 / 3, w a :=
      (intervalIntegral.integral_add_adjacent_intervals hwl hwr).symm
    _ = (∫ a in (1 / 10 : ℝ)..1 / 5, b a + c a) +
          ∫ a in (1 / 5 : ℝ)..1 / 3, b a := by
      rw [intervalIntegral.integral_congr hleft,
        intervalIntegral.integral_congr hright]
    _ = ((∫ a in (1 / 10 : ℝ)..1 / 5, b a) +
          ∫ a in (1 / 10 : ℝ)..1 / 5, c a) +
          ∫ a in (1 / 5 : ℝ)..1 / 3, b a := by
      rw [intervalIntegral.integral_add hbl hc]
    _ = (∫ a in (1 / 10 : ℝ)..1 / 3, b a) +
          ∫ a in (1 / 10 : ℝ)..1 / 5, c a := by
      rw [← intervalIntegral.integral_add_adjacent_intervals hbl hbr]
      ring
    _ = (C / 5) * Real.log 8 +
          (Real.exp Real.eulerMascheroniConstant / 5) * jurkatRichertK := by
      rw [show (∫ a in (1 / 10 : ℝ)..1 / 3, b a) =
          (C / 5) * Real.log 8 by
            simpa [b, C] using jurkatRichertUpperLinearSieveFactor_base_integral,
        show (∫ a in (1 / 10 : ℝ)..1 / 5, c a) =
          (Real.exp Real.eulerMascheroniConstant / 5) * jurkatRichertK by
            simpa [c, C] using
              jurkatRichertUpperLinearSieveFactor_inner_correction_integral]
    _ = (C / 5) * (Real.log 8 + jurkatRichertK / 2) := by
      dsimp [C]
      ring

end MathlibNt.SieveTheory.SwitchingPrinciple
