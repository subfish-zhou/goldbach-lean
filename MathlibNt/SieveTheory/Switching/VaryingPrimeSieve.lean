import MathlibNt.SieveTheory.Switching.SourceSieve

/-!
# Varying-prime sieves and cutoff corrections

Upper Rosser certificates and weighted Bombieri--Vinogradov remainders control
the medium-prime aggregate. Nonreduced residues and cutoff fibers are bounded
explicitly before comparison with the corrected weighted count.

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

/-- The explicit q-local density model before prime-q partial summation.  It
retains the exact `1 / (q - 1)` mass and the varying upper-sieve factor. -/
noncomputable def jurkatRichertSourceVaryingQDensityModel
    (N : ℕ) (ε : ℝ) : ℝ :=
  (jurkatRichertSourceMediumPrimes N).sum (fun q =>
    (jurkatRichertSourceConditionedBoundingSieve N q).totalMass *
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
        (jurkatRichertSourceConditionedBoundingSieve N q) *
      jurkatRichertUpperLinearSieveFactor
        (jurkatRichertSourceUpperSieveRatio N q ε))

/-- The conditioned densities have one common Goldbach sieve mass.  Only the
exact local factor `1 / (q - 1)` and the varying linear-sieve weight remain
inside the prime sum. -/
theorem jurkatRichertSourceVaryingQDensityModel_eq_common_mul
    (N : ℕ) (ε : ℝ) :
    jurkatRichertSourceVaryingQDensityModel N ε =
      (LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N *
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
          (jurkatRichertSourceBoundingSieve N)) *
      ∑ q ∈ jurkatRichertSourceMediumPrimes N,
        jurkatRichertUpperLinearSieveFactor
          (jurkatRichertSourceUpperSieveRatio N q ε) / ((q : ℝ) - 1) := by
  unfold jurkatRichertSourceVaryingQDensityModel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  change
    (LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N / ((q : ℝ) - 1) *
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
        (jurkatRichertSourceBoundingSieve N)) *
        jurkatRichertUpperLinearSieveFactor
          (jurkatRichertSourceUpperSieveRatio N q ε) =
      (LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N *
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
          (jurkatRichertSourceBoundingSieve N)) *
        (jurkatRichertUpperLinearSieveFactor
          (jurkatRichertSourceUpperSieveRatio N q ε) / ((q : ℝ) - 1))
  ring

/-- The explicit upper Rosser coefficient at Chen's exact varying level
`floor (N^(1/2-ε) / q) + 1`. -/
noncomputable def jurkatRichertSourceVaryingQUpperRosserWeight
    (N q : ℕ) (ε : ℝ) (d : ℕ) : ℝ :=
  LinearSieve.upperRosserWeight (jurkatRichertSourceSiftingProduct N)
    (jurkatRichertSourceUpperLevel N q ε) d

theorem jurkatRichertSourceVaryingQUpperRosserWeight_hasUpperLevelSupport
    (N q : ℕ) (ε : ℝ) :
    LinearSieve.HasUpperLevelSupport
      (jurkatRichertSourceSiftingProduct N)
      (jurkatRichertSourceUpperLevel N q ε)
      (jurkatRichertSourceVaryingQUpperRosserWeight N q ε) :=
  LinearSieve.upperRosserWeight_hasUpperLevelSupport _ _

theorem abs_jurkatRichertSourceVaryingQUpperRosserWeight_le_one
    (N q d : ℕ) (ε : ℝ) :
    |jurkatRichertSourceVaryingQUpperRosserWeight N q ε d| ≤ 1 :=
  LinearSieve.abs_upperRosserWeight_le_one _ _ _

theorem abs_jurkatRichertSourceVaryingQUpperRosserWeight_le_threePow
    (N q d : ℕ) (ε : ℝ) :
    |jurkatRichertSourceVaryingQUpperRosserWeight N q ε d| ≤
      (3 : ℝ) ^ d.primeFactors.card :=
  (abs_jurkatRichertSourceVaryingQUpperRosserWeight_le_one N q d ε).trans
    (one_le_pow₀ (by norm_num))

/-- At every medium prime and for the epsilon range supplied by Chen's prime-sum
argument, the explicit coefficient is a finite upper-Möbius certificate. -/
theorem jurkatRichertSourceVaryingQUpperRosserWeight_certificate
    {N q : ℕ} {ε : ℝ} (hN : 1 < N) (hε : ε < 1 / 60)
    (hq : q ∈ jurkatRichertSourceMediumPrimes N) :
    LinearSieve.IsUpperRosserCertificate
      (jurkatRichertSourceSiftingProduct N)
      (jurkatRichertSourceUpperLevel N q ε) := by
  rcases (Finset.mem_filter.mp hq).2 with ⟨hqPrime, _, hqUpper⟩
  have hNr : 1 < (N : ℝ) := by exact_mod_cast hN
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hqPrime.pos
  have hbase : (1 : ℝ) ≤ (N : ℝ) := hNr.le
  have hDeltaOne :
      (1 : ℝ) ≤ (N : ℝ) ^ (1 / 2 - ε) / (q : ℝ) := by
    rw [le_div_iff₀ hqr]
    calc
      (1 : ℝ) * (q : ℝ) = (q : ℝ) := one_mul _
      _ ≤ (N : ℝ) ^ (1 / 3 : ℝ) := hqUpper
      _ ≤ (N : ℝ) ^ (1 / 2 - ε) :=
        Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  have hlevelOne : 1 < jurkatRichertSourceUpperLevel N q ε := by
    unfold jurkatRichertSourceUpperLevel
    have hfloor :
        1 ≤ Nat.floor ((N : ℝ) ^ (1 / 2 - ε) / (q : ℝ)) :=
      Nat.le_floor (by exact_mod_cast hDeltaOne)
    omega
  apply LinearSieve.upperRosserWeight_certificate
    (jurkatRichertSourceSiftingProduct_squarefree N)
    (jurkatRichertSourceSiftingProduct_ne_zero N) hlevelOne
  intro p hp
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpDvd : p ∣ jurkatRichertSourceSiftingProduct N :=
    (Nat.mem_primeFactors_of_ne_zero
      (jurkatRichertSourceSiftingProduct_ne_zero N)).mp hp |>.2
  have hpCutoff :
      (p : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) :=
    (prime_dvd_jurkatRichertSourceSiftingProduct hpPrime).mp hpDvd |>.2.1
  have hpowDelta :
      (N : ℝ) ^ (1 / 10 : ℝ) ≤
        (N : ℝ) ^ (1 / 2 - ε) / (q : ℝ) := by
    rw [le_div_iff₀ hqr]
    calc
      (N : ℝ) ^ (1 / 10 : ℝ) * (q : ℝ) ≤
          (N : ℝ) ^ (1 / 10 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left hqUpper
          (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      _ = (N : ℝ) ^ ((1 / 10 : ℝ) + 1 / 3) := by
        rw [Real.rpow_add (by positivity : 0 < (N : ℝ))]
      _ ≤ (N : ℝ) ^ (1 / 2 - ε) :=
        Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  have hpFloor :
      p ≤ Nat.floor ((N : ℝ) ^ (1 / 2 - ε) / (q : ℝ)) :=
    Nat.le_floor (hpCutoff.trans hpowDelta)
  unfold jurkatRichertSourceUpperLevel
  omega

/-- The exact sum of the q-conditioned upper Rosser main terms. -/
noncomputable def jurkatRichertSourceVaryingQMainSum
    (N : ℕ) (ε : ℝ) : ℝ :=
  (jurkatRichertSourceMediumPrimes N).sum (fun q =>
    (jurkatRichertSourceConditionedBoundingSieve N q).totalMass *
      (jurkatRichertSourceConditionedBoundingSieve N q).mainSum
        (jurkatRichertSourceVaryingQUpperRosserWeight N q ε))

/-- The exact sum of the q-conditioned, level-`D/q` upper Rosser remainders. -/
noncomputable def jurkatRichertSourceVaryingQRemainderSum
    (N : ℕ) (ε : ℝ) : ℝ :=
  (jurkatRichertSourceMediumPrimes N).sum (fun q =>
    LinearSieve.upperErrSum (jurkatRichertSourceConditionedBoundingSieve N q)
      (jurkatRichertSourceUpperLevel N q ε)
      (jurkatRichertSourceVaryingQUpperRosserWeight N q ε))

/-- A source medium prime is coprime to every divisor of the source sifting
product: the prime lies strictly above `N^(1/10)`, whereas every prime factor of
the product lies at or below that cutoff. -/
theorem jurkatRichertSourceMediumPrime_coprime_siftingDivisor
    {N q d : ℕ} (hq : q ∈ jurkatRichertSourceMediumPrimes N)
    (hd : d ∣ jurkatRichertSourceSiftingProduct N) :
    q.Coprime d := by
  rcases Finset.mem_filter.mp hq with ⟨_, hqPrime, hqLower, _⟩
  have hqProduct : q.Coprime (jurkatRichertSourceSiftingProduct N) := by
    rw [hqPrime.coprime_iff_not_dvd]
    intro hqDvd
    have hqUpper :=
      (prime_dvd_jurkatRichertSourceSiftingProduct hqPrime).mp hqDvd |>.2.1
    exact (not_lt_of_ge hqUpper) hqLower
  exact hqProduct.coprime_dvd_right hd

/-- The conditioned `multSum` is exactly the source prime-support count in the
single progression modulo `q*d`. -/
theorem jurkatRichertSourceConditionedMultSum_eq_modEq_count
    (N q d : ℕ) (hEven : Even N) (hN : 2 < N)
    (hq : q ∈ jurkatRichertSourceMediumPrimes N)
    (hd : d ∣ jurkatRichertSourceSiftingProduct N) :
    (jurkatRichertSourceConditionedBoundingSieve N q).multSum d =
      (((jurkatRichertSourceUnsiftedPrimeSupport N).filter
        (fun p => p ≡ N [MOD q * d])).card : ℝ) := by
  have hcop := jurkatRichertSourceMediumPrime_coprime_siftingDivisor hq hd
  have hsupport :
      (jurkatRichertSourceConditionedSupport N q).filter (fun a => d ∣ a) =
        (jurkatRichertSourceUnsiftedComplements N).filter
          (fun a => q * d ∣ a) := by
    ext a
    simp only [jurkatRichertSourceConditionedSupport, Finset.mem_filter]
    constructor
    · rintro ⟨⟨ha, hqa⟩, hda⟩
      refine ⟨ha, ?_⟩
      rw [← hcop.lcm_eq_mul]
      exact Nat.lcm_dvd hqa hda
    · rintro ⟨ha, hqda⟩
      exact ⟨⟨ha, (dvd_trans (dvd_mul_right q d) hqda)⟩,
        dvd_trans (dvd_mul_left d q) hqda⟩
  unfold BoundingSieve.multSum
  change (∑ a ∈ jurkatRichertSourceConditionedSupport N q,
      if d ∣ a then (1 : ℝ) else 0) = _
  rw [Finset.sum_boole, hsupport,
    jurkatRichertSourceMultiples_card_eq_primeSupport]
  apply congrArg (fun s : Finset ℕ => (s.card : ℝ))
  apply Finset.filter_congr
  intro p hp
  have hpData := Finset.mem_filter.mp hp
  have hpLe : p ≤ N := by simpa using hpData.1
  have hpPrime : p.Prime := hpData.2.1
  have hpLt : p < N := by
    apply lt_of_le_of_ne hpLe
    intro hpEq
    have hNPrime : N.Prime := hpEq ▸ hpPrime
    have hN2 : N = 2 := hNPrime.even_iff.mp hEven
    omega
  exact AnalyticNumberTheory.Sieve.prime_dvd_complement_iff_modEq hpLt

/-- On the source divisor carrier, the conditioned remainder is the exact
prime-support AP count modulo `q*d`, centered at `li(N)/φ(q*d)`. -/
theorem jurkatRichertSourceConditionedRem_eq_modEq_count
    (N q d : ℕ) (hEven : Even N) (hN : 2 < N)
    (hq : q ∈ jurkatRichertSourceMediumPrimes N)
    (hd : d ∣ jurkatRichertSourceSiftingProduct N) :
    (jurkatRichertSourceConditionedBoundingSieve N q).rem d =
      (((jurkatRichertSourceUnsiftedPrimeSupport N).filter
          (fun p => p ≡ N [MOD q * d])).card : ℝ) -
        BombieriVinogradov.trueLogarithmicIntegral N / Nat.totient (q * d) := by
  have hqPrime := (Finset.mem_filter.mp hq).2.1
  have hcop := jurkatRichertSourceMediumPrime_coprime_siftingDivisor hq hd
  have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hd
    (Nat.pos_of_ne_zero (jurkatRichertSourceSiftingProduct_ne_zero N))
  have htotient : (Nat.totient d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hdPos).ne'
  have hqSub : (q : ℝ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hqPrime.ne_one)
  change
    (jurkatRichertSourceConditionedBoundingSieve N q).multSum d -
        AnalyticNumberTheory.Sieve.goldbachNu d *
          (LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N /
            ((q : ℝ) - 1)) = _
  rw [jurkatRichertSourceConditionedMultSum_eq_modEq_count N q d hEven hN hq hd,
    jurkatRichertSource_goldbachNu_eq_inv_totient hd,
    Nat.totient_mul hcop, Nat.totient_prime hqPrime]
  simp only [BombieriVinogradov.trueLogarithmicIntegral]
  push_cast [hqPrime.one_lt.le]
  field_simp [htotient, hqSub]

/-- Membership in the exact integer level `⌊N^(1/2-ε)/q⌋ + 1` implies the
required real modulus cutoff, including the floor endpoint. -/
theorem jurkatRichertSourceUpperLevel_mul_le
    {N q d : ℕ} {ε : ℝ}
    (hq : q ∈ jurkatRichertSourceMediumPrimes N)
    (hd : d < jurkatRichertSourceUpperLevel N q ε) :
    ((q * d : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / 2 - ε) := by
  have hqPrime := (Finset.mem_filter.mp hq).2.1
  have hqPos : (0 : ℝ) < q := by exact_mod_cast hqPrime.pos
  have hquotNonneg :
      0 ≤ (N : ℝ) ^ (1 / 2 - ε) / (q : ℝ) := by positivity
  have hdFloor :
      d ≤ Nat.floor ((N : ℝ) ^ (1 / 2 - ε) / (q : ℝ)) := by
    unfold jurkatRichertSourceUpperLevel at hd
    omega
  have hdQuot :
      (d : ℝ) ≤ (N : ℝ) ^ (1 / 2 - ε) / (q : ℝ) := by
    exact (by exact_mod_cast hdFloor : (d : ℝ) ≤
      Nat.floor ((N : ℝ) ^ (1 / 2 - ε) / (q : ℝ))).trans
        (Nat.floor_le hquotNonneg)
  rw [Nat.cast_mul]
  simpa [mul_comm] using (le_div_iff₀ hqPos).mp hdQuot

/-- If the medium prime does not divide `N`, then `N mod (q*d)` is the
canonical reduced residue for the combined modulus. -/
theorem jurkatRichertSource_mul_mod_coprime
    {N q d : ℕ} (hq : q ∈ jurkatRichertSourceMediumPrimes N)
    (hd : d ∣ jurkatRichertSourceSiftingProduct N) (hqN : ¬q ∣ N) :
    (N % (q * d)).Coprime (q * d) := by
  have hqPrime := (Finset.mem_filter.mp hq).2.1
  have hqCoprimeN : q.Coprime N := hqPrime.coprime_iff_not_dvd.mpr hqN
  have hdCoprimeN : d.Coprime N :=
    (jurkatRichertSourceSiftingProduct_coprime_N N).coprime_dvd_left hd
  have hNProduct : N.Coprime (q * d) :=
    (hqCoprimeN.mul_left hdCoprimeN).symm
  exact (ZMod.coprime_mod_iff_coprime N (q * d)).2 hNProduct

/-- The preceding canonical residue belongs to the standard reduced-residue
carrier used by the Bombieri--Vinogradov maximum. -/
theorem jurkatRichertSource_mul_mod_mem_unitResidues
    {N q d : ℕ} (hq : q ∈ jurkatRichertSourceMediumPrimes N)
    (hd : d ∣ jurkatRichertSourceSiftingProduct N) (hqN : ¬q ∣ N) :
    N % (q * d) ∈ AnalyticNumberTheory.Sieve.unitResidues (q * d) := by
  have hqPos := (Finset.mem_filter.mp hq).2.1.pos
  have hdPos := Nat.pos_of_dvd_of_pos hd
    (Nat.pos_of_ne_zero (jurkatRichertSourceSiftingProduct_ne_zero N))
  rw [AnalyticNumberTheory.Sieve.unitResidues]
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (Nat.mod_lt _ (Nat.mul_pos hqPos hdPos)),
      jurkatRichertSource_mul_mod_coprime hq hd hqN⟩

/-- The map `(q,d) ↦ q*d` is injective on medium primes times source sifting
divisors. -/
theorem jurkatRichertSource_mediumPrime_mul_siftingDivisor_injective
    {N q₁ q₂ d₁ d₂ : ℕ}
    (hq₁ : q₁ ∈ jurkatRichertSourceMediumPrimes N)
    (hq₂ : q₂ ∈ jurkatRichertSourceMediumPrimes N)
    (_hd₁ : d₁ ∣ jurkatRichertSourceSiftingProduct N)
    (hd₂ : d₂ ∣ jurkatRichertSourceSiftingProduct N)
    (hmul : q₁ * d₁ = q₂ * d₂) :
    q₁ = q₂ ∧ d₁ = d₂ := by
  have hq₁Prime := (Finset.mem_filter.mp hq₁).2.1
  have hq₂Prime := (Finset.mem_filter.mp hq₂).2.1
  have hq₁d₂ :=
    jurkatRichertSourceMediumPrime_coprime_siftingDivisor hq₁ hd₂
  have hq₁Dvd : q₁ ∣ q₂ * d₂ := by
    rw [← hmul]
    exact dvd_mul_right q₁ d₁
  have hqEq : q₁ = q₂ := by
    rcases hq₁Prime.dvd_or_dvd hq₁Dvd with hq₁q₂ | hq₁d₂'
    · exact ((Nat.dvd_prime hq₂Prime).mp hq₁q₂).resolve_left hq₁Prime.ne_one
    · exact False.elim (hq₁Prime.coprime_iff_not_dvd.mp hq₁d₂ hq₁d₂')
  subst q₂
  exact ⟨rfl, Nat.mul_left_cancel hq₁Prime.pos hmul⟩

/-- The genuinely `3^ω`-weighted standard AP-error sum on Chen's exact reduced
`(q,d)` carrier.  The modulus is `q*d`, not `d`, and the strict integer level is
the floor-safe source level `⌊N^(1/2-ε)/q⌋ + 1`.

There is no hidden multiplicity in this sum: the preceding injectivity theorem
shows that `(q,d) ↦ q*d` has fibres of cardinality one on this carrier. -/
noncomputable def jurkatRichertSourceReducedWeightedBVSum
    (N : ℕ) (ε : ℝ) : ℝ :=
  ∑ q ∈ (jurkatRichertSourceMediumPrimes N).filter (fun q => ¬q ∣ N),
    ∑ d ∈ (jurkatRichertSourceSiftingProduct N).divisors.filter
        (fun d => d < jurkatRichertSourceUpperLevel N q ε),
      (3 : ℝ) ^ d.primeFactors.card *
        BombieriVinogradov.standardPrimeAPMaxError N (q * d)

/-- **Source-faithful divisor-weighted Bombieri--Vinogradov interface.**

For every positive logarithmic saving, this controls the actual reduced
`(q,d)` carrier occurring in Chen's varying-`q` upper sieve, with its genuine
`3^ω(d)` Rosser majorant and modulus `q*d`. The proof from ordinary
`StandardBombieriVinogradov` is supplied downstream by
`Richert1969.chenWeightedBombieriVinogradov_of_standard`; the unconditional
instance is in `ChenVaryingQWeightedBVUnconditional`. Fibre uniqueness is supplied by
`jurkatRichertSource_mediumPrime_mul_siftingDivisor_injective`, so this
pair-indexed formulation counts every combined modulus with multiplicity one. -/
def ChenJurkatRichertVaryingQWeightedBombieriVinogradov : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
    ∀ A : ℝ, 0 < A →
      ∃ C : ℝ, 0 < C ∧
        ∀ᶠ N : ℕ in Filter.atTop,
          jurkatRichertSourceReducedWeightedBVSum N ε ≤
            C * (N : ℝ) / Real.log N ^ A

/-- The total `3^ω(d)` mass of the exact varying-level divisor carrier. -/
noncomputable def jurkatRichertSourceVaryingQWeightMass
    (N : ℕ) (ε : ℝ) : ℝ :=
  ∑ q ∈ jurkatRichertSourceMediumPrimes N,
    ∑ d ∈ (jurkatRichertSourceSiftingProduct N).divisors.filter
        (fun d => d < jurkatRichertSourceUpperLevel N q ε),
      (3 : ℝ) ^ d.primeFactors.card

/-- The nonreduced (`q ∣ N`) main-term contribution left after bounding its
prime count by one.  This is kept outside the weighted BV hypothesis. -/
noncomputable def jurkatRichertSourceNonreducedCenterSum
    (N : ℕ) (ε : ℝ) : ℝ :=
  ∑ q ∈ (jurkatRichertSourceMediumPrimes N).filter (fun q => q ∣ N),
    ∑ d ∈ (jurkatRichertSourceSiftingProduct N).divisors.filter
        (fun d => d < jurkatRichertSourceUpperLevel N q ε),
      (3 : ℝ) ^ d.primeFactors.card *
        (BombieriVinogradov.trueLogarithmicIntegral N / Nat.totient (q * d))

/-- All source corrections not paid for by the weighted BV input: the removed
small prime fibres on reduced lanes, the at-most-one prime on nonreduced lanes,
and the nonreduced centering terms. -/
noncomputable def jurkatRichertSourceVaryingQUnconditionalCorrection
    (N : ℕ) (ε : ℝ) : ℝ :=
  (((jurkatRichertSourceExceptionalPrimes N).card : ℝ) + 1) *
      jurkatRichertSourceVaryingQWeightMass N ε +
    jurkatRichertSourceNonreducedCenterSum N ε

/-- On a reduced `q`-lane the exact conditioned source remainder is bounded by
the standard reduced-residue AP maximum plus the explicit removed-prime
correction. -/
theorem abs_jurkatRichertSourceConditionedRem_le_standardMax_add_exceptional
    (N q d : ℕ) (hEven : Even N) (hN : 2 < N)
    (hq : q ∈ jurkatRichertSourceMediumPrimes N)
    (hd : d ∣ jurkatRichertSourceSiftingProduct N) (hqN : ¬q ∣ N) :
    |(jurkatRichertSourceConditionedBoundingSieve N q).rem d| ≤
      BombieriVinogradov.standardPrimeAPMaxError N (q * d) +
        (jurkatRichertSourceExceptionalPrimes N).card := by
  rw [jurkatRichertSourceConditionedRem_eq_modEq_count N q d hEven hN hq hd]
  calc
    |(((jurkatRichertSourceUnsiftedPrimeSupport N).filter
          (fun p => p ≡ N [MOD q * d])).card : ℝ) -
        BombieriVinogradov.trueLogarithmicIntegral N / Nat.totient (q * d)| ≤
        |BombieriVinogradov.standardPrimeAPError N (q * d) (N % (q * d))| +
          (jurkatRichertSourceExceptionalPrimes N).card :=
      abs_jurkatRichertSource_AP_sub_trueLi_div_totient_le N (q * d)
    _ ≤ BombieriVinogradov.standardPrimeAPMaxError N (q * d) +
          (jurkatRichertSourceExceptionalPrimes N).card := by
      simpa [add_comm] using add_le_add_right
        (BombieriVinogradov.abs_standardPrimeAPError_le_max
          (jurkatRichertSource_mul_mod_mem_unitResidues hq hd hqN))
        ((jurkatRichertSourceExceptionalPrimes N).card : ℝ)

/-- If `q ∣ N`, every prime in the conditioned progression modulo `q*d` equals
`q`; hence the exact source count on this nonreduced lane is at most one. -/
theorem jurkatRichertSourceConditioned_modEq_card_le_one_of_dvd
    (N q d : ℕ) (hq : q ∈ jurkatRichertSourceMediumPrimes N) (hqN : q ∣ N) :
    ((jurkatRichertSourceUnsiftedPrimeSupport N).filter
      (fun p => p ≡ N [MOD q * d])).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro p r hp hr
  rcases Finset.mem_filter.mp hp with ⟨hpSupport, hpMod⟩
  rcases Finset.mem_filter.mp hr with ⟨hrSupport, hrMod⟩
  have hqPrime := (Finset.mem_filter.mp hq).2.1
  have hpPrime := (Finset.mem_filter.mp hpSupport).2.1
  have hrPrime := (Finset.mem_filter.mp hrSupport).2.1
  have hqpd : q ∣ p := by
    have hqpN : p ≡ N [MOD q] :=
      hpMod.of_dvd (dvd_mul_right q d)
    exact (hqpN.dvd_iff (dvd_refl q)).mpr hqN
  have hqrd : q ∣ r := by
    have hqrN : r ≡ N [MOD q] :=
      hrMod.of_dvd (dvd_mul_right q d)
    exact (hqrN.dvd_iff (dvd_refl q)).mpr hqN
  have hpq : p = q :=
    (((Nat.dvd_prime hpPrime).mp hqpd).resolve_left hqPrime.ne_one).symm
  have hrq : r = q :=
    (((Nat.dvd_prime hrPrime).mp hqrd).resolve_left hqPrime.ne_one).symm
  omega

/-- The exact nonreduced conditioned remainder is bounded without any
Bombieri--Vinogradov input. -/
theorem abs_jurkatRichertSourceConditionedRem_le_one_add_center_of_dvd
    (N q d : ℕ) (hEven : Even N) (hN : 2 < N)
    (hq : q ∈ jurkatRichertSourceMediumPrimes N)
    (hd : d ∣ jurkatRichertSourceSiftingProduct N) (hqN : q ∣ N) :
    |(jurkatRichertSourceConditionedBoundingSieve N q).rem d| ≤
      1 + BombieriVinogradov.trueLogarithmicIntegral N / Nat.totient (q * d) := by
  rw [jurkatRichertSourceConditionedRem_eq_modEq_count N q d hEven hN hq hd]
  have hcard :=
    jurkatRichertSourceConditioned_modEq_card_le_one_of_dvd N q d hq hqN
  have hcountNonneg : 0 ≤
      (((jurkatRichertSourceUnsiftedPrimeSupport N).filter
        (fun p => p ≡ N [MOD q * d])).card : ℝ) := Nat.cast_nonneg _
  have hcountOne : (((jurkatRichertSourceUnsiftedPrimeSupport N).filter
      (fun p => p ≡ N [MOD q * d])).card : ℝ) ≤ 1 := by
    exact_mod_cast hcard
  have hcenterNonneg :
      0 ≤ BombieriVinogradov.trueLogarithmicIntegral N / Nat.totient (q * d) := by
    apply div_nonneg
    · exact LiuWeight.liuLogarithmicIntegral_nonneg
        (2 / Real.log 2) (by positivity) (by exact_mod_cast (show 2 ≤ N by omega))
    · exact Nat.cast_nonneg _
  calc
    |(((jurkatRichertSourceUnsiftedPrimeSupport N).filter
          (fun p => p ≡ N [MOD q * d])).card : ℝ) -
        BombieriVinogradov.trueLogarithmicIntegral N / Nat.totient (q * d)| ≤
        |(((jurkatRichertSourceUnsiftedPrimeSupport N).filter
          (fun p => p ≡ N [MOD q * d])).card : ℝ)| +
          |BombieriVinogradov.trueLogarithmicIntegral N / Nat.totient (q * d)| :=
      abs_sub _ _
    _ = (((jurkatRichertSourceUnsiftedPrimeSupport N).filter
          (fun p => p ≡ N [MOD q * d])).card : ℝ) +
          BombieriVinogradov.trueLogarithmicIntegral N / Nat.totient (q * d) := by
      rw [abs_of_nonneg hcountNonneg, abs_of_nonneg hcenterNonneg]
    _ ≤ 1 + BombieriVinogradov.trueLogarithmicIntegral N / Nat.totient (q * d) :=
      by
        simpa [add_comm] using
          (add_le_add_right hcountOne
            (BombieriVinogradov.trueLogarithmicIntegral N /
              (Nat.totient (q * d) : ℝ)))

/-- Exact expansion of `upperErrSum`, with reduced lanes paid for by the
genuinely weighted BV sum and every nonreduced or source-support correction
left in the explicit unconditional term. -/
theorem jurkatRichertSourceVaryingQRemainderSum_le_weightedBV_add_correction
    (N : ℕ) (ε : ℝ) (hEven : Even N) (hN : 2 < N) :
    jurkatRichertSourceVaryingQRemainderSum N ε ≤
      jurkatRichertSourceReducedWeightedBVSum N ε +
        jurkatRichertSourceVaryingQUnconditionalCorrection N ε := by
  let Q := jurkatRichertSourceMediumPrimes N
  let P := jurkatRichertSourceSiftingProduct N
  let E : ℝ := (jurkatRichertSourceExceptionalPrimes N).card
  let D : ℕ → Finset ℕ := fun q =>
    P.divisors.filter (fun d => d < jurkatRichertSourceUpperLevel N q ε)
  let w : ℕ → ℝ := fun d => (3 : ℝ) ^ d.primeFactors.card
  let R : ℕ → ℝ := fun q =>
    LinearSieve.upperErrSum (jurkatRichertSourceConditionedBoundingSieve N q)
      (jurkatRichertSourceUpperLevel N q ε)
      (jurkatRichertSourceVaryingQUpperRosserWeight N q ε)
  let M : ℕ → ℝ := fun q =>
    ∑ d ∈ D q, w d
  let B : ℕ → ℝ := fun q =>
    ∑ d ∈ D q, w d *
      BombieriVinogradov.standardPrimeAPMaxError N (q * d)
  let C : ℕ → ℝ := fun q =>
    ∑ d ∈ D q, w d *
      (BombieriVinogradov.trueLogarithmicIntegral N / Nat.totient (q * d))
  have hredPoint : ∀ q ∈ Q, ¬q ∣ N → R q ≤ B q + E * M q := by
    intro q hq hqN
    have hq' : q ∈ jurkatRichertSourceMediumPrimes N := by simpa [Q] using hq
    unfold R LinearSieve.upperErrSum
    change (∑ d ∈ D q,
      |jurkatRichertSourceVaryingQUpperRosserWeight N q ε d| *
        |(jurkatRichertSourceConditionedBoundingSieve N q).rem d|) ≤ _
    calc
      (∑ d ∈ D q,
          |jurkatRichertSourceVaryingQUpperRosserWeight N q ε d| *
            |(jurkatRichertSourceConditionedBoundingSieve N q).rem d|) ≤
          ∑ d ∈ D q, w d *
            (BombieriVinogradov.standardPrimeAPMaxError N (q * d) + E) := by
        apply Finset.sum_le_sum
        intro d hd
        rcases Finset.mem_filter.mp hd with ⟨hdDivMem, _⟩
        have hdvd : d ∣ jurkatRichertSourceSiftingProduct N :=
          Nat.dvd_of_mem_divisors hdDivMem
        exact mul_le_mul
          (abs_jurkatRichertSourceVaryingQUpperRosserWeight_le_threePow N q d ε)
          (by
            simpa [E] using
              (abs_jurkatRichertSourceConditionedRem_le_standardMax_add_exceptional
                N q d hEven hN hq' hdvd hqN))
          (abs_nonneg _) (pow_nonneg (by norm_num) _)
      _ = B q + E * M q := by
        simp only [B, M]
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro d hd
        ring
  have hbadPoint : ∀ q ∈ Q, q ∣ N → R q ≤ M q + C q := by
    intro q hq hqN
    have hq' : q ∈ jurkatRichertSourceMediumPrimes N := by simpa [Q] using hq
    unfold R LinearSieve.upperErrSum
    change (∑ d ∈ D q,
      |jurkatRichertSourceVaryingQUpperRosserWeight N q ε d| *
        |(jurkatRichertSourceConditionedBoundingSieve N q).rem d|) ≤ _
    calc
      (∑ d ∈ D q,
          |jurkatRichertSourceVaryingQUpperRosserWeight N q ε d| *
            |(jurkatRichertSourceConditionedBoundingSieve N q).rem d|) ≤
          ∑ d ∈ D q, w d *
            (1 + BombieriVinogradov.trueLogarithmicIntegral N /
              Nat.totient (q * d)) := by
        apply Finset.sum_le_sum
        intro d hd
        rcases Finset.mem_filter.mp hd with ⟨hdDivMem, _⟩
        have hdvd : d ∣ jurkatRichertSourceSiftingProduct N :=
          Nat.dvd_of_mem_divisors hdDivMem
        exact mul_le_mul
          (abs_jurkatRichertSourceVaryingQUpperRosserWeight_le_threePow N q d ε)
          (abs_jurkatRichertSourceConditionedRem_le_one_add_center_of_dvd
            N q d hEven hN hq' hdvd hqN)
          (abs_nonneg _) (pow_nonneg (by norm_num) _)
      _ = M q + C q := by
        simp only [M, C, w]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro d hd
        ring
  have hsplit :
      ∑ q ∈ Q, R q =
        (∑ q ∈ Q.filter (fun q => ¬q ∣ N), R q) +
          ∑ q ∈ Q.filter (fun q => q ∣ N), R q := by
    have hs := Finset.sum_filter_add_sum_filter_not Q (fun q => q ∣ N) R
    calc
      ∑ q ∈ Q, R q =
          (∑ q ∈ Q.filter (fun q => q ∣ N), R q) +
            ∑ q ∈ Q.filter (fun q => ¬q ∣ N), R q := hs.symm
      _ = _ := add_comm _ _
  have hred :
      (∑ q ∈ Q.filter (fun q => ¬q ∣ N), R q) ≤
        (∑ q ∈ Q.filter (fun q => ¬q ∣ N), B q) +
          E * ∑ q ∈ Q.filter (fun q => ¬q ∣ N), M q := by
    calc
      (∑ q ∈ Q.filter (fun q => ¬q ∣ N), R q) ≤
          ∑ q ∈ Q.filter (fun q => ¬q ∣ N), (B q + E * M q) := by
        apply Finset.sum_le_sum
        intro q hq
        rcases Finset.mem_filter.mp hq with ⟨hqQ, hqN⟩
        exact hredPoint q hqQ hqN
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hbad :
      (∑ q ∈ Q.filter (fun q => q ∣ N), R q) ≤
        (∑ q ∈ Q.filter (fun q => q ∣ N), M q) +
          ∑ q ∈ Q.filter (fun q => q ∣ N), C q := by
    calc
      (∑ q ∈ Q.filter (fun q => q ∣ N), R q) ≤
          ∑ q ∈ Q.filter (fun q => q ∣ N), (M q + C q) := by
        apply Finset.sum_le_sum
        intro q hq
        rcases Finset.mem_filter.mp hq with ⟨hqQ, hqN⟩
        exact hbadPoint q hqQ hqN
      _ = _ := Finset.sum_add_distrib
  have hMnonneg : ∀ q, 0 ≤ M q := by
    intro q
    apply Finset.sum_nonneg
    intro d hd
    exact pow_nonneg (by norm_num) _
  have hMred :
      (∑ q ∈ Q.filter (fun q => ¬q ∣ N), M q) ≤ ∑ q ∈ Q, M q :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun q _ _ => hMnonneg q)
  have hMbad :
      (∑ q ∈ Q.filter (fun q => q ∣ N), M q) ≤ ∑ q ∈ Q, M q :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun q _ _ => hMnonneg q)
  unfold jurkatRichertSourceVaryingQRemainderSum
  change (∑ q ∈ Q, R q) ≤ _
  rw [hsplit]
  calc
    (∑ q ∈ Q.filter (fun q => ¬q ∣ N), R q) +
          ∑ q ∈ Q.filter (fun q => q ∣ N), R q ≤
        ((∑ q ∈ Q.filter (fun q => ¬q ∣ N), B q) +
          E * ∑ q ∈ Q.filter (fun q => ¬q ∣ N), M q) +
        ((∑ q ∈ Q.filter (fun q => q ∣ N), M q) +
          ∑ q ∈ Q.filter (fun q => q ∣ N), C q) :=
      add_le_add hred hbad
    _ ≤ (∑ q ∈ Q.filter (fun q => ¬q ∣ N), B q) +
        (E + 1) * (∑ q ∈ Q, M q) +
          ∑ q ∈ Q.filter (fun q => q ∣ N), C q := by
      have hE : 0 ≤ E := by dsimp [E]; positivity
      nlinarith [mul_le_mul_of_nonneg_left hMred hE, hMbad]
    _ = jurkatRichertSourceReducedWeightedBVSum N ε +
        jurkatRichertSourceVaryingQUnconditionalCorrection N ε := by
      simp only [jurkatRichertSourceReducedWeightedBVSum,
        jurkatRichertSourceVaryingQUnconditionalCorrection,
        jurkatRichertSourceVaryingQWeightMass,
        jurkatRichertSourceNonreducedCenterSum, Q, P, E, D, w, B, C, M]
      ring

/-- The source sifting product satisfies the uniform `3^ω/φ` divisor bound
needed for all correction terms. -/
theorem exists_jurkatRichertSource_divisorWeight_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      ∑ d ∈ (jurkatRichertSourceSiftingProduct N).divisors,
          (3 : ℝ) ^ d.primeFactors.card / Nat.totient d ≤
        C * Real.log N ^ (3 : ℕ) := by
  obtain ⟨C₀, hC₀⟩ :=
    SelbergUpperBound.divisor_sum_bound_squarefree (3 : ℝ) (by norm_num)
  refine ⟨|C₀| + 1, by positivity, ?_⟩
  intro N hN
  have hPpos : 1 ≤ jurkatRichertSourceSiftingProduct N :=
    Nat.one_le_iff_ne_zero.mpr (jurkatRichertSourceSiftingProduct_ne_zero N)
  have hprimeBound : ∀ p : ℕ, p.Prime →
      p ∣ jurkatRichertSourceSiftingProduct N → p ≤ N := by
    intro p hp hpd
    have hpCutoff :=
      (prime_dvd_jurkatRichertSourceSiftingProduct hp).mp hpd |>.2.1
    have hpowN : (N : ℝ) ^ (1 / 10 : ℝ) ≤ N :=
      Real.rpow_le_self_of_one_le (by exact_mod_cast (show 1 ≤ N by omega))
        (by norm_num)
    exact_mod_cast hpCutoff.trans hpowN
  have hraw := hC₀ (jurkatRichertSourceSiftingProduct N) N hPpos
    (jurkatRichertSourceSiftingProduct_squarefree N) hprimeBound hN
  have hlogNonneg : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  calc
    ∑ d ∈ (jurkatRichertSourceSiftingProduct N).divisors,
          (3 : ℝ) ^ d.primeFactors.card / Nat.totient d ≤
        C₀ * Real.log N ^ (3 : ℝ) := hraw
    _ ≤ (|C₀| + 1) * Real.log N ^ (3 : ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (le_trans (le_abs_self C₀) (by linarith)) (Real.rpow_nonneg hlogNonneg _)
    _ = (|C₀| + 1) * Real.log N ^ (3 : ℕ) := by
      norm_num [Real.rpow_natCast]

/-- The medium-prime carrier has the elementary cardinality bound supplied by
its upper cutoff `q ≤ N^(1/3)`. -/
theorem jurkatRichertSourceMediumPrimes_card_cast_le
    (N : ℕ) (hN : 1 ≤ N) :
    ((jurkatRichertSourceMediumPrimes N).card : ℝ) ≤
      2 * (N : ℝ) ^ (1 / 3 : ℝ) := by
  let R := Finset.range (Nat.floor ((N : ℝ) ^ (1 / 3 : ℝ)) + 1)
  have hsub : jurkatRichertSourceMediumPrimes N ⊆ R := by
    intro q hq
    have hqUpper := (Finset.mem_filter.mp hq).2.2.2
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Nat.le_floor hqUpper))
  have hcardNat :
      (jurkatRichertSourceMediumPrimes N).card ≤
        Nat.floor ((N : ℝ) ^ (1 / 3 : ℝ)) + 1 := by
    simpa [R] using Finset.card_le_card hsub
  have hcard :
      ((jurkatRichertSourceMediumPrimes N).card : ℝ) ≤
        (Nat.floor ((N : ℝ) ^ (1 / 3 : ℝ)) + 1 : ℕ) := by
    exact_mod_cast hcardNat
  have hfloor :
      (Nat.floor ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ) ≤
        (N : ℝ) ^ (1 / 3 : ℝ) :=
    Nat.floor_le (by positivity)
  have hone : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  norm_num at hcard
  linarith

/-- The total coefficient mass on all varying levels is power-saving before any
analytic distribution theorem is used. -/
theorem jurkatRichertSourceVaryingQWeightMass_le
    (C : ℝ)
    (hC : ∀ N : ℕ, 3 ≤ N →
      ∑ d ∈ (jurkatRichertSourceSiftingProduct N).divisors,
          (3 : ℝ) ^ d.primeFactors.card / Nat.totient d ≤
        C * Real.log N ^ (3 : ℕ))
    (N : ℕ) (ε : ℝ) (hN : 3 ≤ N) (hε : 0 < ε) :
    jurkatRichertSourceVaryingQWeightMass N ε ≤
      2 * C * (N : ℝ) ^ (5 / 6 : ℝ) * Real.log N ^ (3 : ℕ) := by
  let P := jurkatRichertSourceSiftingProduct N
  let L : ℝ := (N : ℝ) ^ (1 / 2 : ℝ)
  have hbase : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hinner : ∀ q ∈ jurkatRichertSourceMediumPrimes N,
      (∑ d ∈ P.divisors.filter
          (fun d => d < jurkatRichertSourceUpperLevel N q ε),
        (3 : ℝ) ^ d.primeFactors.card) ≤
        L * (C * Real.log N ^ (3 : ℕ)) := by
    intro q hq
    calc
      (∑ d ∈ P.divisors.filter
          (fun d => d < jurkatRichertSourceUpperLevel N q ε),
          (3 : ℝ) ^ d.primeFactors.card) ≤
          ∑ d ∈ P.divisors.filter
              (fun d => d < jurkatRichertSourceUpperLevel N q ε),
            L * ((3 : ℝ) ^ d.primeFactors.card / Nat.totient d) := by
        apply Finset.sum_le_sum
        intro d hd
        rcases Finset.mem_filter.mp hd with ⟨hdDivMem, hdLevel⟩
        have hdvd : d ∣ jurkatRichertSourceSiftingProduct N :=
          Nat.dvd_of_mem_divisors hdDivMem
        have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hdvd
          (Nat.pos_of_ne_zero (jurkatRichertSourceSiftingProduct_ne_zero N))
        have hqPos := (Finset.mem_filter.mp hq).2.1.pos
        have hmul :=
          jurkatRichertSourceUpperLevel_mul_le hq hdLevel
        have hexponent : 1 / 2 - ε ≤ (1 / 2 : ℝ) := by linarith
        have hpow :
            (N : ℝ) ^ (1 / 2 - ε) ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hbase hexponent
        have hdL : (d : ℝ) ≤ L := by
          dsimp [L]
          have hdqd : (d : ℝ) ≤ (q * d : ℕ) := by
            exact_mod_cast (Nat.le_mul_of_pos_left d hqPos)
          exact hdqd.trans (hmul.trans hpow)
        have hφPos : (0 : ℝ) < Nat.totient d := by
          exact_mod_cast (Nat.totient_pos.mpr hdPos)
        have hφL : (Nat.totient d : ℝ) ≤ L :=
          (by exact_mod_cast Nat.totient_le d : (Nat.totient d : ℝ) ≤ d) |>.trans hdL
        have hwNonneg : 0 ≤ (3 : ℝ) ^ d.primeFactors.card := by positivity
        calc
          (3 : ℝ) ^ d.primeFactors.card =
              (Nat.totient d : ℝ) *
                ((3 : ℝ) ^ d.primeFactors.card / Nat.totient d) := by
            field_simp [hφPos.ne']
          _ ≤ L * ((3 : ℝ) ^ d.primeFactors.card / Nat.totient d) :=
            mul_le_mul_of_nonneg_right hφL (div_nonneg hwNonneg hφPos.le)
      _ ≤ ∑ d ∈ P.divisors,
            L * ((3 : ℝ) ^ d.primeFactors.card / Nat.totient d) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro d hd hdnot
        positivity
      _ = L * (∑ d ∈ P.divisors,
            (3 : ℝ) ^ d.primeFactors.card / Nat.totient d) := by
        rw [Finset.mul_sum]
      _ ≤ L * (C * Real.log N ^ (3 : ℕ)) :=
        mul_le_mul_of_nonneg_left (hC N hN) (by positivity)
  unfold jurkatRichertSourceVaryingQWeightMass
  change (∑ q ∈ jurkatRichertSourceMediumPrimes N,
    ∑ d ∈ P.divisors.filter
      (fun d => d < jurkatRichertSourceUpperLevel N q ε),
      (3 : ℝ) ^ d.primeFactors.card) ≤ _
  calc
    _ ≤ ∑ _q ∈ jurkatRichertSourceMediumPrimes N,
        L * (C * Real.log N ^ (3 : ℕ)) :=
      Finset.sum_le_sum hinner
    _ = ((jurkatRichertSourceMediumPrimes N).card : ℝ) *
        (L * (C * Real.log N ^ (3 : ℕ))) := by
      simp [nsmul_eq_mul]
    _ ≤ (2 * (N : ℝ) ^ (1 / 3 : ℝ)) *
        (L * (C * Real.log N ^ (3 : ℕ))) := by
      apply mul_le_mul_of_nonneg_right
        (jurkatRichertSourceMediumPrimes_card_cast_le N (by omega))
      have hsumNonneg : 0 ≤
          ∑ d ∈ (jurkatRichertSourceSiftingProduct N).divisors,
            (3 : ℝ) ^ d.primeFactors.card / Nat.totient d := by positivity
      have hCLogNonneg : 0 ≤ C * Real.log N ^ (3 : ℕ) :=
        hsumNonneg.trans (hC N hN)
      exact mul_nonneg (by positivity) hCLogNonneg
    _ = 2 * C * (N : ℝ) ^ (5 / 6 : ℝ) *
        Real.log N ^ (3 : ℕ) := by
      dsimp [L]
      have hpows :
          (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) =
            (N : ℝ) ^ (5 / 6 : ℝ) := by
        rw [← Real.rpow_add (by positivity : (0 : ℝ) < N)]
        norm_num
      rw [show
        2 * (N : ℝ) ^ (1 / 3 : ℝ) *
              ((N : ℝ) ^ (1 / 2 : ℝ) * (C * Real.log N ^ (3 : ℕ))) =
            2 * C *
              ((N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ)) *
                Real.log N ^ (3 : ℕ) by ring, hpows]

/-- Medium primes in the nonreduced lane are distinct prime divisors of `N`. -/
theorem jurkatRichertSourceNonreducedPrimes_card_le_primeFactors
    (N : ℕ) (hN : 0 < N) :
    ((jurkatRichertSourceMediumPrimes N).filter (fun q => q ∣ N)).card ≤
      N.primeFactors.card := by
  apply Finset.card_le_card
  intro q hq
  rcases Finset.mem_filter.mp hq with ⟨hqMedium, hqN⟩
  have hqPrime := (Finset.mem_filter.mp hqMedium).2.1
  exact (Nat.mem_primeFactors_of_ne_zero hN.ne').mpr ⟨hqPrime, hqN⟩

/-- The nonreduced centering terms have a power-saving factor because every
such medium prime divides `N` and is larger than `N^(1/10)`. -/
theorem jurkatRichertSourceNonreducedCenterSum_le
    (C : ℝ)
    (hC : ∀ N : ℕ, 3 ≤ N →
      ∑ d ∈ (jurkatRichertSourceSiftingProduct N).divisors,
          (3 : ℝ) ^ d.primeFactors.card / Nat.totient d ≤
        C * Real.log N ^ (3 : ℕ))
    (N : ℕ) (ε : ℝ) (hN : 3 ≤ N) :
    jurkatRichertSourceNonreducedCenterSum N ε ≤
      (Real.log N / Real.log 2) *
        ((2 * BombieriVinogradov.trueLogarithmicIntegral N /
            (N : ℝ) ^ (1 / 10 : ℝ)) *
          (C * Real.log N ^ (3 : ℕ))) := by
  let P := jurkatRichertSourceSiftingProduct N
  let Q := (jurkatRichertSourceMediumPrimes N).filter (fun q => q ∣ N)
  let li := BombieriVinogradov.trueLogarithmicIntegral N
  have hli : 0 ≤ li := by
    dsimp [li, BombieriVinogradov.trueLogarithmicIntegral]
    exact LiuWeight.liuLogarithmicIntegral_nonneg
      (2 / Real.log 2) (by positivity)
      (by exact_mod_cast (show 2 ≤ N by omega))
  have hpowPos : 0 < (N : ℝ) ^ (1 / 10 : ℝ) := by positivity
  have hdivisorNonneg :
      0 ≤ C * Real.log N ^ (3 : ℕ) := by
    have hsumNonneg : 0 ≤
        ∑ d ∈ P.divisors,
          (3 : ℝ) ^ d.primeFactors.card / Nat.totient d := by positivity
    exact hsumNonneg.trans (by simpa [P] using hC N hN)
  have hinner : ∀ q ∈ Q,
      (∑ d ∈ P.divisors.filter
          (fun d => d < jurkatRichertSourceUpperLevel N q ε),
        (3 : ℝ) ^ d.primeFactors.card *
          (li / Nat.totient (q * d))) ≤
        (2 * li / (N : ℝ) ^ (1 / 10 : ℝ)) *
          (C * Real.log N ^ (3 : ℕ)) := by
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqMedium, _hqN⟩
    have hqPrime := (Finset.mem_filter.mp hqMedium).2.1
    have hqLower := (Finset.mem_filter.mp hqMedium).2.2.1
    have hqSubPos : 0 < (q : ℝ) - 1 := by
      have hqTwo : (2 : ℝ) ≤ q := by exact_mod_cast hqPrime.two_le
      linarith
    have hInv :
        1 / ((q : ℝ) - 1) ≤ 2 / (N : ℝ) ^ (1 / 10 : ℝ) := by
      rw [div_le_div_iff₀ hqSubPos hpowPos]
      have hqTwo : (2 : ℝ) ≤ q := by exact_mod_cast hqPrime.two_le
      nlinarith
    have hfactor :
        li / ((q : ℝ) - 1) ≤
          2 * li / (N : ℝ) ^ (1 / 10 : ℝ) := by
      calc
        li / ((q : ℝ) - 1) = li * (1 / ((q : ℝ) - 1)) := by ring
        _ ≤ li * (2 / (N : ℝ) ^ (1 / 10 : ℝ)) :=
          mul_le_mul_of_nonneg_left hInv hli
        _ = 2 * li / (N : ℝ) ^ (1 / 10 : ℝ) := by ring
    calc
      (∑ d ∈ P.divisors.filter
          (fun d => d < jurkatRichertSourceUpperLevel N q ε),
          (3 : ℝ) ^ d.primeFactors.card * (li / Nat.totient (q * d))) =
          ∑ d ∈ P.divisors.filter
            (fun d => d < jurkatRichertSourceUpperLevel N q ε),
            (li / ((q : ℝ) - 1)) *
              ((3 : ℝ) ^ d.primeFactors.card / Nat.totient d) := by
        apply Finset.sum_congr rfl
        intro d hd
        rcases Finset.mem_filter.mp hd with ⟨hdDivMem, _⟩
        have hdvd : d ∣ jurkatRichertSourceSiftingProduct N :=
          Nat.dvd_of_mem_divisors hdDivMem
        have hcop :=
          jurkatRichertSourceMediumPrime_coprime_siftingDivisor hqMedium hdvd
        have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hdvd
          (Nat.pos_of_ne_zero (jurkatRichertSourceSiftingProduct_ne_zero N))
        have hφNe : (Nat.totient d : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.totient_pos.mpr hdPos).ne'
        rw [Nat.totient_mul hcop, Nat.totient_prime hqPrime]
        push_cast [hqPrime.one_lt.le]
        field_simp [hqSubPos.ne', hφNe]
      _ ≤ ∑ d ∈ P.divisors.filter
            (fun d => d < jurkatRichertSourceUpperLevel N q ε),
          (2 * li / (N : ℝ) ^ (1 / 10 : ℝ)) *
            ((3 : ℝ) ^ d.primeFactors.card / Nat.totient d) := by
        apply Finset.sum_le_sum
        intro d hd
        have hratioNonneg :
            0 ≤ (3 : ℝ) ^ d.primeFactors.card / Nat.totient d := by positivity
        exact mul_le_mul_of_nonneg_right hfactor hratioNonneg
      _ ≤ ∑ d ∈ P.divisors,
          (2 * li / (N : ℝ) ^ (1 / 10 : ℝ)) *
            ((3 : ℝ) ^ d.primeFactors.card / Nat.totient d) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro d hd hdnot
        positivity
      _ = (2 * li / (N : ℝ) ^ (1 / 10 : ℝ)) *
          (∑ d ∈ P.divisors,
            (3 : ℝ) ^ d.primeFactors.card / Nat.totient d) := by
        rw [Finset.mul_sum]
      _ ≤ (2 * li / (N : ℝ) ^ (1 / 10 : ℝ)) *
          (C * Real.log N ^ (3 : ℕ)) := by
        apply mul_le_mul_of_nonneg_left
        · simpa [P] using hC N hN
        · positivity
  have hcard :
      (Q.card : ℝ) ≤ Real.log N / Real.log 2 := by
    calc
      (Q.card : ℝ) ≤ (N.primeFactors.card : ℝ) := by
        exact_mod_cast
          jurkatRichertSourceNonreducedPrimes_card_le_primeFactors N (by omega)
      _ ≤ Real.log N / Real.log 2 :=
        LiuWeight.primeFactors_card_cast_le_log (by omega)
  unfold jurkatRichertSourceNonreducedCenterSum
  change (∑ q ∈ Q,
    ∑ d ∈ P.divisors.filter
        (fun d => d < jurkatRichertSourceUpperLevel N q ε),
      (3 : ℝ) ^ d.primeFactors.card *
        (li / Nat.totient (q * d))) ≤ _
  calc
    _ ≤ ∑ _q ∈ Q,
        (2 * li / (N : ℝ) ^ (1 / 10 : ℝ)) *
          (C * Real.log N ^ (3 : ℕ)) :=
      Finset.sum_le_sum hinner
    _ = (Q.card : ℝ) *
        ((2 * li / (N : ℝ) ^ (1 / 10 : ℝ)) *
          (C * Real.log N ^ (3 : ℕ))) := by
      simp [nsmul_eq_mul]
    _ ≤ (Real.log N / Real.log 2) *
        ((2 * li / (N : ℝ) ^ (1 / 10 : ℝ)) *
          (C * Real.log N ^ (3 : ℕ))) :=
      mul_le_mul_of_nonneg_right hcard
        (mul_nonneg (by positivity) hdivisorNonneg)

/-- A fixed multiple of `N^(9/10) log^4 N` is negligible on the singular-series
Goldbach scale. -/
private theorem eventually_nineTenths_logFour_le_liuSingularSeries
    (K δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      K * (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ (4 : ℕ) ≤
        δ * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) := by
  have hcore :
      Filter.Tendsto (fun N : ℕ =>
        Real.log (N : ℝ) ^ (6 : ℝ) / (N : ℝ) ^ (1 / 10 : ℝ))
        Filter.atTop (nhds 0) := by
    exact
      ((isLittleO_log_rpow_rpow_atTop (6 : ℝ)
        (by norm_num : (0 : ℝ) < 1 / 10)).tendsto_div_nhds_zero).comp
          tendsto_natCast_atTop_atTop
  have heq :
      (fun N : ℕ => K *
        (Real.log (N : ℝ) ^ (6 : ℝ) / (N : ℝ) ^ (1 / 10 : ℝ))) =ᶠ[Filter.atTop]
      (fun N : ℕ =>
        (K * (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ (4 : ℕ)) /
          ((N : ℝ) / Real.log N ^ (2 : ℕ))) := by
    filter_upwards [Filter.eventually_ge_atTop 2] with N hN
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hlogpos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    rw [show (9 / 10 : ℝ) = 1 - 1 / 10 by norm_num,
      Real.rpow_sub hNpos, Real.rpow_one, ← Real.rpow_natCast]
    field_simp [hNpos.ne', hlogpos.ne']
    norm_num [Real.rpow_natCast]
    ring
  have hratio :
      Filter.Tendsto (fun N : ℕ =>
        (K * (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ (4 : ℕ)) /
          ((N : ℝ) / Real.log N ^ (2 : ℕ)))
        Filter.atTop (nhds 0) := by
    exact ((hcore.const_mul K).congr' heq).trans (by simp)
  have hsmall : ∀ᶠ N : ℕ in Filter.atTop,
      (K * (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ (4 : ℕ)) /
          ((N : ℝ) / Real.log N ^ (2 : ℕ)) ≤
        δ * SingularSeries.liuUniversalProduct :=
    hratio.eventually (Iic_mem_nhds
      (mul_pos hδ SingularSeries.liuUniversalProduct_pos))
  filter_upwards [hsmall, Filter.eventually_ge_atTop 2] with N hsmallN hN
  have hscale : 0 < (N : ℝ) / Real.log N ^ (2 : ℕ) := by
    exact div_pos (by exact_mod_cast (show 0 < N by omega))
      (pow_pos (Real.log_pos (by exact_mod_cast (show 1 < N by omega))) _)
  rw [div_le_iff₀ hscale] at hsmallN
  calc
    K * (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ (4 : ℕ) ≤
        (δ * SingularSeries.liuUniversalProduct) *
          ((N : ℝ) / Real.log N ^ (2 : ℕ)) := hsmallN
    _ ≤ (δ * SingularSeries.liuSingularSeries N) *
          ((N : ℝ) / Real.log N ^ (2 : ℕ)) := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left
          (SingularSeries.liuUniversalProduct_le_liuSingularSeries N) hδ.le
      · exact hscale.le
    _ = δ * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) := by ring

/-- The nonreduced lanes and the source exceptional-prime corrections are
unconditionally power-saving.  No part of this estimate is included in the
weighted Bombieri--Vinogradov hypothesis. -/
theorem eventually_jurkatRichertSourceVaryingQUnconditionalCorrection_le
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      jurkatRichertSourceVaryingQUnconditionalCorrection N ε ≤
        δ * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) := by
  obtain ⟨C, hCpos, hC⟩ := exists_jurkatRichertSource_divisorWeight_bound
  let L := LiuWeight.liuLogarithmicIntegralUpperConstant (2 / Real.log 2)
  have hL : 0 ≤ L := LiuWeight.liuLogarithmicIntegralUpperConstant_nonneg _
  let K : ℝ := (4 + 2 * L) * C / Real.log 2
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hsmall :=
    eventually_nineTenths_logFour_le_liuSingularSeries K δ hδ
  filter_upwards [hsmall, Filter.eventually_ge_atTop 3] with
      N hsmallN hN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogOne : 1 ≤ Real.log (N : ℝ) := by
    have hlog3 : 1 ≤ Real.log (3 : ℝ) := by
      have h := le_log_one_add_of_nonneg (x := (2 : ℝ)) (by norm_num)
      norm_num at h
      exact h
    exact hlog3.trans (Real.strictMonoOn_log.monotoneOn
      (by norm_num) hNpos (by exact_mod_cast hN))
  have hE :=
    jurkatRichertSourceExceptionalPrimes_card_le_log N (by omega : 2 ≤ N)
  have hlogRatioOne : (1 : ℝ) ≤ Real.log N / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    simpa using
      (Real.strictMonoOn_log.monotoneOn
        (by norm_num : (0 : ℝ) < 2) hNpos
        (by exact_mod_cast (show 2 ≤ N by omega) : (2 : ℝ) ≤ N))
  have hEone :
      ((jurkatRichertSourceExceptionalPrimes N).card : ℝ) + 1 ≤
        2 * (Real.log N / Real.log 2) := by linarith
  have hmass :=
    jurkatRichertSourceVaryingQWeightMass_le C hC N ε hN hε
  have hmassNonneg :
      0 ≤ jurkatRichertSourceVaryingQWeightMass N ε := by
    unfold jurkatRichertSourceVaryingQWeightMass
    positivity
  have hfirst :
      (((jurkatRichertSourceExceptionalPrimes N).card : ℝ) + 1) *
          jurkatRichertSourceVaryingQWeightMass N ε ≤
        (4 * C / Real.log 2) * (N : ℝ) ^ (9 / 10 : ℝ) *
          Real.log N ^ (4 : ℕ) := by
    calc
      (((jurkatRichertSourceExceptionalPrimes N).card : ℝ) + 1) *
            jurkatRichertSourceVaryingQWeightMass N ε ≤
          (2 * (Real.log N / Real.log 2)) *
            (2 * C * (N : ℝ) ^ (5 / 6 : ℝ) *
              Real.log N ^ (3 : ℕ)) := by
        exact mul_le_mul hEone hmass hmassNonneg (by positivity)
      _ = (4 * C / Real.log 2) * (N : ℝ) ^ (5 / 6 : ℝ) *
            Real.log N ^ (4 : ℕ) := by ring
      _ ≤ (4 * C / Real.log 2) * (N : ℝ) ^ (9 / 10 : ℝ) *
            Real.log N ^ (4 : ℕ) := by
        have hpow := Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast (show 1 ≤ N by omega) : (1 : ℝ) ≤ N)
          (by norm_num : (5 / 6 : ℝ) ≤ 9 / 10)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
  have hcenter :=
    jurkatRichertSourceNonreducedCenterSum_le C hC N ε hN
  have hliN :
      BombieriVinogradov.trueLogarithmicIntegral N ≤
        L * (N : ℝ) / Real.log N := by
    have habs :=
      LiuWeight.liuLogarithmicIntegral_abs_le (2 / Real.log 2)
        (show (2 : ℝ) ≤ N by exact_mod_cast (show 2 ≤ N by omega))
    exact (le_abs_self _).trans (by
      simpa [BombieriVinogradov.trueLogarithmicIntegral, L] using habs)
  have hli' :
      2 * BombieriVinogradov.trueLogarithmicIntegral N /
          (N : ℝ) ^ (1 / 10 : ℝ) ≤
        2 * (L * (N : ℝ) / Real.log N) /
          (N : ℝ) ^ (1 / 10 : ℝ) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hliN (by norm_num))
      (by positivity)
  have hcenter' :
      jurkatRichertSourceNonreducedCenterSum N ε ≤
        (2 * L * C / Real.log 2) * (N : ℝ) ^ (9 / 10 : ℝ) *
          Real.log N ^ (4 : ℕ) := by
    calc
      jurkatRichertSourceNonreducedCenterSum N ε ≤
          (Real.log N / Real.log 2) *
            ((2 * BombieriVinogradov.trueLogarithmicIntegral N /
                (N : ℝ) ^ (1 / 10 : ℝ)) *
              (C * Real.log N ^ (3 : ℕ))) := hcenter
      _ ≤ (Real.log N / Real.log 2) *
            ((2 * (L * (N : ℝ) / Real.log N) /
                (N : ℝ) ^ (1 / 10 : ℝ)) *
              (C * Real.log N ^ (3 : ℕ))) := by
        gcongr
      _ = (2 * L * C / Real.log 2) * (N : ℝ) ^ (9 / 10 : ℝ) *
            Real.log N ^ (3 : ℕ) := by
        rw [show (9 / 10 : ℝ) = 1 - 1 / 10 by norm_num,
          Real.rpow_sub hNpos, Real.rpow_one]
        field_simp [hlog.ne', hlog2.ne', (Real.rpow_pos_of_pos hNpos _).ne']
      _ ≤ (2 * L * C / Real.log 2) * (N : ℝ) ^ (9 / 10 : ℝ) *
            Real.log N ^ (4 : ℕ) := by
        apply mul_le_mul_of_nonneg_left
        · have hlogCubeNonneg : 0 ≤ Real.log N ^ (3 : ℕ) := by positivity
          calc
            Real.log N ^ (3 : ℕ) =
                Real.log N ^ (3 : ℕ) * 1 := by ring
            _ ≤ Real.log N ^ (3 : ℕ) * Real.log N :=
              mul_le_mul_of_nonneg_left hlogOne hlogCubeNonneg
            _ = Real.log N ^ (4 : ℕ) := by ring
        · positivity
  unfold jurkatRichertSourceVaryingQUnconditionalCorrection
  calc
    _ ≤ (4 * C / Real.log 2) * (N : ℝ) ^ (9 / 10 : ℝ) *
          Real.log N ^ (4 : ℕ) +
    (2 * L * C / Real.log 2) * (N : ℝ) ^ (9 / 10 : ℝ) *
          Real.log N ^ (4 : ℕ) :=
      add_le_add hfirst hcenter'
    _ = K * (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ (4 : ℕ) := by
      dsimp [K]
      ring
    _ ≤ _ := hsmallN

/-- The q-conditioned finite upper sieves sum to Chen's literal medium-prime
aggregate, with no asymptotic step: only their exact main and remainder sums
remain. -/
theorem jurkatRichertSourceMediumPrimeAggregate_le_main_add_remainder
    (N : ℕ) (ε : ℝ) (hN : 1 < N) (hε : ε < 1 / 60) :
    jurkatRichertSourceMediumPrimeAggregate N ≤
      jurkatRichertSourceVaryingQMainSum N ε +
        jurkatRichertSourceVaryingQRemainderSum N ε := by
  unfold jurkatRichertSourceMediumPrimeAggregate
    jurkatRichertSourceVaryingQMainSum
    jurkatRichertSourceVaryingQRemainderSum
  calc
    _ ≤ (jurkatRichertSourceMediumPrimes N).sum (fun q =>
        (jurkatRichertSourceConditionedBoundingSieve N q).totalMass *
          (jurkatRichertSourceConditionedBoundingSieve N q).mainSum
            (jurkatRichertSourceVaryingQUpperRosserWeight N q ε) +
        LinearSieve.upperErrSum (jurkatRichertSourceConditionedBoundingSieve N q)
          (jurkatRichertSourceUpperLevel N q ε)
          (jurkatRichertSourceVaryingQUpperRosserWeight N q ε)) := by
      apply Finset.sum_le_sum
      intro q hq
      have hfinite :=
        LinearSieve.siftedSum_le_mainSum_add_upperErrSum_upperRosser
          (S := jurkatRichertSourceConditionedBoundingSieve N q)
          (D := jurkatRichertSourceUpperLevel N q ε)
          (jurkatRichertSourceVaryingQUpperRosserWeight_certificate hN hε hq)
      rw [jurkatRichertSourceConditionedBoundingSieve_siftedSum_eq_card] at hfinite
      exact hfinite
    _ = _ := Finset.sum_add_distrib

/-- Finite Fubini identity between Chen's displayed `q`-outer aggregate and the
distinct-prime divisor count attached to each source candidate. -/
theorem jurkatRichertSourceMediumPrimeAggregate_eq (N : ℕ) :
    jurkatRichertSourceMediumPrimeAggregate N =
      (jurkatRichertSourceCandidates N).sum (fun p =>
        (jurkatRichertSourceMediumPrimeCount N p : ℝ)) := by
  classical
  unfold jurkatRichertSourceMediumPrimeAggregate
    jurkatRichertSourceMediumPrimes jurkatRichertSourceMediumPrimeCount
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hprime : q.Prime
  <;> by_cases hlower : (N : ℝ) ^ (1 / 10 : ℝ) < (q : ℝ)
  <;> by_cases hupper : (q : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ)
  <;> by_cases hdvd : q ∣ N - p
  <;> simp_all

/-- The exact finite weighted-count identity used to consume the two sieve
asymptotics in Chen's Lemma 9. -/
theorem jurkatRichertSourceWeightedCount_eq (N : ℕ) :
    jurkatRichertSourceWeightedCount N =
      ((jurkatRichertSourceCandidates N).card : ℝ) -
        jurkatRichertSourceMediumPrimeAggregate N / 2 := by
  rw [jurkatRichertSourceMediumPrimeAggregate_eq]
  unfold jurkatRichertSourceWeightedCount
  rw [Finset.sum_sub_distrib, Finset.sum_div]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

/-- Above the fixed cutoff used in the finite comparison, the corrected lower
cutoff is exactly the floor of the source's real cutoff. -/
private theorem correctedChenZ_eq_floor_of_large (N : ℕ) (hNbig : 2 ^ 110 < N) :
    correctedChenZ N = Nat.floor ((N : ℝ) ^ (1 / 10 : ℝ)) := by
  unfold correctedChenZ
  apply max_eq_right
  apply Nat.le_floor
  have hroot := chenZ_root_large N hNbig
  norm_num at hroot ⊢
  linarith

/-- A corrected candidate has at most ten distinct medium prime divisors. -/
private theorem correctedChen_medium_prime_count_le_ten
    (N p : ℕ) (hNbig : 2 ^ 110 < N) (hp : p ∈ correctedChenCandidates N) :
    ((Finset.range (correctedChenY N)).filter
      (fun q => q.Prime ∧ correctedChenZ N ≤ q ∧ q ∣ N - p)).card ≤ 10 := by
  have hp' := Finset.mem_filter.mp hp
  have hpN : p < N := by simpa using hp'.1
  have hnpos : 0 < N - p := by omega
  apply le_trans (Finset.card_le_card ?_)
    (chenZ_tail_prime_count_le N (N - p) hNbig hnpos (by omega))
  intro q hq
  rcases Finset.mem_filter.mp hq with ⟨hqrange, hqprime, hqz, hqdvd⟩
  have hqle : q ≤ N - p := Nat.le_of_dvd hnpos hqdvd
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Ico.mpr ⟨hqz, by omega⟩, hqprime, hqdvd⟩

/-- On a candidate admitted by both finite carriers, every corrected medium
prime is also a source medium prime.  At the upper endpoint this uses
`q < ceil(N^(1/3)) → q < N^(1/3)`; the source may additionally contain the
exact integral upper endpoint. -/
private theorem correctedChen_medium_prime_count_le_source
    (N p : ℕ) (hNbig : 2 ^ 110 < N)
    (hpSource : p ∈ jurkatRichertSourceCandidates N)
    (hpCorrected : p ∈ correctedChenCandidates N) :
    ((Finset.range (correctedChenY N)).filter
      (fun q => q.Prime ∧ correctedChenZ N ≤ q ∧ q ∣ N - p)).card ≤
      jurkatRichertSourceMediumPrimeCount N p := by
  have hz3 : 3 ≤ correctedChenZ N := chenZ_ge_three N hNbig
  have hpS := Finset.mem_filter.mp hpSource
  have hpC := Finset.mem_filter.mp hpCorrected
  have hpN : p < N := by simpa using hpC.1
  have hnpos : 0 < N - p := by omega
  unfold jurkatRichertSourceMediumPrimeCount
  apply Finset.card_le_card
  intro q hq
  rcases Finset.mem_filter.mp hq with ⟨hqrange, hqprime, hqz, hqdvd⟩
  have hqle : q ≤ N - p := Nat.le_of_dvd hnpos hqdvd
  have hq2 : 2 < q := by omega
  have hqlower : (N : ℝ) ^ (1 / 10 : ℝ) < (q : ℝ) := by
    by_contra hnot
    exact (hpS.2.2 q hqprime hq2 (le_of_not_gt hnot)) hqdvd
  have hqupper : (q : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by
    exact le_of_lt (Nat.lt_ceil.mp (by simpa [correctedChenY] using hqrange))
  exact Finset.mem_filter.mpr
    ⟨by simpa using Nat.lt_succ_of_le (hqle.trans (Nat.sub_le N p)),
      hqprime, hqlower, hqupper, hqdvd⟩

/-- A corrected candidate omitted by the source carrier lies on the single
lower-floor fibre. -/
private theorem correctedChen_not_source_dvd_cutoff
    (N p : ℕ) (hNbig : 2 ^ 110 < N)
    (hpCorrected : p ∈ correctedChenCandidates N)
    (hpNotSource : p ∉ jurkatRichertSourceCandidates N) :
    correctedChenZ N ∣ N - p := by
  by_contra hzdvd
  apply hpNotSource
  have hpC := Finset.mem_filter.mp hpCorrected
  have hpN : p < N := by simpa using hpC.1
  refine Finset.mem_filter.mpr
    ⟨by simpa using Nat.lt_succ_of_le (Nat.le_of_lt hpN), hpC.2.1, ?_⟩
  intro r hrprime hr2 hrle hrdvd
  have hrlefloor : r ≤ Nat.floor ((N : ℝ) ^ (1 / 10 : ℝ)) :=
    Nat.le_floor hrle
  have hrlez : r ≤ correctedChenZ N := by
    rwa [correctedChenZ_eq_floor_of_large N hNbig]
  by_cases hrz : r = correctedChenZ N
  · exact hzdvd (hrz ▸ hrdvd)
  · exact (hpC.2.2.2 r hrprime (lt_of_le_of_ne hrlez hrz)) hrdvd

/-- For even `N`, the source carrier can fail the corrected carrier only at
`p = 2` or at the unit complement `N - p = 1`. -/
private theorem source_not_corrected_eq_two_or_sub_eq_one
    (N p : ℕ) (hNbig : 2 ^ 110 < N) (hEven : Even N)
    (hpSource : p ∈ jurkatRichertSourceCandidates N)
    (hpNotCorrected : p ∉ correctedChenCandidates N) :
    p = 2 ∨ N - p = 1 := by
  by_contra hbad
  push Not at hbad
  apply hpNotCorrected
  have hpS := Finset.mem_filter.mp hpSource
  have hpprime : p.Prime := hpS.2.1
  have hpN : p < N := by
    have hple : p ≤ N := by simpa using hpS.1
    by_contra hnot
    have hpEq : p = N := by omega
    have hN2 : N = 2 := (hpEq ▸ hpprime.even_iff).mp hEven
    omega
  have hn2 : 2 ≤ N - p := by
    have hnpos : 0 < N - p := by omega
    omega
  refine Finset.mem_filter.mpr ⟨by simpa using hpN, hpprime, hn2, ?_⟩
  intro r hrprime hrz hrdvd
  by_cases hrEq : r = 2
  · subst r
    have hpodd : Odd p := hpprime.odd_of_ne_two hbad.1
    have hnodd : Odd (N - p) := Nat.Even.sub_odd (by omega) hEven hpodd
    exact (Nat.not_even_iff_odd.mpr hnodd) ((even_iff_two_dvd.mpr hrdvd))
  · have hr2 : 2 < r := by
      have := hrprime.two_le
      omega
    have hrlefloor :
        (r : ℝ) ≤ (Nat.floor ((N : ℝ) ^ (1 / 10 : ℝ)) : ℝ) := by
      exact_mod_cast (by
        rw [correctedChenZ_eq_floor_of_large N hNbig] at hrz
        exact Nat.le_of_lt hrz)
    have hfloorle :
        (Nat.floor ((N : ℝ) ^ (1 / 10 : ℝ)) : ℝ) ≤
          (N : ℝ) ^ (1 / 10 : ℝ) :=
      Nat.floor_le (by positivity)
    exact (hpS.2.2 r hrprime hr2 (hrlefloor.trans hfloorle)) hrdvd

/-- The lower-floor fibre is bounded by the number of positive multiples of the
cutoff up to `N`. -/
private theorem correctedChen_cutoff_fibre_card_le_div
    (N : ℕ) :
    ((correctedChenCandidates N).filter
      (fun p => correctedChenZ N ∣ N - p)).card ≤ N / correctedChenZ N := by
  let B := (correctedChenCandidates N).filter
    (fun p => correctedChenZ N ∣ N - p)
  let T := (Finset.Ioc 0 N).filter (fun n => correctedChenZ N ∣ n)
  have hcard : B.card ≤ T.card := by
    apply Finset.card_le_card_of_injOn (fun p => N - p)
    · intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hpC := Finset.mem_filter.mp hp'.1
      have hpN : p < N := by simpa using hpC.1
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨Nat.sub_pos_of_lt hpN, Nat.sub_le N p⟩, hp'.2⟩
    · intro a ha b hb hab
      have ha' := Finset.mem_filter.mp ha
      have hb' := Finset.mem_filter.mp hb
      have haN : a < N := by
        simpa using (Finset.mem_filter.mp ha'.1).1
      have hbN : b < N := by
        simpa using (Finset.mem_filter.mp hb'.1).1
      have haadd := Nat.sub_add_cancel (Nat.le_of_lt haN)
      have hbadd := Nat.sub_add_cancel (Nat.le_of_lt hbN)
      change N - a = N - b at hab
      omega
  simpa [B, T, Nat.Ioc_filter_dvd_card_eq_div] using hcard

/-- In the source scale, the single lower-floor fibre has size at most
`2 * N^(9/10)`. -/
private theorem correctedChen_cutoff_fibre_card_le_rpow
    (N : ℕ) (hNbig : 2 ^ 110 < N) :
    (((correctedChenCandidates N).filter
      (fun p => correctedChenZ N ∣ N - p)).card : ℝ) ≤
        2 * (N : ℝ) ^ (9 / 10 : ℝ) := by
  let B := (correctedChenCandidates N).filter
    (fun p => correctedChenZ N ∣ N - p)
  have hcard := correctedChen_cutoff_fibre_card_le_div N
  have hmulNat : B.card * correctedChenZ N ≤ N := by
    calc
      B.card * correctedChenZ N ≤
          (N / correctedChenZ N) * correctedChenZ N :=
        Nat.mul_le_mul_right _ (by simpa [B] using hcard)
      _ ≤ N := Nat.div_mul_le_self N (correctedChenZ N)
  have hmulReal :
      (B.card : ℝ) * (correctedChenZ N : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hmulNat
  have hzlower :
      (N : ℝ) ^ (1 / 10 : ℝ) / 2 ≤ (correctedChenZ N : ℝ) :=
    chenZ_ge_root_half N hNbig
  have hsmall :
      (B.card : ℝ) * ((N : ℝ) ^ (1 / 10 : ℝ) / 2) ≤ (N : ℝ) :=
    (mul_le_mul_of_nonneg_left hzlower (Nat.cast_nonneg _)).trans hmulReal
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hmul :
      (B.card : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ) ≤ 2 * (N : ℝ) := by
    nlinarith
  have hprod :
      (N : ℝ) ^ (9 / 10 : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ) = (N : ℝ) := by
    rw [← Real.rpow_add hNpos]
    norm_num
  have hrhs :
      2 * (N : ℝ) ^ (9 / 10 : ℝ) =
        (2 * (N : ℝ)) / (N : ℝ) ^ (1 / 10 : ℝ) := by
    apply (eq_div_iff (Real.rpow_pos_of_pos hNpos _).ne').2
    rw [mul_assoc, hprod]
  rw [hrhs]
  exact (le_div_iff₀ (Real.rpow_pos_of_pos hNpos _)).2 (by simpa [B] using hmul)

/-- Explicit finite comparison between Chen's literal real-cutoff weight and
the corrected distinct-prime weight.  The only positive losses are the lower
floor fibre (at most `2 N^(9/10)` candidates, each costing at most four), and
the two exceptional source fibres `p = 2` and `N - p = 1`. -/
theorem jurkatRichertSourceWeightedCount_sub_boundary_le_distinct
    (N : ℕ) (hNbig : 2 ^ 110 < N) (hEven : Even N) :
    jurkatRichertSourceWeightedCount N -
        10 * (N : ℝ) ^ (9 / 10 : ℝ) ≤
      jurkatRichertDistinctWeightedCount N := by
  let S := jurkatRichertSourceCandidates N
  let C := correctedChenCandidates N
  let I := S ∩ C
  let ES := S \ I
  let EC := C \ I
  let mS := fun p => jurkatRichertSourceMediumPrimeCount N p
  let mC := fun p =>
    ((Finset.range (correctedChenY N)).filter
      (fun q => q.Prime ∧ correctedChenZ N ≤ q ∧ q ∣ N - p)).card
  let wS := fun p => (1 : ℝ) - (mS p : ℝ) / 2
  let wC := fun p => (1 : ℝ) - (mC p : ℝ) / 2
  have hsource :
      jurkatRichertSourceWeightedCount N = ∑ p ∈ S, wS p := by
    rfl
  have hdistinct :
      jurkatRichertDistinctWeightedCount N = ∑ p ∈ C, wC p := by
    unfold jurkatRichertDistinctWeightedCount correctedChenQ1Count
    dsimp [C, wC, mC]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.sum_div]
    ring
  have hI_S : I ⊆ S := by
    intro p hp
    exact (Finset.mem_inter.mp hp).1
  have hI_C : I ⊆ C := by
    intro p hp
    exact (Finset.mem_inter.mp hp).2
  have hsource_split :
      (∑ p ∈ ES, wS p) + ∑ p ∈ I, wS p = ∑ p ∈ S, wS p := by
    simpa [ES, I, Finset.sdiff_inter_self_left] using
      (Finset.sum_sdiff hI_S : (∑ p ∈ S \ I, wS p) + ∑ p ∈ I, wS p =
        ∑ p ∈ S, wS p)
  have hcorrected_split :
      (∑ p ∈ EC, wC p) + ∑ p ∈ I, wC p = ∑ p ∈ C, wC p := by
    simpa [EC] using
      (Finset.sum_sdiff hI_C : (∑ p ∈ C \ I, wC p) + ∑ p ∈ I, wC p =
        ∑ p ∈ C, wC p)
  have hcommon : ∑ p ∈ I, wS p ≤ ∑ p ∈ I, wC p := by
    apply Finset.sum_le_sum
    intro p hp
    have hp' := Finset.mem_inter.mp hp
    have hcount :=
      correctedChen_medium_prime_count_le_source N p hNbig hp'.1 hp'.2
    dsimp [wS, wC, mS, mC]
    exact sub_le_sub_left (div_le_div_of_nonneg_right
      (by exact_mod_cast hcount) (by norm_num)) 1
  have hESsub : ES ⊆ ({2, N - 1} : Finset ℕ) := by
    intro p hp
    have hp' : p ∈ S \ I := by simpa [ES] using hp
    have hpS : p ∈ S := (Finset.mem_sdiff.mp hp').1
    have hpNotC : p ∉ C := by
      intro hpC
      exact (Finset.mem_sdiff.mp hp').2 (Finset.mem_inter.mpr ⟨hpS, hpC⟩)
    have hex := source_not_corrected_eq_two_or_sub_eq_one N p hNbig hEven hpS hpNotC
    rcases hex with rfl | hunit
    · simp
    · have hpS' := Finset.mem_filter.mp hpS
      have hple : p ≤ N := by simpa [S] using hpS'.1
      have hpEq : p = N - 1 := by omega
      simp [hpEq]
  have hEScard : ES.card ≤ 2 :=
    (Finset.card_le_card hESsub).trans Finset.card_le_two
  have hESsum : ∑ p ∈ ES, wS p ≤ 2 := by
    calc
      (∑ p ∈ ES, wS p) ≤ ∑ _p ∈ ES, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        dsimp [wS, mS]
        have hnonneg : (0 : ℝ) ≤ jurkatRichertSourceMediumPrimeCount N p := by
          positivity
        linarith
      _ = (ES.card : ℝ) := by simp
      _ ≤ 2 := by exact_mod_cast hEScard
  have hECsub :
      EC ⊆ (C.filter (fun p => correctedChenZ N ∣ N - p)) := by
    intro p hp
    have hpC : p ∈ C := (Finset.mem_sdiff.mp hp).1
    have hpNotS : p ∉ S := by
      intro hpS
      exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_inter.mpr ⟨hpS, hpC⟩)
    exact Finset.mem_filter.mpr
      ⟨hpC, correctedChen_not_source_dvd_cutoff N p hNbig hpC hpNotS⟩
  have hECcard :
      (EC.card : ℝ) ≤ 2 * (N : ℝ) ^ (9 / 10 : ℝ) := by
    have hle := Finset.card_le_card hECsub
    have hboundary := correctedChen_cutoff_fibre_card_le_rpow N hNbig
    have hleR :
        (EC.card : ℝ) ≤
          ((C.filter (fun p => correctedChenZ N ∣ N - p)).card : ℝ) := by
      exact_mod_cast hle
    exact le_trans hleR (by simpa [C] using hboundary)
  have hECsum : -(4 : ℝ) * (EC.card : ℝ) ≤ ∑ p ∈ EC, wC p := by
    calc
      -(4 : ℝ) * (EC.card : ℝ) = ∑ _p ∈ EC, -(4 : ℝ) := by
        simp
        ring
      _ ≤ ∑ p ∈ EC, wC p := by
        apply Finset.sum_le_sum
        intro p hp
        have hpC : p ∈ correctedChenCandidates N := by
          simpa [EC, C] using (Finset.mem_sdiff.mp hp).1
        have hten := correctedChen_medium_prime_count_le_ten N p hNbig hpC
        dsimp [wC, mC]
        have hten' : (mC p : ℝ) ≤ 10 := by
          exact_mod_cast hten
        dsimp [mC] at hten'
        linarith
  have hpowone : (1 : ℝ) ≤ (N : ℝ) ^ (9 / 10 : ℝ) := by
    apply Real.one_le_rpow
    exact_mod_cast (show 1 ≤ N by omega)
    norm_num
  rw [hsource, hdistinct]
  rw [← hsource_split, ← hcorrected_split]
  nlinarith

/-- Source-faithful Chen/Jurkat--Richert lower-sieve input.  Chen 1973,
Lemma 9 (equations (25)--(27)), lower-bounds the finite weight

`#candidates - (1/2) * Σ_q #candidates_q`,

where the medium primes `q` are distinct.  Its analytic proof requires:

* the Mertens normalization `Γ_N(z) ~ 20 exp(-γ) 𝔖(N) / log N`;
* the lower sieve at level `N^(1/2-ε)` and the q-conditioned upper sieves at
  the varying levels `N^(1/2-ε)/q`;
* the integral estimate `J - K/4 ≥ -0.0164725`, whose final coefficient
  conversion is `jurkatRichert_mainCoefficient_ge_twoPoint6408`.

The real cutoff inequalities and the exceptional `p = 2`/unit fibres are kept
in this source object.  Valuation multiplicity and the ordered-triple penalty
are deliberately absent. -/
def ChenJurkatRichertDistinctWeightedLowerBound : Prop :=
  ∀ η : ℝ, 0 < η →
    ∀ᶠ N : ℕ in Filter.atTop, Even N →
      (2.6408 - η) * SingularSeries.liuSingularSeries N *
            (N : ℝ) / Real.log N ^ (2 : ℕ) ≤
        jurkatRichertSourceWeightedCount N

/-- The integral-free natural-number level corresponding exactly to
`d ≤ N^(1/2-ε)`. -/
noncomputable def jurkatRichertSourceLowerLevel (N : ℕ) (ε : ℝ) : ℕ :=
  Nat.floor ((N : ℝ) ^ (1 / 2 - ε)) + 1

/-- The explicit lower Rosser coefficient used for Chen's base sieve. -/
noncomputable def jurkatRichertBaseLowerRosserWeight
    (N : ℕ) (ε : ℝ) (d : ℕ) : ℝ :=
  LinearSieve.lowerRosserWeight (jurkatRichertSourceSiftingProduct N)
    (jurkatRichertSourceLowerLevel N ε) d

end MathlibNt.SieveTheory.SwitchingPrinciple
