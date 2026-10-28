import MathlibNt.SieveTheory.Switching.VaryingPrimeSieve
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.AnalyticNumberTheory.BombieriVinogradov.Bombieri1965Richert418
import MathlibNt.SieveTheory.LinearSieve.Richert.Richert1969BombieriWeightPayment

/-!
# Richert 1969: the combined-modulus E-star adapter

Frozen source:

* `references/richert-1969/richert-1969.pdf`, PDF pages 10 and 17--20,
  equations (3.9)--(3.10), (4.18), and the Cauchy argument after (4.22);
* `references/richert-1969/VISION_TRANSCRIPTION.md`, sections 5, 7, and 9.

The source first replaces `(q,d)` by the injective combined modulus `q*d`.
Ordinary Bombieri (4.18) controls Richert's prefix-maximal `E*` on that
carrier.  This file proves the exact finite reindexing and both directions of
the fixed logarithmic-integral normalization comparison.  It does not assume
the divisor-weighted Bombieri conclusion.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace MathlibNt.SieveTheory.Richert1969

open SwitchingPrinciple
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

/-- The fixed positive shift between the project's standard prime-AP center
and Richert's literal integral from `2` to `x`. -/
def richert418NormalizationShift (q : ℕ) : ℝ :=
  (2 / Real.log 2) / Nat.totient q

theorem richert418NormalizationShift_nonneg
    {q : ℕ} (hq : 0 < q) :
    0 ≤ richert418NormalizationShift q := by
  unfold richert418NormalizationShift
  exact div_nonneg (by positivity)
    (by exact_mod_cast (Nat.totient_pos.mpr hq).le)

/-- Reverse normalization comparison: the project's endpoint maximum is at
most Richert's residue maximum plus the explicit fixed shift. -/
theorem standardPrimeAPMaxError_le_richert_add
    (x q : ℕ) (hq : 0 < q)
    (hres : (AnalyticNumberTheory.Sieve.unitResidues q).Nonempty) :
    BombieriVinogradov.standardPrimeAPMaxError x q ≤
      primeAPResidueMaxError x q +
        richert418NormalizationShift q := by
  unfold BombieriVinogradov.standardPrimeAPMaxError
  dsimp only
  rw [dif_pos hres]
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨l, hl, rfl⟩
  have hshift := richert418NormalizationShift_nonneg hq
  have hrewrite :
      BombieriVinogradov.standardPrimeAPError x q l =
        primeAPError x q l - richert418NormalizationShift q := by
    rw [primeAPError_eq_standard_add]
    unfold richert418NormalizationShift
    ring
  rw [hrewrite]
  calc
    |primeAPError x q l - richert418NormalizationShift q| ≤
        |primeAPError x q l| +
          |richert418NormalizationShift q| := abs_sub _ _
    _ = |primeAPError x q l| +
          richert418NormalizationShift q := by rw [abs_of_nonneg hshift]
    _ ≤ primeAPResidueMaxError x q +
          richert418NormalizationShift q := by
      exact add_le_add (abs_primeAPError_le_residueMax hl) le_rfl

/-- Endpoint-to-prefix normalization on every positive combined modulus.
The hypothesis `2 ≤ N` is exactly the lower endpoint in Richert's `E*`. -/
theorem standardPrimeAPMaxError_le_richertEStar_add
    (N q : ℕ) (hN : 2 ≤ N) (hq : 0 < q)
    (hres : (AnalyticNumberTheory.Sieve.unitResidues q).Nonempty) :
    BombieriVinogradov.standardPrimeAPMaxError N q ≤
      primeAPPrefixMaxError N q +
        richert418NormalizationShift q := by
  exact (standardPrimeAPMaxError_le_richert_add N q hq hres).trans
    (add_le_add
      (primeAPResidueMaxError_le_prefixMax
        (Finset.mem_Icc.mpr ⟨hN, le_rfl⟩))
      le_rfl)


/-- The image of Chen's reduced `(q,d)` carrier under the combined-modulus
map from Richert (3.9)--(3.10). -/
noncomputable def chenReducedCombinedModuli
    (N : ℕ) (ε : ℝ) : Finset ℕ :=
  ((jurkatRichertSourceMediumPrimes N).filter fun q => ¬q ∣ N).biUnion
    fun q =>
      ((jurkatRichertSourceSiftingProduct N).divisors.filter
        fun d => d < jurkatRichertSourceUpperLevel N q ε).image
          fun d => q * d

/-- Distinct reduced medium primes have disjoint combined-modulus fibres. -/
theorem chenReducedCombinedModulusFibres_pairwise
    (N : ℕ) (ε : ℝ) :
    ∀ q₁ ∈ (jurkatRichertSourceMediumPrimes N).filter (fun q => ¬q ∣ N),
      ∀ q₂ ∈ (jurkatRichertSourceMediumPrimes N).filter (fun q => ¬q ∣ N),
        q₁ ≠ q₂ →
          Disjoint
            (((jurkatRichertSourceSiftingProduct N).divisors.filter
              fun d => d < jurkatRichertSourceUpperLevel N q₁ ε).image
                fun d => q₁ * d)
            (((jurkatRichertSourceSiftingProduct N).divisors.filter
              fun d => d < jurkatRichertSourceUpperLevel N q₂ ε).image
                fun d => q₂ * d) := by
  intro q₁ hq₁ q₂ hq₂ hqNe
  rw [Finset.disjoint_left]
  intro m hm₁ hm₂
  rcases Finset.mem_image.mp hm₁ with ⟨d₁, hd₁, rfl⟩
  rcases Finset.mem_image.mp hm₂ with ⟨d₂, hd₂, hmul⟩
  have hq₁' := (Finset.mem_filter.mp hq₁).1
  have hq₂' := (Finset.mem_filter.mp hq₂).1
  have hd₁' : d₁ ∣ jurkatRichertSourceSiftingProduct N :=
    Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd₁).1
  have hd₂' : d₂ ∣ jurkatRichertSourceSiftingProduct N :=
    Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd₂).1
  exact hqNe
    (jurkatRichertSource_mediumPrime_mul_siftingDivisor_injective
      hq₁' hq₂' hd₁' hd₂' hmul.symm).1


/-- Every combined modulus lies in the literal real cutoff
`q*d ≤ N^(1/2-ε)` supplied by the varying source level. -/
theorem chenReducedCombinedModuli_cast_le
    {N m : ℕ} {ε : ℝ}
    (hm : m ∈ chenReducedCombinedModuli N ε) :
    (m : ℝ) ≤ (N : ℝ) ^ (1 / 2 - ε) := by
  rcases Finset.mem_biUnion.mp hm with ⟨q, hq, hm⟩
  rcases Finset.mem_image.mp hm with ⟨d, hd, rfl⟩
  exact jurkatRichertSourceUpperLevel_mul_le
    (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hd).2


end MathlibNt.SieveTheory.Richert1969
