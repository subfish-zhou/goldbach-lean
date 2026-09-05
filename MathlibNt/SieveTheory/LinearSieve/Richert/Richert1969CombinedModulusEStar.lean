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

/-- The `3^ω(d)`-weighted Richert `E*` mass on Chen's exact reduced pair
carrier, before reindexing by `m = q*d`. -/
noncomputable def chenReducedPairWeightedEStar
    (N : ℕ) (ε : ℝ) : ℝ :=
  ∑ q ∈ (jurkatRichertSourceMediumPrimes N).filter (fun q => ¬q ∣ N),
    ∑ d ∈ (jurkatRichertSourceSiftingProduct N).divisors.filter
        (fun d => d < jurkatRichertSourceUpperLevel N q ε),
      (3 : ℝ) ^ d.primeFactors.card * primeAPPrefixMaxError N (q * d)

/-- Exact normalization of the existing endpoint-error carrier against
Richert's prefix-maximal `E*`, retaining the explicit fixed shift at every
combined modulus. -/
theorem reducedWeightedBVSum_le_richertEStar_add_shift
    (N : ℕ) (ε : ℝ) (hN : 2 ≤ N) :
    jurkatRichertSourceReducedWeightedBVSum N ε ≤
      ∑ q ∈ (jurkatRichertSourceMediumPrimes N).filter (fun q => ¬q ∣ N),
        ∑ d ∈ (jurkatRichertSourceSiftingProduct N).divisors.filter
            (fun d => d < jurkatRichertSourceUpperLevel N q ε),
          (3 : ℝ) ^ d.primeFactors.card *
            (primeAPPrefixMaxError N (q * d) +
              richert418NormalizationShift (q * d)) := by
  unfold jurkatRichertSourceReducedWeightedBVSum
  apply Finset.sum_le_sum
  intro q hq
  apply Finset.sum_le_sum
  intro d hd
  have hqSource := (Finset.mem_filter.mp hq).1
  have hqN := (Finset.mem_filter.mp hq).2
  have hdDiv : d ∣ jurkatRichertSourceSiftingProduct N :=
    Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
  have hres :
      (AnalyticNumberTheory.Sieve.unitResidues (q * d)).Nonempty :=
    ⟨N % (q * d),
      jurkatRichertSource_mul_mod_mem_unitResidues hqSource hdDiv hqN⟩
  have hqPos := (Finset.mem_filter.mp hqSource).2.1.pos
  have hdPos := Nat.pos_of_dvd_of_pos hdDiv
    (Nat.pos_of_ne_zero (jurkatRichertSourceSiftingProduct_ne_zero N))
  exact mul_le_mul_of_nonneg_left
    (standardPrimeAPMaxError_le_richertEStar_add N (q * d)
      hN (Nat.mul_pos hqPos hdPos) hres)
    (pow_nonneg (by norm_num) _)

/-- The image of Chen's reduced `(q,d)` carrier under the combined-modulus
map from Richert (3.9)--(3.10). -/
noncomputable def chenReducedCombinedModuli
    (N : ℕ) (ε : ℝ) : Finset ℕ :=
  ((jurkatRichertSourceMediumPrimes N).filter fun q => ¬q ∣ N).biUnion
    fun q =>
      ((jurkatRichertSourceSiftingProduct N).divisors.filter
        fun d => d < jurkatRichertSourceUpperLevel N q ε).image
          fun d => q * d

private theorem chenReducedCombinedModulusFibres_pairwise
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

/-- Exact `(q,d) ↦ q*d` reindexing of Richert's ordinary `E*` mass.  Fibre
uniqueness is proved on Chen's literal source carrier, so no multiplicity is
discarded. -/
theorem sum_richertEStar_combined_eq_pairSum
    (N : ℕ) (ε : ℝ) :
    (∑ m ∈ chenReducedCombinedModuli N ε,
        primeAPPrefixMaxError N m) =
      ∑ q ∈ (jurkatRichertSourceMediumPrimes N).filter (fun q => ¬q ∣ N),
        ∑ d ∈ (jurkatRichertSourceSiftingProduct N).divisors.filter
            (fun d => d < jurkatRichertSourceUpperLevel N q ε),
          primeAPPrefixMaxError N (q * d) := by
  unfold chenReducedCombinedModuli
  rw [Finset.sum_biUnion
    (chenReducedCombinedModulusFibres_pairwise N ε)]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.sum_image]
  intro d₁ hd₁ d₂ hd₂ hmul
  have hqPrime := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
  exact Nat.mul_left_cancel hqPrime.pos hmul

/-- Reindexing also pays Richert's divisor weight: because `d ∣ q*d`,
`3^ω(d) ≤ 3^ω(q*d)`, and injectivity prevents any repeated combined modulus. -/
theorem chenReducedPairWeightedEStar_le_combinedMass
    (N : ℕ) (ε : ℝ) :
    chenReducedPairWeightedEStar N ε ≤
      threeOmegaErrorMass (chenReducedCombinedModuli N ε)
        (primeAPPrefixMaxError N) := by
  unfold chenReducedPairWeightedEStar threeOmegaErrorMass
  unfold chenReducedCombinedModuli
  rw [Finset.sum_biUnion
    (chenReducedCombinedModulusFibres_pairwise N ε)]
  apply Finset.sum_le_sum
  intro q hq
  rw [Finset.sum_image]
  · apply Finset.sum_le_sum
    intro d hd
    have hqPrime :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
    have hdDiv : d ∣ jurkatRichertSourceSiftingProduct N :=
      Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
    have hdPos := Nat.pos_of_dvd_of_pos hdDiv
      (Nat.pos_of_ne_zero (jurkatRichertSourceSiftingProduct_ne_zero N))
    have hsubset : d.primeFactors ⊆ (q * d).primeFactors := by
      rw [Nat.primeFactors_mul hqPrime.ne_zero hdPos.ne']
      exact Finset.subset_union_right
    have homega : d.primeFactors.card ≤ (q * d).primeFactors.card :=
      Finset.card_le_card hsubset
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) homega)
      (primeAPPrefixMaxError_nonneg N (q * d))
  · intro d₁ hd₁ d₂ hd₂ hmul
    have hqPrime :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
    exact Nat.mul_left_cancel hqPrime.pos hmul

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

/-- If the real Chen level lies below the integer (4.18) cutoff, ordinary
Bombieri pays the exact combined-modulus `E*` mass by finite subset
monotonicity. -/
theorem sum_richertEStar_combined_le_initialRange
    (N Q : ℕ) (ε : ℝ)
    (hcut : (N : ℝ) ^ (1 / 2 - ε) ≤ Q) :
    (∑ m ∈ chenReducedCombinedModuli N ε,
        primeAPPrefixMaxError N m) ≤
      ∑ m ∈ Finset.Icc 1 Q, primeAPPrefixMaxError N m := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm
    have hmPos : 0 < m := by
      rcases Finset.mem_biUnion.mp hm with ⟨q, hq, hm⟩
      rcases Finset.mem_image.mp hm with ⟨d, hd, rfl⟩
      have hqPos := (Finset.mem_filter.mp
        (Finset.mem_filter.mp hq).1).2.1.pos
      have hdDiv : d ∣ jurkatRichertSourceSiftingProduct N :=
        Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
      exact Nat.mul_pos hqPos (Nat.pos_of_dvd_of_pos hdDiv
        (Nat.pos_of_ne_zero (jurkatRichertSourceSiftingProduct_ne_zero N)))
    refine Finset.mem_Icc.mpr ⟨hmPos, ?_⟩
    exact_mod_cast (chenReducedCombinedModuli_cast_le hm).trans hcut
  · intro m hm hmNot
    exact primeAPPrefixMaxError_nonneg N m

/-- Richert's actual finite Cauchy/Lemma 3 payment on Chen's combined
moduli.  The only distribution premise is the ordinary unweighted (4.18)
mass on the initial modulus range. -/
theorem chenReducedPairWeightedEStar_sq_le_of_ordinary418
    (N Q : ℕ) (ε X B : ℝ)
    (hcut : (N : ℝ) ^ (1 / 2 - ε) ≤ Q)
    (hX : 0 ≤ X)
    (henvelope :
      ∀ m ∈ chenReducedCombinedModuli N ε,
        (m : ℝ) * primeAPPrefixMaxError N m ≤ X)
    (hOrdinary418 :
      (∑ m ∈ Finset.Icc 1 Q, primeAPPrefixMaxError N m) ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      chenReducedPairWeightedEStar N ε ^ 2 ≤
        (C * (Real.log (Q + 2)) ^ (9 : ℝ)) * (X * B) := by
  let S := chenReducedCombinedModuli N ε
  let E := primeAPPrefixMaxError N
  have hS : S ⊆ Finset.range (Q + 1) := by
    intro m hm
    have hmIcc : m ∈ Finset.Icc 1 Q := by
      have hmPos : 0 < m := by
        rcases Finset.mem_biUnion.mp hm with ⟨q, hq, hmImage⟩
        rcases Finset.mem_image.mp hmImage with ⟨d, hd, rfl⟩
        have hqPos :=
          (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1.pos
        have hdDiv : d ∣ jurkatRichertSourceSiftingProduct N :=
          Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
        exact Nat.mul_pos hqPos (Nat.pos_of_dvd_of_pos hdDiv
          (Nat.pos_of_ne_zero (jurkatRichertSourceSiftingProduct_ne_zero N)))
      exact Finset.mem_Icc.mpr
        ⟨hmPos, by
          have hreal : (m : ℝ) ≤ (Q : ℝ) :=
            (chenReducedCombinedModuli_cast_le hm).trans hcut
          exact_mod_cast hreal⟩
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Finset.mem_Icc.mp hmIcc).2)
  have hSquarefree : ∀ m ∈ S, Squarefree m := by
    intro m hm
    rcases Finset.mem_biUnion.mp hm with ⟨q, hq, hmImage⟩
    rcases Finset.mem_image.mp hmImage with ⟨d, hd, rfl⟩
    have hqSource := (Finset.mem_filter.mp hq).1
    have hqPrime := (Finset.mem_filter.mp hqSource).2.1
    have hdDiv : d ∣ jurkatRichertSourceSiftingProduct N :=
      Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
    have hdSquarefree :=
      (jurkatRichertSourceSiftingProduct_squarefree N).squarefree_of_dvd hdDiv
    have hcop :=
      jurkatRichertSourceMediumPrime_coprime_siftingDivisor hqSource hdDiv
    exact (Nat.squarefree_mul hcop).mpr ⟨hqPrime.squarefree, hdSquarefree⟩
  have hE : ∀ m ∈ S, 0 ≤ E m := by
    intro m hm
    exact primeAPPrefixMaxError_nonneg N m
  have hordinaryS : (∑ m ∈ S, E m) ≤ B :=
    (sum_richertEStar_combined_le_initialRange N Q ε hcut).trans
      hOrdinary418
  obtain ⟨C, hC, hmass⟩ :=
    threeOmegaError_sq_le_of_ordinaryBombieri_squarefree
      S Q E X B hS hSquarefree hE hX henvelope hordinaryS
  refine ⟨C, hC, ?_⟩
  have hpairNonneg : 0 ≤ chenReducedPairWeightedEStar N ε := by
    unfold chenReducedPairWeightedEStar
    apply Finset.sum_nonneg
    intro q hq
    apply Finset.sum_nonneg
    intro d hd
    exact mul_nonneg (pow_nonneg (by norm_num) _)
      (primeAPPrefixMaxError_nonneg N (q * d))
  have hcombinedNonneg : 0 ≤ threeOmegaErrorMass S E := by
    unfold threeOmegaErrorMass
    apply Finset.sum_nonneg
    intro m hm
    exact mul_nonneg (pow_nonneg (by norm_num) _)
      (primeAPPrefixMaxError_nonneg N m)
  have hsquare :
      chenReducedPairWeightedEStar N ε ^ 2 ≤
        threeOmegaErrorMass S E ^ 2 :=
    (sq_le_sq₀ hpairNonneg hcombinedNonneg).2
      (chenReducedPairWeightedEStar_le_combinedMass N ε)
  exact hsquare.trans hmass

end MathlibNt.SieveTheory.Richert1969
