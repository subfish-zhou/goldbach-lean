import MathlibNt.SieveTheory.LiLiuPrereqWFExternalFamily
import MathlibNt.SieveTheory.LiLiuPrereqWFProgressionAdapter

/-!
# Unmasked transport for the fixed external families

The full-modulus and reduced-progression sums use precisely externalTerm.
The quantitative hypotheses remain positive/injective or prime-shift ones;
arbitrary weighted convolution consumers are not asserted here.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open Finset ArithmeticFunction
open scoped Classical

noncomputable def externalFullRemainder {ι : Type*} (upper : Bool) (P : Finset ℕ)
    (D ε z : ℝ) (I : Finset ι) (a : ι → ℕ) (X : ℝ) (g : ArithmeticFunction ℝ) : ℝ :=
  ∑ t ∈ externalTags upper P D ε z, ∑ d ∈ Icc 1 ⌊D ^ (1 + ε + ε ^ 9)⌋₊,
    externalTerm upper P D ε z t d * sequenceRemainder I a X g d

noncomputable def externalFullTransportCost (upper : Bool) (P : Finset ℕ)
    (D ε z : ℝ) (N : ℕ) (X : ℝ) : ℝ :=
  if z ≤ Real.sqrt D then
    fullModulusTransportCost upper P D ε (geometricSieveLabel D ε) N X
  else if upper then
    fullModulusTransportCost true (externalEdgePrimes P D) D ε
      (geometricSieveLabel D ε) N X
  else 0

noncomputable def externalProgressionDiscrepancy (upper : Bool) (P : Finset ℕ)
    (D ε z : ℝ) (I : Finset ℕ) (a : ℕ) : ℝ :=
  ∑ t ∈ externalTags upper P D ε z,
    ∑ d ∈ (Icc 1 ⌊D ^ (1 + ε + ε ^ 9)⌋₊).filter (fun d => d.Coprime a),
      externalTerm upper P D ε z t d * primeProgressionDiscrepancy I a d

noncomputable def externalPrimeTransportCost (upper : Bool) (P : Finset ℕ)
    (D ε z : ℝ) (I : Finset ℕ) (N : ℕ) (X : ℝ) : ℝ :=
  if z ≤ Real.sqrt D then
    primeProgressionTransportCost upper P D ε (geometricSieveLabel D ε) I N X
  else if upper then
    primeProgressionTransportCost true (externalEdgePrimes P D) D ε
      (geometricSieveLabel D ε) I N X
  else 0

theorem externalFullRemainder_eq {ι : Type*} (upper : Bool) (P : Finset ℕ)
    (D ε z : ℝ) (I : Finset ι) (a : ι → ℕ) (X : ℝ) (g : ArithmeticFunction ℝ) :
    externalFullRemainder upper P D ε z I a X g =
      if z ≤ Real.sqrt D then
        fullSignedFamilyRemainder upper P D ε (geometricSieveLabel D ε) I a X g
      else if upper then fullSignedFamilyRemainder true (externalEdgePrimes P D) D ε
        (geometricSieveLabel D ε) I a X g else 0 := by
  unfold externalFullRemainder externalTags externalTerm
  split_ifs <;> first | rfl | simp

theorem externalProgressionDiscrepancy_eq (upper : Bool) (P : Finset ℕ)
    (D ε z : ℝ) (I : Finset ℕ) (a : ℕ) :
    externalProgressionDiscrepancy upper P D ε z I a =
      if z ≤ Real.sqrt D then
        familyProgressionDiscrepancy upper P D ε (geometricSieveLabel D ε) I a
      else if upper then familyProgressionDiscrepancy true (externalEdgePrimes P D) D ε
        (geometricSieveLabel D ε) I a else 0 := by
  unfold externalProgressionDiscrepancy externalTags externalTerm
  split_ifs <;> first | rfl | simp

theorem externalFamily_full_sequence_sieve {ι : Type*} (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {D ε z : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (hcut : ∀ p ∈ P, (p : ℝ) < z) (I : Finset ι) (a : ι → ℕ) (N : ℕ)
    (ha : ∀ i ∈ I, 0 < a i ∧ a i ≤ N) (hinj : Set.InjOn a (↑I : Set ι))
    (X : ℝ) {g : ArithmeticFunction ℝ} (hg : ∀ d, |g d| ≤ (d.totient : ℝ)⁻¹) :
    X * externalDensity false P D ε z g + externalFullRemainder false P D ε z I a X g -
        externalFullTransportCost false P D ε z N X ≤ sequenceSifted I a P ∧
      sequenceSifted I a P ≤ X * externalDensity true P D ε z g +
        externalFullRemainder true P D ε z I a X g +
          externalFullTransportCost true P D ε z N X := by
  rw [externalDensity_eq false P hP, externalDensity_eq true P hP,
    externalFullRemainder_eq, externalFullRemainder_eq]
  unfold externalFullTransportCost
  by_cases hz : z ≤ Real.sqrt D
  · simp only [hz, if_true]
    exact signedFamily_full_sequence_sieve P hP hD hε hεsmall
      (fun p hp => (hcut p (mem_sdiff.mp hp).1).trans_le hz) I a N ha hinj X hg
  · simp only [hz, if_false, Bool.false_eq_true, if_true, mul_zero, add_zero, sub_zero]
    refine ⟨sequenceSifted_nonneg I a P, ?_⟩
    have hB : externalEdgePrimes P D ⊆ P := filter_subset _ _
    exact (sequenceSifted_antitone I a hB).trans
      (signedFamily_full_sequence_sieve _ (fun p hp => hP p (hB hp)) hD hε hεsmall
        (fun p hp => (mem_filter.mp (mem_sdiff.mp hp).1).2) I a N ha hinj X hg).2

/-- This is the actual reduced residue discrepancy, not a maximal absolute
error and not a squarefree-masked weight. Both transport costs are retained. -/
theorem externalFamily_reduced_prime_sieve (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {D ε z : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (hcut : ∀ p ∈ P, (p : ℝ) < z) (I : Finset ℕ) (hIprime : ∀ p ∈ I, p.Prime)
    (N : ℕ) (hI : ∀ p ∈ I, p < N) (hPN : ∀ p ∈ P, p.Coprime N) (X : ℝ) :
    X * externalDensity false P D ε z (progressionDensity N) +
        externalProgressionDiscrepancy false P D ε z I N -
          externalPrimeTransportCost false P D ε z I N X ≤
      sequenceSifted I (fun p => N - p) P ∧
      sequenceSifted I (fun p => N - p) P ≤
        X * externalDensity true P D ε z (progressionDensity N) +
          externalProgressionDiscrepancy true P D ε z I N +
            externalPrimeTransportCost true P D ε z I N X := by
  rw [externalDensity_eq false P hP, externalDensity_eq true P hP,
    externalProgressionDiscrepancy_eq, externalProgressionDiscrepancy_eq]
  unfold externalPrimeTransportCost
  by_cases hz : z ≤ Real.sqrt D
  · simp only [hz, if_true]
    exact signedFamily_reduced_prime_sequence_sieve P hP hD hε hεsmall
      (fun p hp => (hcut p (mem_sdiff.mp hp).1).trans_le hz) I hIprime N hI hPN X
  · simp only [hz, if_false, Bool.false_eq_true, if_true, mul_zero, add_zero, sub_zero]
    refine ⟨sequenceSifted_nonneg I (fun p => N - p) P, ?_⟩
    have hB : externalEdgePrimes P D ⊆ P := filter_subset _ _
    exact (sequenceSifted_antitone I (fun p => N - p) hB).trans
      (signedFamily_reduced_prime_sequence_sieve _ (fun p hp => hP p (hB hp))
        hD hε hεsmall (fun p hp => (mem_filter.mp (mem_sdiff.mp hp).1).2)
        I hIprime N hI (fun p hp => hPN p (hB hp)) X).2

#check externalFamily_full_sequence_sieve
#print axioms externalFamily_full_sequence_sieve
#check externalFamily_reduced_prime_sieve
#print axioms externalFamily_reduced_prime_sieve

end MathlibNt.SieveTheory.LiLiuPrereqWF
