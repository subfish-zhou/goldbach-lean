import MathlibNt.SieveTheory.LiLiuPrereqWFInternalSieve
import MathlibNt.SieveTheory.LiLiuPrereqWFUnmaskedRemainder
import MathlibNt.SieveTheory.LiLiuPrereqWFExternalParameters

/-!
# Fixed piecewise families at the external edge

Above sqrt D the lower family is a singleton zero weight and the upper
family is the original family on primes below sqrt D. No coefficients are
masked. Both the density and the signed remainder below sum the actual
members over divisors of the ORIGINAL primorial.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open Finset ArithmeticFunction SmallRosser
open scoped Classical

noncomputable def externalEdgePrimes (P : Finset ℕ) (D : ℝ) : Finset ℕ :=
  P.filter (fun p => (p : ℝ) < Real.sqrt D)

noncomputable def externalTags (upper : Bool) (P : Finset ℕ) (D ε z : ℝ) :
    Finset (List ℕ) :=
  if z ≤ Real.sqrt D then signedTags upper P D ε (geometricSieveLabel D ε)
  else if upper then
    signedTags true (externalEdgePrimes P D) D ε (geometricSieveLabel D ε)
  else {[]}

noncomputable def externalTerm (upper : Bool) (P : Finset ℕ) (D ε z : ℝ)
    (t : List ℕ) : ArithmeticFunction ℝ :=
  if z ≤ Real.sqrt D then signedFamilyTerm upper P D ε t
  else if upper then signedFamilyTerm true (externalEdgePrimes P D) D ε t else 0

noncomputable def externalDensity (upper : Bool) (P : Finset ℕ) (D ε z : ℝ)
    (g : ArithmeticFunction ℝ) : ℝ :=
  ∑ t ∈ externalTags upper P D ε z, ∑ d ∈ (P.prod id).divisors,
    externalTerm upper P D ε z t d * g d

noncomputable def externalRemainder {ι : Type*} (upper : Bool) (P : Finset ℕ)
    (D ε z : ℝ) (I : Finset ι) (a : ι → ℕ) (X : ℝ) (g : ArithmeticFunction ℝ) : ℝ :=
  ∑ t ∈ externalTags upper P D ε z, ∑ d ∈ (P.prod id).divisors,
    externalTerm upper P D ε z t d * sequenceRemainder I a X g d

theorem sequenceSifted_nonneg {ι : Type*} (I : Finset ι) (a : ι → ℕ)
    (P : Finset ℕ) : 0 ≤ sequenceSifted I a P := by
  apply sum_nonneg
  intro i _
  split_ifs <;> norm_num

theorem sequenceSifted_antitone {ι : Type*} (I : Finset ι) (a : ι → ℕ)
    {B P : Finset ℕ} (hBP : B ⊆ P) :
    sequenceSifted I a P ≤ sequenceSifted I a B := by
  apply sum_le_sum
  intro i _
  have hdiv := prod_dvd_prod_of_subset B P id hBP
  by_cases h : (a i).Coprime (P.prod id)
  · simp only [if_pos h, if_pos (Nat.Coprime.of_dvd_right hdiv h), le_refl]
  · simp only [if_neg h]
    split_ifs <;> norm_num

/-- Enlarging only the summation carrier does not change these coefficients
on squarefree divisors; their non-squarefree extension remains untouched. -/
theorem signedFamilyTerm_sum_subcarrier (upper : Bool) {B P : Finset ℕ}
    (hBP : B ⊆ P) (hP : ∀ p ∈ P, p.Prime) (D ε : ℝ) (t : List ℕ) (r : ℕ → ℝ) :
    (∑ d ∈ (P.prod id).divisors, signedFamilyTerm upper B D ε t d * r d) =
      ∑ d ∈ (B.prod id).divisors, signedFamilyTerm upper B D ε t d * r d := by
  have hP0 : P.prod id ≠ 0 := prod_ne_zero_iff.mpr (fun p hp => (hP p hp).ne_zero)
  have hB0 : B.prod id ≠ 0 := prod_ne_zero_iff.mpr
    (fun p hp => (hP p (hBP hp)).ne_zero)
  have hdiv := prod_dvd_prod_of_subset B P id hBP
  symm
  apply sum_subset
  · intro d hd
    exact Nat.mem_divisors.mpr ⟨(Nat.dvd_of_mem_divisors hd).trans hdiv, hP0⟩
  · intro d hd hnot
    have hz : signedFamilyTerm upper B D ε t d = 0 := by
      by_contra hn
      have hsf : Squarefree d := fun x hx =>
        primeProduct_squarefree P hP x (hx.trans (Nat.dvd_of_mem_divisors hd))
      exact hnot (Nat.mem_divisors.mpr
        ⟨signedFamilyTerm_squarefree_dvd_primorial upper B D ε t hn hsf, hB0⟩)
    simp only [hz, zero_mul]

theorem signedFamilyDensity_eq_member_sum (upper : Bool) (P : Finset ℕ)
    (D ε : ℝ) (label : ℕ → ℕ) (g : ArithmeticFunction ℝ) :
    signedFamilyDensity upper P D ε label g =
      ∑ t ∈ signedTags upper P D ε label, ∑ d ∈ (P.prod id).divisors,
        signedFamilyTerm upper P D ε t d * g d := by
  rw [signedFamilyDensity, sum_comm]
  apply sum_congr rfl
  intro d _
  rw [signedFamilyAggregate_apply, sum_mul]

theorem externalDensity_eq (upper : Bool) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (D ε z : ℝ) (g : ArithmeticFunction ℝ) :
    externalDensity upper P D ε z g =
      if z ≤ Real.sqrt D then
        signedFamilyDensity upper P D ε (geometricSieveLabel D ε) g
      else if upper then signedFamilyDensity true (externalEdgePrimes P D) D ε
        (geometricSieveLabel D ε) g else 0 := by
  unfold externalDensity externalTags externalTerm
  split_ifs with hz hu
  · simp only [signedFamilyDensity_eq_member_sum]
  · rw [signedFamilyDensity_eq_member_sum]
    apply sum_congr rfl
    intro t _
    exact signedFamilyTerm_sum_subcarrier true (filter_subset _ _) hP D ε t g
  · simp

theorem externalRemainder_eq {ι : Type*} (upper : Bool) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (D ε z : ℝ) (I : Finset ι) (a : ι → ℕ)
    (X : ℝ) (g : ArithmeticFunction ℝ) :
    externalRemainder upper P D ε z I a X g =
      if z ≤ Real.sqrt D then
        signedFamilyRemainder upper P D ε (geometricSieveLabel D ε) I a X g
      else if upper then signedFamilyRemainder true (externalEdgePrimes P D) D ε
        (geometricSieveLabel D ε) I a X g else 0 := by
  unfold externalRemainder externalTags externalTerm
  split_ifs with hz hu
  · rfl
  · unfold signedFamilyRemainder
    apply sum_congr rfl
    intro t _
    exact signedFamilyTerm_sum_subcarrier true (filter_subset _ _) hP D ε t _
  · simp

theorem zero_wellFactorable {Q : ℝ} (hQ : 1 ≤ Q) :
    WellFactorable (0 : ArithmeticFunction ℝ) Q := by
  refine ⟨hQ, ?_, ?_, ?_⟩
  · simp [BoundedOne]
  · simp [SupportedAt]
  · intro A B _ _ _
    exact ⟨0, 0, by simp [BoundedOne], by simp [SupportedAt],
      by simp [BoundedOne], by simp [SupportedAt], by simp⟩

/-- These exact families, including the singleton zero lower edge, satisfy
the original source cardinality bound before all level splits. -/
theorem externalTags_card_and_wellFactorable (upper : Bool) (P : Finset ℕ)
    {D ε : ℝ} (z : ℝ) (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8) :
    ((externalTags upper P D ε z).card : ℝ) < Real.exp (8 * (ε⁻¹) ^ 3) ∧
      ∀ t ∈ externalTags upper P D ε z,
        WellFactorable (externalTerm upper P D ε z t) (D ^ (1 + ε + ε ^ 9)) := by
  unfold externalTags externalTerm
  split_ifs with hz hu
  · exact ⟨signedTags_card_lt_exp_source upper P _ hD hε hεsmall,
      signedTags_common_wellFactorable upper P _ hD hε hεsmall⟩
  · exact ⟨signedTags_card_lt_exp_source true _ _ hD hε hεsmall,
      signedTags_common_wellFactorable true _ _ hD hε hεsmall⟩
  · constructor
    · simp only [card_singleton, Nat.cast_one]
      exact Real.one_lt_exp_iff.mpr (by positivity)
    · intro t _
      apply zero_wellFactorable
      exact Real.one_le_rpow (by linarith) (by
        linarith [(external_dilation_bounds hε hεsmall).1])

/-- Finite sieve direction for the actual piecewise families. In the edge
range the upper inequality is sieve monotonicity and the lower is positivity.
Analytic F/f density is a separate obligation. -/
theorem externalFamily_sequence_sieve {ι : Type*} (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {D ε z : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (hcut : ∀ p ∈ P, (p : ℝ) < z) (I : Finset ι) (a : ι → ℕ)
    (X : ℝ) (g : ArithmeticFunction ℝ) :
    X * externalDensity false P D ε z g + externalRemainder false P D ε z I a X g ≤
        sequenceSifted I a P ∧
      sequenceSifted I a P ≤
        X * externalDensity true P D ε z g + externalRemainder true P D ε z I a X g := by
  rw [externalDensity_eq false P hP, externalDensity_eq true P hP,
    externalRemainder_eq false P hP, externalRemainder_eq true P hP]
  by_cases hz : z ≤ Real.sqrt D
  · simp only [hz, if_true]
    exact signedFamily_sequence_sieve P hP hD hε hεsmall
      (fun p hp => (hcut p (mem_sdiff.mp hp).1).trans_le hz) I a X g
  · simp only [hz, if_false, Bool.false_eq_true, if_true, mul_zero, add_zero]
    refine ⟨sequenceSifted_nonneg I a P, ?_⟩
    have hB : externalEdgePrimes P D ⊆ P := filter_subset _ _
    exact (sequenceSifted_antitone I a hB).trans
      (signedFamily_sequence_sieve _ (fun p hp => hP p (hB hp)) hD hε hεsmall
        (fun p hp => (mem_filter.mp (mem_sdiff.mp hp).1).2) I a X g).2

#check externalTags_card_and_wellFactorable
#print axioms externalTags_card_and_wellFactorable
#check externalFamily_sequence_sieve
#print axioms externalFamily_sequence_sieve
#check externalRemainder_eq
#print axioms externalRemainder_eq

end MathlibNt.SieveTheory.LiLiuPrereqWF
