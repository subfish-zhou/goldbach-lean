import MathlibNt.SieveTheory.LiLiuPrereqWFSignedDensity

/-!
# Actual signed remainders for the common normalized family

The sequence keeps its indices, so equal integers retain their multiplicity.
All divisor sums are over the sieve primorial. The remainder is the actual
divisibility count minus the chosen main density, never an assumed error
certificate and never a sum of absolute values.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open Finset ArithmeticFunction
open scoped Classical

variable {ι : Type*}

noncomputable def sequenceDivisibility (I : Finset ι) (a : ι → ℕ) (d : ℕ) : ℝ :=
  ∑ i ∈ I, if d ∣ a i then 1 else 0

noncomputable def sequenceSifted (I : Finset ι) (a : ι → ℕ) (P : Finset ℕ) : ℝ :=
  ∑ i ∈ I, if (a i).Coprime (P.prod id) then 1 else 0

noncomputable def sequenceRemainder (I : Finset ι) (a : ι → ℕ) (X : ℝ)
    (g : ArithmeticFunction ℝ) (d : ℕ) : ℝ :=
  sequenceDivisibility I a d - X * g d

noncomputable def signedFamilyRemainder (upper : Bool) (P : Finset ℕ) (D ε : ℝ)
    (label : ℕ → ℕ) (I : Finset ι) (a : ι → ℕ) (X : ℝ)
    (g : ArithmeticFunction ℝ) : ℝ :=
  ∑ t ∈ signedTags upper P D ε label, ∑ d ∈ (P.prod id).divisors,
    signedFamilyTerm upper P D ε t d * sequenceRemainder I a X g d

theorem sum_gcd_divisors_eq_filtered {M : ℕ} (hM : M ≠ 0) (n : ℕ) (f : ℕ → ℝ) :
    (∑ d ∈ (n.gcd M).divisors, f d) =
      ∑ d ∈ M.divisors, if d ∣ n then f d else 0 := by
  have hg : n.gcd M ≠ 0 := by
    intro hz
    have hd := Nat.gcd_dvd_right n M
    rw [hz, zero_dvd_iff] at hd
    exact hM hd
  have hs : (n.gcd M).divisors = M.divisors.filter (fun d => d ∣ n) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    tauto
  rw [hs, Finset.sum_filter]

/-- Exact double-counting, valid also for zero sequence entries. -/
theorem sequence_divisor_sum (I : Finset ι) (a : ι → ℕ) {M : ℕ}
    (hM : M ≠ 0) (f : ℕ → ℝ) :
    (∑ i ∈ I, ∑ d ∈ ((a i).gcd M).divisors, f d) =
      ∑ d ∈ M.divisors, f d * sequenceDivisibility I a d := by
  simp only [sum_gcd_divisors_eq_filtered hM, sequenceDivisibility, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

/-- Main density plus the actual signed family remainder is exactly the
weighted divisibility count. This holds for arbitrary X and g. -/
theorem signedFamily_main_remainder_identity (upper : Bool) (P : Finset ℕ)
    (D ε : ℝ) (label : ℕ → ℕ) (I : Finset ι) (a : ι → ℕ) (X : ℝ)
    (g : ArithmeticFunction ℝ) :
    X * signedFamilyDensity upper P D ε label g +
        signedFamilyRemainder upper P D ε label I a X g =
      ∑ d ∈ (P.prod id).divisors,
        signedFamilyAggregate upper P D ε label d * sequenceDivisibility I a d := by
  have hr :
      signedFamilyRemainder upper P D ε label I a X g =
        ∑ d ∈ (P.prod id).divisors,
          signedFamilyAggregate upper P D ε label d * sequenceRemainder I a X g d := by
    rw [signedFamilyRemainder, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    rw [signedFamilyAggregate_apply, Finset.sum_mul]
  rw [hr, signedFamilyDensity, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  unfold sequenceRemainder
  ring

/-- A concrete common-WF family gives the true two-sided finite sieve bound
with its OWN density and its OWN signed remainder. No density estimate is
assumed. The short empty-profile weight is already included in the family. -/
theorem signedFamily_sequence_sieve (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {D ε : ℝ} (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (hcut : ∀ p ∈ P \ geometricSmallPrimes P D ε, (p : ℝ) < Real.sqrt D)
    (I : Finset ι) (a : ι → ℕ) (X : ℝ) (g : ArithmeticFunction ℝ) :
    let label := geometricSieveLabel D ε
    X * signedFamilyDensity false P D ε label g +
        signedFamilyRemainder false P D ε label I a X g ≤ sequenceSifted I a P ∧
      sequenceSifted I a P ≤ X * signedFamilyDensity true P D ε label g +
        signedFamilyRemainder true P D ε label I a X g := by
  dsimp only
  rw [signedFamily_main_remainder_identity, signedFamily_main_remainder_identity]
  have hM : P.prod id ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p hp => (hP p hp).ne_zero)
  rw [← sequence_divisor_sum I a hM, ← sequence_divisor_sum I a hM]
  exact ⟨Finset.sum_le_sum (fun i _ =>
    (signedFamilyAggregate_canonical_gcd_divisor_sum_bounds P hP hD hε hεsmall hcut (a i)).1),
    Finset.sum_le_sum (fun i _ =>
    (signedFamilyAggregate_canonical_gcd_divisor_sum_bounds P hP hD hε hεsmall hcut (a i)).2)⟩

#check sequence_divisor_sum
#check signedFamily_main_remainder_identity
#check signedFamily_sequence_sieve
#print axioms sequence_divisor_sum
#print axioms signedFamily_main_remainder_identity
#print axioms signedFamily_sequence_sieve

end MathlibNt.SieveTheory.LiLiuPrereqWF
