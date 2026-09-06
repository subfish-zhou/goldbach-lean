

import MathlibNt.AnalyticNumberTheory.LargeSieve.PrimitiveCharacters

/-!
 # Reduced Farey indices for primitive-character Gauss expansions

This module supplies the finite, multiplicity-free frequency index needed after
expanding primitive Dirichlet characters by Gauss sums.  An index is an exact
pair `(q,a)` with `1 ≤ q ≤ Q`, `a < q`, and `Nat.Coprime a q`; its real
frequency is `a/q`.

The main output is structural rather than a Bombieri--Davenport conclusion:
the index-to-frequency map is injective, its image lies in the existing
`rationalPoints Q`, and additive large-sieve energy over the exact reduced
indices is bounded by `largeSieveBound`.  Thus later primitive-character
arguments may sum Gauss frequencies across moduli without introducing the
forbidden multiplicities from unreduced rational representatives.
-/

namespace AnalyticNumberTheory.LargeSieve

open scoped BigOperators
open Classical

noncomputable section

/-- Canonical reduced residues `0 ≤ a < q`. -/
def reducedResidues (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter fun a => Nat.Coprime a q

@[simp]
theorem mem_reducedResidues {q a : ℕ} :
    a ∈ reducedResidues q ↔ a < q ∧ Nat.Coprime a q := by
  simp [reducedResidues]

/-- A primitive-character Gauss term is supported exactly on canonical reduced
residues.  This is the pointwise transform that produces the Farey frequencies
indexed below; no non-unit residue survives. -/
theorem primitive_gaussSum_mulShift_eq_sum_reducedResidues {q : ℕ} [NeZero q]
    (χ : PrimitiveCharacter q) (n : ℤ) :
    gaussSum χ.1 ((primitiveGaussAddChar q).mulShift (n : ZMod q)) =
      ∑ a ∈ reducedResidues q,
        χ.1 (a : ZMod q) * charReal ((n : ℝ) * (a : ℝ) / (q : ℝ)) := by
  have hq : 0 < q := NeZero.pos q
  rw [gaussSum_primitiveGaussAddChar_mulShift]
  rw [sum_zmod_eq_sum_range]
  have hperiod : ∀ a ∈ Finset.range q,
      charReal ((((n : ZMod q).val : ℝ) * (((a : ZMod q).val : ℝ)) / (q : ℝ))) =
        charReal ((n : ℝ) * (a : ℝ) / (q : ℝ)) := by
    intro a ha
    have haval : (a : ZMod q).val = a := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ha)]
    rw [haval]
    exact (charReal_zmod_eq hq
      (m := n) (n := (n : ZMod q).val) (ZMod.natCast_zmod_val (n : ZMod q)).symm a).symm
  calc
    ∑ a ∈ Finset.range q,
        χ.1 (a : ZMod q) *
          charReal ((((n : ZMod q).val : ℝ) * (((a : ZMod q).val : ℝ)) / (q : ℝ))) =
        ∑ a ∈ Finset.range q,
          χ.1 (a : ZMod q) * charReal ((n : ℝ) * (a : ℝ) / (q : ℝ)) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [hperiod a ha]
    _ = ∑ a ∈ reducedResidues q,
          χ.1 (a : ZMod q) * charReal ((n : ℝ) * (a : ℝ) / (q : ℝ)) := by
            rw [reducedResidues, Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro a ha
            by_cases hcop : Nat.Coprime a q
            · simp [hcop]
            · have hnonunit : ¬ IsUnit (a : ZMod q) := by
                simpa [ZMod.isUnit_iff_coprime] using hcop
              simp [hcop, χ.1.map_nonunit hnonunit]

/-- Gauss shifting identifies the preceding reduced-residue sum with the
primitive character coefficient times its Gauss sum. -/
theorem sum_reducedResidues_eq_invChar_mul_gaussSum {q : ℕ} [NeZero q]
    (χ : PrimitiveCharacter q) (n : ℤ) :
    (∑ a ∈ reducedResidues q,
        χ.1 (a : ZMod q) * charReal ((n : ℝ) * (a : ℝ) / (q : ℝ))) =
      χ.1⁻¹ (n : ZMod q) * gaussSum χ.1 (primitiveGaussAddChar q) := by
  rw [← primitive_gaussSum_mulShift_eq_sum_reducedResidues χ n]
  exact gaussSum_mulShift_of_isPrimitive (primitiveGaussAddChar q) χ.2 (n : ZMod q)

/-- Exact finite cross-modulus index for reduced Farey/Gauss frequencies.
The first coordinate is the modulus and the second the canonical residue. -/
def reducedFareyIndices (Q : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 Q).product (Finset.range Q)).filter fun qa =>
    qa.2 < qa.1 ∧ Nat.Coprime qa.2 qa.1

@[simp]
theorem mem_reducedFareyIndices {Q q a : ℕ} :
    (q, a) ∈ reducedFareyIndices Q ↔
      1 ≤ q ∧ q ≤ Q ∧ a < q ∧ Nat.Coprime a q := by
  simp [reducedFareyIndices]
  omega

/-- The real additive frequency attached to a modulus-residue pair. -/
def reducedFareyPoint (qa : ℕ × ℕ) : ℝ :=
  (qa.2 : ℝ) / (qa.1 : ℝ)

@[simp]
theorem reducedFareyPoint_pair (q a : ℕ) :
    reducedFareyPoint (q, a) = (a : ℝ) / (q : ℝ) :=
  rfl

/-- Every exact reduced index gives one of the pre-existing rational points. -/
theorem reducedFareyPoint_mem_rationalPoints {Q : ℕ} {qa : ℕ × ℕ}
    (hqa : qa ∈ reducedFareyIndices Q) :
    reducedFareyPoint qa ∈ rationalPoints Q := by
  rcases qa with ⟨q, a⟩
  obtain ⟨hq, hqQ, haq, _⟩ := mem_reducedFareyIndices.mp hqa
  rw [reducedFareyPoint_pair]
  refine Finset.mem_biUnion.mpr ⟨q, Finset.mem_Icc.mpr ⟨hq, hqQ⟩, ?_⟩
  exact Finset.mem_image.mpr ⟨a, Finset.mem_range.mpr haq, rfl⟩

/-- Reduced canonical fractions have unique numerator and denominator.
This is the no-multiplicity fact missing from the unreduced `rationalPoints`
parameterization. -/
theorem reducedFareyPoint_injOn (Q : ℕ) :
    Set.InjOn reducedFareyPoint (reducedFareyIndices Q : Set (ℕ × ℕ)) := by
  rintro ⟨q₁, a₁⟩ h₁ ⟨q₂, a₂⟩ h₂ hpoint
  change (q₁, a₁) ∈ reducedFareyIndices Q at h₁
  change (q₂, a₂) ∈ reducedFareyIndices Q at h₂
  obtain ⟨hq₁, _, _, hcop₁⟩ := mem_reducedFareyIndices.mp h₁
  obtain ⟨hq₂, _, _, hcop₂⟩ := mem_reducedFareyIndices.mp h₂
  have hq₁0 : (q₁ : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq₁)
  have hq₂0 : (q₂ : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq₂)
  have hcrossR : (a₁ : ℝ) * (q₂ : ℝ) = (a₂ : ℝ) * (q₁ : ℝ) :=
    (div_eq_div_iff hq₁0 hq₂0).mp hpoint
  have hcross : a₁ * q₂ = a₂ * q₁ := by exact_mod_cast hcrossR
  -- Coprimality turns cross-multiplication into divisibility of both denominators.
  have hq₁dvdq₂ : q₁ ∣ q₂ := by
    apply hcop₁.symm.dvd_of_dvd_mul_left
    refine ⟨a₂, ?_⟩
    calc
      a₁ * q₂ = a₂ * q₁ := hcross
      _ = q₁ * a₂ := Nat.mul_comm _ _
  have hq₂dvdq₁ : q₂ ∣ q₁ := by
    apply hcop₂.symm.dvd_of_dvd_mul_left
    refine ⟨a₁, ?_⟩
    calc
      a₂ * q₁ = a₁ * q₂ := hcross.symm
      _ = q₂ * a₁ := Nat.mul_comm _ _
  have hq : q₁ = q₂ := Nat.dvd_antisymm hq₁dvdq₂ hq₂dvdq₁
  subst q₂
  have ha : a₁ = a₂ :=
    Nat.mul_right_cancel hq₁ hcross
  subst a₂
  rfl

/-- Multiplicity-free reduced Farey point set. -/
def reducedFareyPoints (Q : ℕ) : Finset ℝ :=
  (reducedFareyIndices Q).image reducedFareyPoint

/-- The reduced set is a subset of the existing rational point set. -/
theorem reducedFareyPoints_subset_rationalPoints (Q : ℕ) :
    reducedFareyPoints Q ⊆ rationalPoints Q := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨qa, hqa, rfl⟩
  exact reducedFareyPoint_mem_rationalPoints hqa

/-- Exact reindexing: because reduced fractions are unique, summing over the
finite `(q,a)` Gauss-frequency index is summing over its point set once. -/
theorem sum_reducedFareyPoints_eq_sum_indices {Q : ℕ} {β : Type*}
    [AddCommMonoid β] (f : ℝ → β) :
    (∑ x ∈ reducedFareyPoints Q, f x) =
      ∑ qa ∈ reducedFareyIndices Q, f (reducedFareyPoint qa) := by
  exact Finset.sum_image (reducedFareyPoint_injOn Q)

/-- The exact reduced Farey points retain the standard `1/Q²` spacing. -/
theorem reducedFareyPoints_wellSpaced (Q : ℕ) (hQ : 0 < Q) :
    wellSpacedReal (reducedFareyPoints Q) (1 / (Q : ℝ) ^ 2) := by
  intro x hx y hy hxy
  exact rationalPoints_wellSpaced Q hQ
    (reducedFareyPoints_subset_rationalPoints Q hx)
    (reducedFareyPoints_subset_rationalPoints Q hy) hxy

/-- Spacing-consumption bridge on the exact finite reduced indices.

This is ready for the Gauss-expanded primitive-character sum: each canonical
coprime `(q,a)` occurs exactly once across all `1 ≤ q ≤ Q`, and the right side
is the existing additive large-sieve bound. -/
theorem largeSieveReducedFareyIndices (M : ℤ) (N Q : ℕ) (hQ : 0 < Q)
    (b : ℤ → ℂ) :
    (∑ qa ∈ reducedFareyIndices Q,
        ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
          (charReal ((n : ℝ) * reducedFareyPoint qa) : ℂ) * b n‖ ^ 2)
      ≤ largeSieveBound N (1 / (Q : ℝ) ^ 2) *
          ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2 := by
  rw [← sum_reducedFareyPoints_eq_sum_indices (f := fun x =>
    ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
      (charReal ((n : ℝ) * x) : ℂ) * b n‖ ^ 2)]
  exact largeSievePrimal_wellSpaced M N (by positivity)
    (reducedFareyPoints Q) (reducedFareyPoints_wellSpaced Q hQ) b

end

end AnalyticNumberTheory.LargeSieve
