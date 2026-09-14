

import MathlibNt.AnalyticNumberTheory.LargeSieve.ReducedFareyGauss

/-!
 # Weighted primitive-character Bombieri--Davenport inequality

This module combines primitive Gauss inversion with the multiplicity-free
reduced Farey additive large sieve.  The only loss relative to the classical
`N + Q²` constant is the explicit dyadic-shell logarithm already present in
`largeSieveBound`.
-/

namespace AnalyticNumberTheory.LargeSieve

open scoped BigOperators
open Classical

noncomputable section

/-- Character orthogonality for arbitrary coefficients on canonical reduced
residues.  This is the exact finite Bessel inequality needed after Gauss
inversion. -/
theorem character_reducedResidues_bessel {q : ℕ} [NeZero q] (c : ℕ → ℂ) :
    (∑ χ : PrimitiveCharacter q,
        ‖∑ a ∈ reducedResidues q, c a * χ.1 (a : ZMod q)‖ ^ 2) ≤
      (q.totient : ℝ) * ∑ a ∈ reducedResidues q, ‖c a‖ ^ 2 := by
  classical
  have hsum (χ : DirichletCharacter ℂ q) :
      (∑ x : ZMod q, c x.val * χ x) =
        ∑ a ∈ reducedResidues q, c a * χ (a : ZMod q) := by
    rw [sum_zmod_eq_sum_range, reducedResidues, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a ha
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ha)]
    by_cases hcop : Nat.Coprime a q
    · simp [hcop]
    · have hnonunit : ¬ IsUnit (a : ZMod q) := by
        simpa only [ZMod.isUnit_iff_coprime] using hcop
      simp [hcop, χ.map_nonunit hnonunit]
  have hparseval := charParseval_units (fun x : ZMod q => star (c x.val))
  simp_rw [← star_mul, ← star_sum, norm_star] at hparseval
  rw [unitsSum_eq_reducedFracs] at hparseval
  have henergy :
      (∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q),
        ‖c (a : ZMod q).val‖ ^ 2) =
      ∑ a ∈ reducedResidues q, ‖c a‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [ZMod.val_natCast,
      Nat.mod_eq_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)]
  simp_rw [hsum] at hparseval
  rw [henergy] at hparseval
  exact (sum_primitive_le_sum_all
    (fun χ => ‖∑ a ∈ reducedResidues q, c a * χ (a : ZMod q)‖ ^ 2)
    (fun _ => sq_nonneg _)).trans_eq hparseval

/-- Inversion by the primitive Gauss sum, with the inverse character chosen so
that the recovered interval coefficient is `χ(n)` rather than `χ⁻¹(n)`. -/
theorem primitive_interval_gauss_inversion {q : ℕ} [NeZero q]
    (χ : PrimitiveCharacter q) (b : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    gaussSum χ.1⁻¹ (primitiveGaussAddChar q) *
        (∑ n ∈ Finset.Icc (M + 1) (M + N), b n * χ.1 (n : ZMod q)) =
      ∑ a ∈ reducedResidues q, χ.1⁻¹ (a : ZMod q) *
        (∑ n ∈ Finset.Icc (M + 1) (M + N),
          (charReal ((n : ℝ) * (a : ℝ) / (q : ℝ)) : ℂ) * b n) := by
  let χi : PrimitiveCharacter q :=
    ⟨χ.1⁻¹, by change χ.1⁻¹.conductor = q; rw [DirichletCharacter.conductor_inv]; exact χ.2⟩
  calc
    gaussSum χ.1⁻¹ (primitiveGaussAddChar q) *
        (∑ n ∈ Finset.Icc (M + 1) (M + N), b n * χ.1 (n : ZMod q))
        = ∑ n ∈ Finset.Icc (M + 1) (M + N),
            b n * (χi.1⁻¹ (n : ZMod q) *
              gaussSum χi.1 (primitiveGaussAddChar q)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n hn
            simp [χi]
            ring
    _ = ∑ n ∈ Finset.Icc (M + 1) (M + N), b n *
          (∑ a ∈ reducedResidues q,
            χi.1 (a : ZMod q) *
              charReal ((n : ℝ) * (a : ℝ) / (q : ℝ))) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [sum_reducedResidues_eq_invChar_mul_gaussSum χi n]
    _ = ∑ n ∈ Finset.Icc (M + 1) (M + N),
          ∑ a ∈ reducedResidues q,
            b n * (χi.1 (a : ZMod q) *
              charReal ((n : ℝ) * (a : ℝ) / (q : ℝ))) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [Finset.mul_sum]
    _ = ∑ a ∈ reducedResidues q, χ.1⁻¹ (a : ZMod q) *
          (∑ n ∈ Finset.Icc (M + 1) (M + N),
            (charReal ((n : ℝ) * (a : ℝ) / (q : ℝ)) : ℂ) * b n) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro a ha
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n hn
            simp [χi]
            ring

/-- Inversion is an involution on primitive characters. -/
noncomputable def primitiveCharacterInvEquiv (q : ℕ) :
    PrimitiveCharacter q ≃ PrimitiveCharacter q where
  toFun χ := ⟨χ.1⁻¹, by change χ.1⁻¹.conductor = q; rw [DirichletCharacter.conductor_inv]; exact χ.2⟩
  invFun χ := ⟨χ.1⁻¹, by change χ.1⁻¹.conductor = q; rw [DirichletCharacter.conductor_inv]; exact χ.2⟩
  left_inv χ := by ext; simp
  right_inv χ := by ext; simp

/-- The exact single-modulus weighted primitive-character inequality after
Gauss inversion.  Its right side contains only canonical reduced additive
frequencies, with constant one. -/
theorem weighted_primitive_modulus_le_reduced {q : ℕ} [NeZero q]
    (b : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
            b n * χ.1 (n : ZMod q)‖ ^ 2 ≤
      ∑ a ∈ reducedResidues q,
        ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
          (charReal ((n : ℝ) * (a : ℝ) / (q : ℝ)) : ℂ) * b n‖ ^ 2 := by
  let A : ℕ → ℂ := fun a =>
    ∑ n ∈ Finset.Icc (M + 1) (M + N),
      (charReal ((n : ℝ) * (a : ℝ) / (q : ℝ)) : ℂ) * b n
  have hB := character_reducedResidues_bessel (q := q) A
  have hterm : ∀ χ : PrimitiveCharacter q,
      (q : ℝ) * ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
        b n * χ.1 (n : ZMod q)‖ ^ 2 =
      ‖∑ a ∈ reducedResidues q, A a * χ.1⁻¹ (a : ZMod q)‖ ^ 2 := by
    intro χ
    have hi := primitive_interval_gauss_inversion χ b M N
    have hn := primitive_gaussSum_norm_sq
      (⟨χ.1⁻¹, by change χ.1⁻¹.conductor = q; rw [DirichletCharacter.conductor_inv]; exact χ.2⟩ : PrimitiveCharacter q)
    have hiNorm := congrArg (fun z : ℂ => ‖z‖ ^ 2) hi
    simp only [norm_mul] at hiNorm
    calc
      (q : ℝ) * ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
          b n * χ.1 (n : ZMod q)‖ ^ 2 =
          ‖gaussSum χ.1⁻¹ (primitiveGaussAddChar q)‖ ^ 2 *
            ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
              b n * χ.1 (n : ZMod q)‖ ^ 2 := by rw [hn]
      _ = ‖∑ a ∈ reducedResidues q, χ.1⁻¹ (a : ZMod q) * A a‖ ^ 2 := by
        convert hiNorm using 1; ring
      _ = ‖∑ a ∈ reducedResidues q, A a * χ.1⁻¹ (a : ZMod q)‖ ^ 2 := by
        congr 2
        apply Finset.sum_congr rfl
        intro a ha
        ring
  have hsum :
      (q : ℝ) * ∑ χ : PrimitiveCharacter q,
          ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
            b n * χ.1 (n : ZMod q)‖ ^ 2 ≤
        (q.totient : ℝ) * ∑ a ∈ reducedResidues q, ‖A a‖ ^ 2 := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ χ : PrimitiveCharacter q,
          ‖∑ a ∈ reducedResidues q, A a * χ.1⁻¹ (a : ZMod q)‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro χ hχ
            exact hterm χ
      _ ≤ _ := by
        have hle :
            (∑ χ : PrimitiveCharacter q,
              ‖∑ a ∈ reducedResidues q, A a * χ.1⁻¹ (a : ZMod q)‖ ^ 2) =
              ∑ χ : PrimitiveCharacter q,
                ‖∑ a ∈ reducedResidues q, A a * χ.1 (a : ZMod q)‖ ^ 2 := by
          exact Fintype.sum_equiv
            (primitiveCharacterInvEquiv q) _ _ (fun χ => by rfl)
        rw [hle]
        exact hB
  have hφ : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  calc
    ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖∑ n ∈ Finset.Icc (M + 1) (M + N), b n * χ.1 (n : ZMod q)‖ ^ 2
        = ((q : ℝ) * ∑ χ : PrimitiveCharacter q,
          ‖∑ n ∈ Finset.Icc (M + 1) (M + N), b n * χ.1 (n : ZMod q)‖ ^ 2) /
            (q.totient : ℝ) := by ring
    _ ≤ ((q.totient : ℝ) * ∑ a ∈ reducedResidues q, ‖A a‖ ^ 2) /
          (q.totient : ℝ) := (div_le_div_iff_of_pos_right hφ).mpr hsum
    _ = ∑ a ∈ reducedResidues q, ‖A a‖ ^ 2 := by field_simp
    _ = _ := rfl

/-- Reindex canonical reduced residues for `1 ≤ q ≤ Q` by reduced Farey
indices, preserving the modulus range and coprimality condition. -/
theorem sum_reducedResidues_eq_sum_reducedFareyIndices
    {β : Type*} [AddCommMonoid β] (Q : ℕ) (f : ℕ × ℕ → β) :
    (∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ reducedResidues q, f (q, a)) =
      ∑ qa ∈ reducedFareyIndices Q, f qa := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij (fun x _ => (x.1, x.2)) ?_ ?_ ?_ ?_
  · intro x hx
    rcases x with ⟨q, a⟩
    simp only [Finset.mem_sigma] at hx
    rw [mem_reducedFareyIndices]
    rcases Finset.mem_Icc.mp hx.1 with ⟨hq1, hqQ⟩
    rcases mem_reducedResidues.mp hx.2 with ⟨haq, hcop⟩
    exact ⟨hq1, hqQ, haq, hcop⟩
  · intro x hx y hy hxy
    rcases x with ⟨q, a⟩
    rcases y with ⟨r, b⟩
    cases hxy
    rfl
  · intro qa hqa
    rcases qa with ⟨q, a⟩
    rw [mem_reducedFareyIndices] at hqa
    refine ⟨⟨q, a⟩, ?_, rfl⟩
    simp only [Finset.mem_sigma]
    exact ⟨Finset.mem_Icc.mpr ⟨hqa.1, hqa.2.1⟩,
      mem_reducedResidues.mpr ⟨hqa.2.2.1, hqa.2.2.2⟩⟩
  · intro x hx
    rfl

/-- Concrete reindexing of the interval additive energy. -/
theorem interval_additive_energy_reindex (b : ℤ → ℂ) (M : ℤ) (N Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ reducedResidues q,
      ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
        (charReal ((n : ℝ) * (a : ℝ) / (q : ℝ)) : ℂ) * b n‖ ^ 2) =
      ∑ qa ∈ reducedFareyIndices Q,
        ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
          (charReal ((n : ℝ) * reducedFareyPoint qa) : ℂ) * b n‖ ^ 2 := by
  simpa only [reducedFareyPoint, mul_div_assoc] using
    sum_reducedResidues_eq_sum_reducedFareyIndices Q (fun qa =>
      ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
        (charReal ((n : ℝ) * (qa.2 : ℝ) / (qa.1 : ℝ)) : ℂ) * b n‖ ^ 2)

/-- Weighted primitive-character Bombieri--Davenport inequality across all
`1 ≤ q ≤ Q`, with interval coefficients and the exact additive-stack constant. -/
theorem weighted_primitive_bombieri_davenport (b : ℤ → ℂ) (M : ℤ)
    (N Q : ℕ) (hQ : 0 < Q) :
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
            b n * χ.1 (n : ZMod q)‖ ^ 2) ≤
      largeSieveBound N (1 / (Q : ℝ) ^ 2) *
        ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2 := by
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ reducedResidues q,
        ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
          (charReal ((n : ℝ) * (a : ℝ) / (q : ℝ)) : ℂ) * b n‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro q hq
      let : NeZero q := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
      exact weighted_primitive_modulus_le_reduced b M N
    _ = ∑ qa ∈ reducedFareyIndices Q,
        ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
          (charReal ((n : ℝ) * reducedFareyPoint qa) : ℂ) * b n‖ ^ 2 := by
      exact interval_additive_energy_reindex b M N Q
    _ ≤ _ := largeSieveReducedFareyIndices M N Q hQ b

/-- Fully expanded constant.  This records the unique current scale loss:
`N + (2⌈log₂(Q²)⌉+12)Q²`, inherited solely from the additive Schur/dyadic stack. -/
theorem weighted_primitive_bombieri_davenport_explicit (b : ℤ → ℂ) (M : ℤ)
    (N Q : ℕ) (hQ : 0 < Q) :
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
            b n * χ.1 (n : ZMod q)‖ ^ 2) ≤
      ((N : ℝ) +
        (2 * (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) + 12) *
          (Q : ℝ) ^ 2) *
        ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2 := by
  have h := weighted_primitive_bombieri_davenport b M N Q hQ
  have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hOneDiv : 1 / (1 / (Q : ℝ) ^ 2) = (Q : ℝ) ^ 2 := by
    field_simp [hQr]
  have hDivide (x : ℝ) : x / (1 / (Q : ℝ) ^ 2) = x * (Q : ℝ) ^ 2 := by
    field_simp [hQr]
  convert h using 1
  dsimp [largeSieveBound]
  rw [hOneDiv, hDivide]
