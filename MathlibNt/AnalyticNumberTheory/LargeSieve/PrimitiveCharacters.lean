

import AnalyticNumberTheory.LargeSieve.Multiplicative
import AnalyticNumberTheory.LargeSieve.BombieriDavenport
import Mathlib.NumberTheory.DirichletCharacter.GaussSum

/-!
 # Primitive Dirichlet characters for the multiplicative large sieve

This module supplies the finite primitive-character and conductor interface
needed before a Bombieri--Davenport large sieve can be stated faithfully.
It deliberately does not state a sum over moduli: the pinned analytic-number-
theory dependency has only the single-modulus all-character estimate
`characterSieveModulus_le`.

The underlying Mathlib API already defines `DirichletCharacter.conductor`,
`DirichletCharacter.IsPrimitive`, `primitiveCharacter`, and `changeLevel`.
The definitions below package those heterogeneous conductor-level objects into
a finite subtype that can be used directly by `Finset` sums.  The module also
constructs the standard primitive additive character on `ZMod q`, bridges its
Gauss sums to the existing finite Fourier API, and proves both
`‖τ(χ)‖ ^ 2 = q` and `‖τ(χ)‖ = √q` for primitive complex characters.
-/

namespace AnalyticNumberTheory.LargeSieve

open scoped BigOperators
open Classical

noncomputable section

/-- Primitive complex Dirichlet characters of the fixed modulus `q`.

This is a subtype rather than a new character structure, so every existing
`DirichletCharacter` theorem applies to its coercion. -/
abbrev PrimitiveCharacter (q : ℕ) :=
  {χ : DirichletCharacter ℂ q // χ.IsPrimitive}

/-- The primitive characters of a fixed modulus form a finite type. -/
noncomputable instance (q : ℕ) : Fintype (PrimitiveCharacter q) :=
  Fintype.ofFinite _

/-- A positive modulus has at most its totient many primitive characters. -/
theorem primitiveCharacter_card_le_totient_basic (q : ℕ) (hq : 0 < q) :
    Fintype.card (PrimitiveCharacter q) ≤ q.totient := by
  let : NeZero q := ⟨hq.ne'⟩
  calc
    Fintype.card (PrimitiveCharacter q) ≤
        Fintype.card (DirichletCharacter ℂ q) := Fintype.card_subtype_le _
    _ = q.totient := by
      rw [← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q

/-- Primitive characters as a filtered finset of all characters modulo `q`.
This form is useful when applying an all-character estimate. -/
noncomputable def primitiveCharacters (q : ℕ) :
    Finset (DirichletCharacter ℂ q) :=
  Finset.univ.filter DirichletCharacter.IsPrimitive

@[simp]
theorem mem_primitiveCharacters {q : ℕ} {χ : DirichletCharacter ℂ q} :
    χ ∈ primitiveCharacters q ↔ χ.IsPrimitive := by
  simp [primitiveCharacters]

/-- A member of the primitive subtype has conductor exactly its modulus. -/
@[simp]
theorem primitive_conductor {q : ℕ} (χ : PrimitiveCharacter q) :
    χ.1.conductor = q :=
  χ.2

/-- The conductor-level primitive character associated to an arbitrary
Dirichlet character, packaged in the finite primitive subtype. -/
noncomputable def conductorPrimitiveCharacter {q : ℕ}
    (χ : DirichletCharacter ℂ q) : PrimitiveCharacter χ.conductor :=
  ⟨χ.primitiveCharacter, χ.primitiveCharacter_isPrimitive⟩

@[simp]
theorem conductorPrimitiveCharacter_val {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    (conductorPrimitiveCharacter χ).1 = χ.primitiveCharacter :=
  rfl

/-- Exact conductor decomposition: changing the conductor-level primitive
character back to the original modulus recovers the original character. -/
theorem changeLevel_conductorPrimitiveCharacter {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    DirichletCharacter.changeLevel χ.conductor_dvd_level
      (conductorPrimitiveCharacter χ).1 = χ :=
  χ.changeLevel_primitiveCharacter

/-- A sum over the primitive subtype is the corresponding filtered sum over all
characters. -/
theorem sum_primitive_eq_filter {q : ℕ} {β : Type*} [AddCommMonoid β]
    (f : DirichletCharacter ℂ q → β) :
    (∑ χ : PrimitiveCharacter q, f χ.1) =
      ∑ χ ∈ primitiveCharacters q, f χ := by
  exact (Finset.sum_subtype (primitiveCharacters q)
    (fun χ => mem_primitiveCharacters) f).symm

/-- Restricting a nonnegative all-character sum to primitive characters can
only decrease it. -/
theorem sum_primitive_le_sum_all {q : ℕ}
    (f : DirichletCharacter ℂ q → ℝ) (hf : ∀ χ, 0 ≤ f χ) :
    (∑ χ : PrimitiveCharacter q, f χ.1) ≤
      ∑ χ : DirichletCharacter ℂ q, f χ := by
  rw [sum_primitive_eq_filter]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun χ _ _ => hf χ)

/-- The first primitive-character multiplicative large-sieve foundation:
the pinned single-modulus all-character estimate restricts to the primitive
subtype. This is intentionally only pointwise in `q`; it is not the missing
Bombieri--Davenport sum over moduli. -/
theorem characterSievePrimitiveModulus_le {q : ℕ} [NeZero q]
    (a : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
            a n * χ.1 (n : ZMod q)‖ ^ 2
      ≤ ∑ r ∈ Finset.range q,
          ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
            (charReal ((n : ℝ) * (r : ℝ) / (q : ℝ)) : ℂ) * a n‖ ^ 2 := by
  refine le_trans (mul_le_mul_of_nonneg_left
    (sum_primitive_le_sum_all (fun χ =>
      ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
        a n * χ (n : ZMod q)‖ ^ 2) (fun _ => sq_nonneg _)) ?_)
    (characterSieveModulus_le a M N)
  exact div_nonneg (by positivity) (by positivity)

/-! ## Primitive Gauss sums -/

/-- The standard `q`-th root of unity used for the primitive additive character. -/
private def primitiveGaussRoot (q : ℕ) : ℂ := charReal (1 / (q : ℝ))

private lemma primitiveGaussRoot_isPrimitiveRoot (q : ℕ) (hq : q ≠ 0) :
    IsPrimitiveRoot (primitiveGaussRoot q) q := by
  have h := Complex.isPrimitiveRoot_exp_of_isCoprime (1 : ℤ) q hq isCoprime_one_left
  convert h using 1
  dsimp [primitiveGaussRoot, charReal]
  congr 1
  norm_num
  ring

private lemma primitiveGaussRoot_pow (q : ℕ) (hq : q ≠ 0) :
    primitiveGaussRoot q ^ q = 1 :=
  (primitiveGaussRoot_isPrimitiveRoot q hq).pow_eq_one

/-- The standard primitive additive character `x ↦ exp(2πix/q)` on `ZMod q`. -/
noncomputable def primitiveGaussAddChar (q : ℕ) [NeZero q] : AddChar (ZMod q) ℂ :=
  AddChar.zmodChar q (primitiveGaussRoot_pow q (NeZero.ne q))

@[simp]
theorem primitiveGaussAddChar_apply (q : ℕ) [NeZero q] (a : ZMod q) :
    primitiveGaussAddChar q a = charReal ((a.val : ℝ) / (q : ℝ)) := by
  rw [primitiveGaussAddChar, AddChar.zmodChar_apply, primitiveGaussRoot]
  rw [← charReal_nat_mul a.val (1 / (q : ℝ))]
  congr 1
  exact mul_one_div (a.val : ℝ) (q : ℝ)

/-- The standard additive character on `ZMod q` is primitive. -/
theorem primitiveGaussAddChar_isPrimitive (q : ℕ) [NeZero q] :
    (primitiveGaussAddChar q).IsPrimitive := by
  exact AddChar.zmodChar_primitive_of_primitive_root q
    (primitiveGaussRoot_isPrimitiveRoot q (NeZero.ne q))

private theorem charReal_eq_of_int_modEq {q : ℕ} (hq : 0 < q) {m n : ℤ}
    (hmn : m ≡ n [ZMOD (q : ℤ)]) :
    charReal ((m : ℝ) / (q : ℝ)) = charReal ((n : ℝ) / (q : ℝ)) := by
  exact charReal_periodic_zmod hq hmn

private theorem primitiveGaussAddChar_mulShift_apply (q : ℕ) [NeZero q]
    (n : ℤ) (x : ZMod q) :
    (primitiveGaussAddChar q).mulShift (n : ZMod q) x =
      charReal ((n : ℝ) * (x.val : ℝ) / (q : ℝ)) := by
  rw [AddChar.mulShift_apply, primitiveGaussAddChar_apply]
  have heq : ((n : ZMod q) * x : ZMod q) =
      ((n * (x.val : ℤ) : ℤ) : ZMod q) := by
    calc
      (n : ZMod q) * x = (n : ZMod q) * ((x.val : ℤ) : ZMod q) := by
        rw [Int.cast_natCast, ZMod.natCast_zmod_val]
      _ = ((n * (x.val : ℤ) : ℤ) : ZMod q) := by
        exact (Int.cast_mul (α := ZMod q) n (x.val : ℤ)).symm
  have hmod : (((n : ZMod q) * x).val : ℤ) ≡ n * (x.val : ℤ) [ZMOD (q : ℤ)] := by
    apply (ZMod.intCast_eq_intCast_iff _ _ q).1
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    exact heq
  have hmain := charReal_eq_of_int_modEq (NeZero.pos q) hmod
  convert hmain using 1 <;> norm_num [Int.cast_mul]

/-- Sums over `ZMod q` can be written using the canonical representatives `0 ≤ r < q`. -/
theorem sum_zmod_eq_sum_range {q : ℕ} [NeZero q] {M : Type*} [AddCommMonoid M]
    (f : ZMod q → M) :
    (∑ a : ZMod q, f a) = ∑ r ∈ Finset.range q, f (r : ZMod q) := by
  exact zmod_sum_range f

/-- Finite Fourier energy identity on `ZMod q`, specialized to the additive
character convention used by Gauss sums. -/
theorem zmod_fourier_energy {q : ℕ} [NeZero q] (z : ZMod q → ℂ) :
    (∑ a : ZMod q,
        ‖∑ x : ZMod q,
          charReal ((a.val : ℝ) * (x.val : ℝ) / (q : ℝ)) * z x‖ ^ 2) =
      (q : ℝ) * ∑ x : ZMod q, ‖z x‖ ^ 2 := by
  exact zmodParseval_zmod z

/-- The squared `L²` mass of a complex Dirichlet character is `φ(q)`. -/
theorem dirichletCharacter_sum_norm_sq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    (∑ a : ZMod q, ‖χ a‖ ^ 2) = (q.totient : ℝ) := by
  exact charNormSq_sum χ

/-- The Gauss sum against a shifted standard additive character is its explicit
finite Fourier sum. -/
theorem gaussSum_primitiveGaussAddChar_mulShift {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    gaussSum χ ((primitiveGaussAddChar q).mulShift a) =
      ∑ x : ZMod q,
        χ x * charReal ((a.val : ℝ) * (x.val : ℝ) / (q : ℝ)) := by
  unfold gaussSum
  apply Finset.sum_congr rfl
  intro x _
  have ha : ((a.val : ℤ) : ZMod q) = a := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [show (primitiveGaussAddChar q).mulShift a x =
      charReal ((a.val : ℝ) * (x.val : ℝ) / (q : ℝ)) by
    have h := primitiveGaussAddChar_mulShift_apply q (a.val : ℤ) x
    rw [ha] at h
    convert h using 1
    all_goals norm_num]

/-- Primitive complex Dirichlet characters have the classical Gauss-sum norm:
`|τ(χ)|² = q`. -/
theorem primitive_gaussSum_norm_sq {q : ℕ} [NeZero q]
    (χ : PrimitiveCharacter q) :
    ‖gaussSum χ.1 (primitiveGaussAddChar q)‖ ^ 2 = (q : ℝ) := by
  have hP := zmod_fourier_energy (z := fun x => χ.1 x)
  have hL :
      (∑ a : ZMod q,
          ‖gaussSum χ.1 ((primitiveGaussAddChar q).mulShift a)‖ ^ 2) =
        (q : ℝ) * ∑ x : ZMod q, ‖χ.1 x‖ ^ 2 := by
    rw [← hP]
    apply Finset.sum_congr rfl
    intro a _
    rw [gaussSum_primitiveGaussAddChar_mulShift]
    congr 2
    apply Finset.sum_congr rfl
    intro x _
    rw [mul_comm]
  have hR :
      (∑ a : ZMod q,
          ‖gaussSum χ.1 ((primitiveGaussAddChar q).mulShift a)‖ ^ 2) =
        ‖gaussSum χ.1 (primitiveGaussAddChar q)‖ ^ 2 * (q.totient : ℝ) := by
    calc
      _ = ∑ a : ZMod q,
          ‖χ.1⁻¹ a * gaussSum χ.1 (primitiveGaussAddChar q)‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro a _
            rw [gaussSum_mulShift_of_isPrimitive
              (e := primitiveGaussAddChar q) χ.2 a]
      _ = ∑ a : ZMod q,
          ‖χ.1⁻¹ a‖ ^ 2 * ‖gaussSum χ.1 (primitiveGaussAddChar q)‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro a _
            rw [norm_mul]
            ring
      _ = ‖gaussSum χ.1 (primitiveGaussAddChar q)‖ ^ 2 *
          (∑ a : ZMod q, ‖χ.1⁻¹ a‖ ^ 2) := by
            rw [← Finset.sum_mul]
            ring
      _ = _ := by rw [dirichletCharacter_sum_norm_sq]
  have hEq :
      ‖gaussSum χ.1 (primitiveGaussAddChar q)‖ ^ 2 * (q.totient : ℝ) =
        (q : ℝ) * (q.totient : ℝ) := by
    rw [← hR, hL, dirichletCharacter_sum_norm_sq]
  have hφ : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  exact mul_right_cancel₀ hφ hEq

/-- Norm form of the primitive Gauss-sum identity. -/
theorem primitive_gaussSum_norm {q : ℕ} [NeZero q]
    (χ : PrimitiveCharacter q) :
    ‖gaussSum χ.1 (primitiveGaussAddChar q)‖ = Real.sqrt q := by
  rw [← primitive_gaussSum_norm_sq χ, Real.sqrt_sq (norm_nonneg _)]



end

end AnalyticNumberTheory.LargeSieve
