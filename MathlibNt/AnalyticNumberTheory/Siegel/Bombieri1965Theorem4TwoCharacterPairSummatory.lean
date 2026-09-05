import MathlibNt.AnalyticNumberTheory.Siegel.Bombieri1965Theorem4TwoCharacterConvolution
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLWeakStripDerivative
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Sqrt

/-!
# Uniform cancellation in the genuine two-character pair

This modern argument uses the classical two-variable hyperbola decomposition
and complete character periods. It does not use primitivity, quadraticity, or
coprime conductors. The pair is the actual Dirichlet convolution, not a
nonnegative majorant. This is an unweighted summatory estimate, not yet a
weighted main-term formula for the fourfold convolution.
-/

open Complex Finset
open ArithmeticFunction hiding log
open scoped BigOperators

namespace DirichletCharacter

private lemma sum_Ioc_cutoff_eq_sum_ite {A : Type*} [AddCommMonoid A]
    (F : ℕ → A) {m N : ℕ} (hm : m ≤ N) :
    (∑ a ∈ Ioc 0 m, F a) = ∑ a ∈ Ioc 0 N, if a ≤ m then F a else 0 := by
  classical
  rw [← sum_filter]
  congr 1
  ext a
  simp only [mem_filter, mem_Ioc]
  omega

private lemma hyperbola_arm_eq_sum_ite (f g : ℕ → ℂ)
    {m N : ℕ} (hm : m ≤ N) :
    (∑ a ∈ Ioc 0 m, f a * ∑ b ∈ Ioc 0 (N / a), g b) =
      ∑ a ∈ Ioc 0 N, ∑ b ∈ Ioc 0 N,
        if a ≤ m ∧ a * b ≤ N then f a * g b else 0 := by
  rw [sum_Ioc_cutoff_eq_sum_ite _ hm]
  apply sum_congr rfl
  intro a ha
  have ha0 := (mem_Ioc.mp ha).1
  rw [sum_Ioc_cutoff_eq_sum_ite g (Nat.div_le_self N a)]
  by_cases ham : a ≤ m
  · simp only [ham, true_and, ↓reduceIte, mul_sum]
    apply sum_congr rfl
    intro b _
    have hdiv : b ≤ N / a ↔ a * b ≤ N := by
      rw [Nat.le_div_iff_mul_le ha0, Nat.mul_comm]
    by_cases hab : a * b ≤ N <;> simp [hdiv, hab]
  · simp [ham]

private lemma hyperbola_square_eq_sum_ite (f g : ℕ → ℂ)
    {m N : ℕ} (hm : m ≤ N) :
    (∑ a ∈ Ioc 0 m, f a) * (∑ b ∈ Ioc 0 m, g b) =
      ∑ a ∈ Ioc 0 N, ∑ b ∈ Ioc 0 N,
        if a ≤ m ∧ b ≤ m then f a * g b else 0 := by
  rw [sum_Ioc_cutoff_eq_sum_ite f hm, sum_Ioc_cutoff_eq_sum_ite g hm,
    sum_mul]
  apply sum_congr rfl
  intro a _
  rw [mul_sum]
  apply sum_congr rfl
  intro b _
  by_cases ha : a ≤ m <;> by_cases hb : b ≤ m <;> simp [ha, hb]

/-- Exact two-variable hyperbola identity at the integer square root. -/
theorem sum_Ioc_convolution_eq_sqrt_hyperbola
    (f g : ArithmeticFunction ℂ) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, (f * g) n) =
      (∑ a ∈ Ioc 0 N.sqrt, f a * ∑ b ∈ Ioc 0 (N / a), g b) +
      (∑ b ∈ Ioc 0 N.sqrt, g b * ∑ a ∈ Ioc 0 (N / b), f a) -
      (∑ a ∈ Ioc 0 N.sqrt, f a) * (∑ b ∈ Ioc 0 N.sqrt, g b) := by
  rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter, sum_filter, sum_product,
    hyperbola_arm_eq_sum_ite f g (Nat.sqrt_le_self N),
    hyperbola_arm_eq_sum_ite g f (Nat.sqrt_le_self N),
    hyperbola_square_eq_sum_ite f g (Nat.sqrt_le_self N)]
  rw [sum_comm (f := fun b a =>
    if b ≤ N.sqrt ∧ b * a ≤ N then g b * f a else 0)]
  rw [← sum_add_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro a _
  rw [← sum_add_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro b _
  have hsmall : a ≤ N.sqrt → b ≤ N.sqrt → a * b ≤ N := by
    intro ha hb
    exact (Nat.mul_le_mul ha hb).trans (Nat.sqrt_le N)
  have hlarge : ¬a ≤ N.sqrt → ¬b ≤ N.sqrt → ¬a * b ≤ N := by
    intro ha hb hab
    have h := Nat.mul_le_mul (by omega : N.sqrt.succ ≤ a)
      (by omega : N.sqrt.succ ≤ b)
    exact (Nat.not_le_of_gt (Nat.lt_succ_sqrt N)) (h.trans hab)
  by_cases ha : a ≤ N.sqrt <;> by_cases hb : b ≤ N.sqrt <;>
    by_cases hab : a * b ≤ N <;>
    simp [ha, hb, hab, mul_comm] <;> aesop

variable {q : ℕ}

/-- Character sums up to a natural endpoint are bounded both by their length
and, for a nonprincipal character, by the full modulus. -/
theorem norm_sum_Ioc_character_le_min [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Ioc 0 N, χ n‖ ≤ min (N : ℝ) q := by
  apply le_min
  · calc
      ‖∑ n ∈ Ioc 0 N, χ n‖ ≤ ∑ n ∈ Ioc 0 N, ‖χ n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Ioc 0 N, (1 : ℝ) :=
        sum_le_sum fun n _ => norm_le_one χ n
      _ = N := by simp
  · have hz : χ (0 : ZMod q) = 0 := by
      by_contra h
      have hq : q = 1 := by
        have hu : IsUnit (0 : ZMod q) := by
          by_contra hu
          exact h (MulChar.map_nonunit χ hu)
        have h01 : (0 : ZMod q) = 1 := hu.mul_left_cancel (by simp)
        exact ZMod.subsingleton_iff.mp ⟨fun a b => by
          calc a = a * 0 := by rw [h01, mul_one]
               _ = b * 0 := by simp
               _ = b := by rw [h01, mul_one]⟩
      subst q
      exact hχ (Subsingleton.elim _ _)
    have hsum : (∑ n ∈ Ioc 0 N, χ n) = ∑ n ∈ range (N + 1), χ n := by
      apply sum_subset
      · intro n hn
        simp only [mem_Ioc, mem_range] at hn ⊢
        omega
      · intro n hn hn'
        have hn0 : n = 0 := by
          simp only [mem_Ioc, mem_range] at hn hn'
          omega
        simpa [hn0] using hz
    rw [hsum]
    exact DirichletLWeakStripDerivative.norm_sum_range_character_le_modulus χ hχ (N + 1)

private lemma sum_Ioc_characterArithmeticFunction
    (χ : DirichletCharacter ℂ q) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, toArithmeticFunction (χ ·) n) =
      ∑ n ∈ Ioc 0 N, χ n :=
  sum_congr rfl fun _n hn =>
    (χ.apply_eq_toArithmeticFunction_apply (Nat.ne_of_gt (mem_Ioc.mp hn).1)).symm

private lemma norm_character_hyperbola_arm_le [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (N m : ℕ) :
    ‖∑ a ∈ Ioc 0 m, toArithmeticFunction (χ ·) a *
        ∑ b ∈ Ioc 0 (N / a), toArithmeticFunction (ψ ·) b‖ ≤ (m : ℝ) * q := by
  calc
    _ ≤ ∑ a ∈ Ioc 0 m, ‖toArithmeticFunction (χ ·) a *
        ∑ b ∈ Ioc 0 (N / a), toArithmeticFunction (ψ ·) b‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ Ioc 0 m, (q : ℝ) := by
      apply sum_le_sum
      intro a ha
      rw [norm_mul, sum_Ioc_characterArithmeticFunction,
        ← χ.apply_eq_toArithmeticFunction_apply (Nat.ne_of_gt (mem_Ioc.mp ha).1)]
      calc
        ‖χ a‖ * ‖∑ b ∈ Ioc 0 (N / a), ψ b‖ ≤ 1 * (q : ℝ) :=
          mul_le_mul (norm_le_one χ a)
            ((norm_sum_Ioc_character_le_min ψ hψ _).trans (min_le_right _ _))
            (norm_nonneg _) (by norm_num)
        _ = q := one_mul _
    _ = (m : ℝ) * q := by simp

/-- Uniform cancellation for two arbitrary nonprincipal characters at a common
nonzero modulus: the constant is `3`, even with the integer square root.
The overlap costs at most `q * sqrt N`, not `q²`, because one short sum is
bounded by its length. -/
theorem norm_sum_Ioc_character_pair_convolution_le_three_mul_nat_sqrt [NeZero q]
    (ψ η : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (hη : η ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Ioc 0 N,
      (toArithmeticFunction (ψ ·) * toArithmeticFunction (η ·)) n‖ ≤
      3 * (q : ℝ) * N.sqrt := by
  rw [sum_Ioc_convolution_eq_sqrt_hyperbola]
  have hoverlap :
      ‖(∑ a ∈ Ioc 0 N.sqrt, toArithmeticFunction (ψ ·) a) *
        (∑ b ∈ Ioc 0 N.sqrt, toArithmeticFunction (η ·) b)‖ ≤
        (N.sqrt : ℝ) * q := by
    rw [norm_mul, sum_Ioc_characterArithmeticFunction, sum_Ioc_characterArithmeticFunction]
    exact mul_le_mul
      ((norm_sum_Ioc_character_le_min ψ hψ _).trans (min_le_left _ _))
      ((norm_sum_Ioc_character_le_min η hη _).trans (min_le_right _ _))
      (norm_nonneg _) (by positivity)
  calc
    _ ≤ ‖∑ a ∈ Ioc 0 N.sqrt, toArithmeticFunction (ψ ·) a *
          ∑ b ∈ Ioc 0 (N / a), toArithmeticFunction (η ·) b‖ +
        ‖∑ b ∈ Ioc 0 N.sqrt, toArithmeticFunction (η ·) b *
          ∑ a ∈ Ioc 0 (N / b), toArithmeticFunction (ψ ·) a‖ +
        ‖(∑ a ∈ Ioc 0 N.sqrt, toArithmeticFunction (ψ ·) a) *
          (∑ b ∈ Ioc 0 N.sqrt, toArithmeticFunction (η ·) b)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (N.sqrt : ℝ) * q + (N.sqrt : ℝ) * q + (N.sqrt : ℝ) * q :=
      add_le_add
        (add_le_add (norm_character_hyperbola_arm_le ψ η hη _ _)
          (norm_character_hyperbola_arm_le η ψ hψ _ _)) hoverlap
    _ = 3 * (q : ℝ) * N.sqrt := by ring

/-- The standard real-square-root form of the genuine pair summatory bound. -/
theorem norm_sum_Icc_character_pair_convolution_le_three_mul_sqrt [NeZero q]
    (ψ η : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (hη : η ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N,
      (toArithmeticFunction (ψ ·) * toArithmeticFunction (η ·)) n‖ ≤
      3 * (q : ℝ) * Real.sqrt N := by
  have hI : Icc 1 N = Ioc 0 N := by
    ext n
    simp only [mem_Icc, mem_Ioc]
    omega
  rw [hI]
  refine (norm_sum_Ioc_character_pair_convolution_le_three_mul_nat_sqrt
    ψ η hψ hη N).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.le_sqrt_of_sq_le
  exact_mod_cast (show N.sqrt ^ 2 ≤ N by simpa only [pow_two] using Nat.sqrt_le N)

/-- The same bound at a real endpoint, including endpoints below `1`. -/
theorem norm_sum_Icc_floor_character_pair_convolution_le_three_mul_sqrt [NeZero q]
    (ψ η : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (hη : η ≠ 1)
    {X : ℝ} (hX : 0 ≤ X) :
    ‖∑ n ∈ Icc 1 ⌊X⌋₊,
      (toArithmeticFunction (ψ ·) * toArithmeticFunction (η ·)) n‖ ≤
      3 * (q : ℝ) * Real.sqrt X := by
  refine (norm_sum_Icc_character_pair_convolution_le_three_mul_sqrt
    ψ η hψ hη ⌊X⌋₊).trans ?_
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Nat.floor_le hX)) (by positivity)

/-- Cancellation for the actual pair `b = ψ * (χψ)` in the fourfold
convolution, written as its exact twist `ψ(n) (ζ * χ)(n)`. -/
theorem norm_sum_Icc_character_twist_zetaMul_le_three_mul_sqrt [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, ψ n * χ.zetaMul n‖ ≤
      3 * (q : ℝ) * Real.sqrt N := by
  simpa only [character_mul_product_apply] using
    norm_sum_Icc_character_pair_convolution_le_three_mul_sqrt ψ (χ * ψ) hψ hχψ N

/-- Real-endpoint form for the actual twisted pair. -/
theorem norm_sum_Icc_floor_character_twist_zetaMul_le_three_mul_sqrt [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1)
    {X : ℝ} (hX : 0 ≤ X) :
    ‖∑ n ∈ Icc 1 ⌊X⌋₊, ψ n * χ.zetaMul n‖ ≤
      3 * (q : ℝ) * Real.sqrt X := by
  simpa only [character_mul_product_apply] using
    norm_sum_Icc_floor_character_pair_convolution_le_three_mul_sqrt
      ψ (χ * ψ) hψ hχψ hX

end DirichletCharacter
