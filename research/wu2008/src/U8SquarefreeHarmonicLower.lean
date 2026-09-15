import U8TwoLogRectangle
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Harmonic.Bounds

/-! The second logarithm is supplied by squarefree reciprocal mass. The only
square-series estimate used here is the elementary finite bound by two. -/
noncomputable section
open Finset
open scoped BigOperators
namespace U8Literal.SmallProduct.TwoDimensional
open scoped Classical

theorem reciprocal_le_harmonicFactor {s : ℕ} (hs : Squarefree s) :
    (s : ℝ)⁻¹ ≤ harmonicFactor s := by
  rw [harmonicFactor, ArithmeticFunction.prodPrimeFactors_apply hs.ne_zero]
  have heq : (s : ℝ)⁻¹ = ∏ p ∈ s.primeFactors, (p : ℝ)⁻¹ := by
    rw [Finset.prod_inv_distrib, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hs]
  rw [heq]
  apply prod_le_prod
  · intro p _
    positivity
  · intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    simpa only [one_div] using
      (one_div_le_one_div_of_le (sub_pos.mpr hp1) (show (p : ℝ)-1 ≤ p by linarith))

theorem reciprocal_square_sum_le_two (T : ℕ) :
    (∑ k ∈ Icc 1 T, ((k : ℝ)^2)⁻¹) ≤ 2 := by
  have heq : Icc 1 T = Ioo 0 (T+1) := by ext k; simp; omega
  rw [heq]
  simpa using (sum_Ioo_inv_sq_le 0 (T+1) : (∑ k ∈ Ioo 0 (T+1), ((k : ℝ)^2)⁻¹) ≤ _)

theorem harmonic_le_twice_squarefree_reciprocal (T : ℕ) :
    (harmonic T : ℝ) ≤ 2 * ∑ s ∈ squarefreePrefix T, (s : ℝ)⁻¹ := by
  let S := squarefreePrefix T ×ˢ Icc 1 T
  let f : ℕ × ℕ → ℕ := fun a => a.2^2*a.1
  have hsub : Icc 1 T ⊆ S.image f := by
    intro n hn
    have hn' := mem_Icc.mp hn
    obtain ⟨s,k,hs,hk,heq,hsf⟩ := Nat.sq_mul_squarefree_of_pos hn'.1
    have hsle : s ≤ n := Nat.le_of_dvd hn'.1 ⟨k^2, by simpa [mul_comm] using heq.symm⟩
    have hkle : k ≤ n := Nat.le_of_dvd hn'.1 ⟨k*s, by simpa [pow_two, mul_assoc] using heq.symm⟩
    exact mem_image.mpr ⟨(s,k), mem_product.mpr
      ⟨mem_squarefreePrefix.mpr ⟨hs,hsle.trans hn'.2,hsf⟩,
        mem_Icc.mpr ⟨hk,hkle.trans hn'.2⟩⟩, heq⟩
  have hrec := reciprocal_square_sum_le_two T
  have hsum : 0 ≤ ∑ s ∈ squarefreePrefix T, (s : ℝ)⁻¹ :=
    sum_nonneg fun s _ => inv_nonneg.mpr (Nat.cast_nonneg s)
  calc
    (harmonic T : ℝ) = ∑ n ∈ Icc 1 T, (n : ℝ)⁻¹ := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ ∑ n ∈ S.image f, (n : ℝ)⁻¹ :=
      sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
    _ ≤ ∑ a ∈ S, ((f a : ℕ) : ℝ)⁻¹ :=
      sum_image_le_of_nonneg (fun n _ => by positivity)
    _ = (∑ s ∈ squarefreePrefix T, (s : ℝ)⁻¹) *
        (∑ k ∈ Icc 1 T, ((k : ℝ)^2)⁻¹) := by
      simp only [S, f, sum_product, Nat.cast_mul, Nat.cast_pow, mul_inv_rev,
        ← sum_mul, ← mul_sum]
    _ ≤ (∑ s ∈ squarefreePrefix T, (s : ℝ)⁻¹)*2 := mul_le_mul_of_nonneg_left hrec hsum
    _ = _ := mul_comm _ _

theorem log_le_twice_harmonicFactor_sum (T : ℕ) :
    Real.log T ≤ 2 * ∑ s ∈ squarefreePrefix T, harmonicFactor s := by
  have hl : Real.log (T : ℝ) ≤ (harmonic T : ℝ) := by
    simpa using log_le_harmonic_floor (T : ℝ) (Nat.cast_nonneg T)
  apply hl.trans ((harmonic_le_twice_squarefree_reciprocal T).trans _)
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact sum_le_sum fun s hs => reciprocal_le_harmonicFactor (mem_squarefreePrefix.mp hs).2.2

end U8Literal.SmallProduct.TwoDimensional
