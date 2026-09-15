import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryStepanovParameters
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Stepanov's square-root point-count bound

The nonzero auxiliary polynomials and their proved Hasse multiplicities
give the one-sided counts in Harcos (13). The quadratic character then
converts these bounds into the affine point count in Theorem 7.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Polynomial Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def stepanovLocus (f : F[X]) (a : F) : Finset F :=
  Finset.univ.filter fun x => f.eval x = 0 ∨
    f.eval x ^ ((Fintype.card F - 1) / 2) = a

theorem stepanov_locus_card_lt (f : F[X]) (a : F)
    (hq : Odd (Fintype.card F)) (hf0 : f.eval 0 ≠ 0)
    (hf : ¬ IsSquare (f.map (algebraMap F (AlgebraicClosure F))))
    (hm : 3 ≤ f.natDegree) (hmq : 6 * f.natDegree < Fintype.card F) :
    ((stepanovLocus f a).card : ℝ) < (Fintype.card F : ℝ) / 2 +
      2 * f.natDegree * stepanovEll (Fintype.card F) := by
  classical
  obtain ⟨h, hnz, _, hdeg, hvan⟩ :=
    stepanov_exists_auxiliary_polynomial_of_large_card f a hq hf0 hf hm hmq
  have hroot := stepanov_card_mul_hasse_order_le h hnz (stepanovLocus f a)
    (stepanovEll (Fintype.card F)) (fun x hx => hvan x
      (by simpa only [stepanovLocus, mem_filter, mem_univ, true_and] using hx))
  have hell := (stepanov_integer_parameters (Fintype.card F) f.natDegree hm hmq).ell_pos
  have hrootR : ((stepanovLocus f a).card : ℝ) *
      (stepanovEll (Fintype.card F) : ℝ) ≤ h.natDegree := by exact_mod_cast hroot
  have hellR : (0 : ℝ) < stepanovEll (Fintype.card F) := by exact_mod_cast hell
  nlinarith

omit [DecidableEq F] in
private theorem stepanov_char_ne_two (hq : Odd (Fintype.card F)) : ringChar F ≠ 2 := by
  intro h
  have hc := FiniteField.even_card_of_char_two h
  obtain ⟨k, hk⟩ := hq
  omega

private theorem stepanov_quadraticChar_locus_bounds (f : F[X])
    (hq : Odd (Fintype.card F)) (x : F) :
    (quadraticChar F (f.eval x) : ℝ) ≤
        2 * (if x ∈ stepanovLocus f 1 then 1 else 0 : ℝ) - 1 ∧
      1 - 2 * (if x ∈ stepanovLocus f (-1) then 1 else 0 : ℝ) ≤
        (quadraticChar F (f.eval x) : ℝ) := by
  classical
  have he : Fintype.card F / 2 = (Fintype.card F - 1) / 2 := by
    obtain ⟨k, hk⟩ := hq
    omega
  have hp := quadraticChar_eq_pow_of_char_ne_two' (stepanov_char_ne_two hq) (f.eval x)
  rw [he] at hp
  by_cases hz : f.eval x = 0
  · simp [stepanovLocus, hz]
  rcases quadraticChar_dichotomy hz with h | h
  · have hx : x ∈ stepanovLocus f 1 := by
      simp only [stepanovLocus, mem_filter, mem_univ, true_and]
      right
      simpa [h] using hp.symm
    rw [h, if_pos hx]
    norm_num
    split_ifs <;> norm_num
  · have hx : x ∈ stepanovLocus f (-1) := by
      simp only [stepanovLocus, mem_filter, mem_univ, true_and]
      right
      simpa [h] using hp.symm
    rw [h, if_pos hx]
    norm_num
    split_ifs <;> norm_num

theorem stepanov_quadraticChar_sum_bound_of_eval_zero_ne (f : F[X])
    (hq : Odd (Fintype.card F)) (hf0 : f.eval 0 ≠ 0)
    (hf : ¬ IsSquare (f.map (algebraMap F (AlgebraicClosure F))))
    (hm : 3 ≤ f.natDegree) (hmq : 6 * f.natDegree < Fintype.card F) :
    |∑ x : F, (quadraticChar F (f.eval x) : ℝ)| <
      4 * f.natDegree * stepanovEll (Fintype.card F) := by
  classical
  have hp := stepanov_locus_card_lt f 1 hq hf0 hf hm hmq
  have hn := stepanov_locus_card_lt f (-1) hq hf0 hf hm hmq
  have hu := sum_le_sum (s := (univ : Finset F))
    (fun x _ => (stepanov_quadraticChar_locus_bounds f hq x).1)
  have hl := sum_le_sum (s := (univ : Finset F))
    (fun x _ => (stepanov_quadraticChar_locus_bounds f hq x).2)
  have hi (a : F) :
      (∑ x : F, (if x ∈ stepanovLocus f a then 1 else 0 : ℝ)) =
        (stepanovLocus f a).card := by simp
  simp only [sum_sub_distrib, ← mul_sum, hi, sum_const, card_univ, nsmul_eq_mul,
    mul_one] at hu hl
  rw [abs_lt]
  constructor <;> linarith

def stepanovPointCount (f : F[X]) : ℕ :=
  (Finset.univ.filter fun xy : F × F => xy.2 ^ 2 = f.eval xy.1).card

/-- The affine point count is exactly `q` plus the quadratic-character sum. -/
theorem stepanovPointCount_eq (f : F[X]) (hq : Odd (Fintype.card F)) :
    (stepanovPointCount f : ℝ) =
      Fintype.card F + ∑ x : F, (quadraticChar F (f.eval x) : ℝ) := by
  classical
  have hfiber (x : F) :
      ((univ.filter fun y : F => y ^ 2 = f.eval x).card : ℝ) =
        (quadraticChar F (f.eval x) : ℝ) + 1 := by
    have h := quadraticChar_card_sqrts (stepanov_char_ne_two hq) (f.eval x)
    simp only [Set.toFinset_ofPred] at h
    exact_mod_cast h
  have hsum : stepanovPointCount f =
      ∑ x : F, (univ.filter fun y : F => y ^ 2 = f.eval x).card := by
    simp only [stepanovPointCount, card_eq_sum_ones, sum_filter, Fintype.sum_prod_type]
  rw [hsum, Nat.cast_sum]
  simp only [hfiber, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one]
  ring

/-- Harcos Theorem 7 with the harmless normalization `f(0) ≠ 0` still explicit. -/
theorem stepanov_pointCount_bound_of_eval_zero_ne (f : F[X])
    (hq : Odd (Fintype.card F)) (hf0 : f.eval 0 ≠ 0)
    (hf : ¬ IsSquare (f.map (algebraMap F (AlgebraicClosure F))))
    (hm : 3 ≤ f.natDegree) (hmq : 6 * f.natDegree < Fintype.card F) :
    |(stepanovPointCount f : ℝ) - Fintype.card F| <
      4 * f.natDegree * ⌈Real.sqrt (Fintype.card F : ℝ)⌉₊ := by
  rw [stepanovPointCount_eq f hq, add_sub_cancel_left]
  exact stepanov_quadraticChar_sum_bound_of_eval_zero_ne f hq hf0 hf hm hmq

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
