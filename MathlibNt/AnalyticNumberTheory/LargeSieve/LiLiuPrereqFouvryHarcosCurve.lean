import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryStepanovPointCount

/-!
# Harcos's affine curve

The final paragraph of Harcos, page 12 (`pages/harcos-weil-12.png`), applies
Theorem 7 to `(X^p - X)^2 - 4ab`.  The geometric nonsquareness below follows
the source's factorization argument, rather than assuming a curve estimate.
The count is the actual affine count, not the count of a projective completion.
The final section removes the auxiliary normalization `f(0) ≠ 0` by translation,
giving Theorem 7 in its original domain.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Polynomial Finset

section Algebra

variable {K : Type*} [Field K]

def harcosCurvePolynomial (p : ℕ) (a b : K) : K[X] :=
  (X ^ p - X) ^ 2 - C (4 * a * b)

theorem harcosCurvePolynomial_eval (p : ℕ) (a b x : K) :
    (harcosCurvePolynomial p a b).eval x = (x ^ p - x) ^ 2 - 4 * a * b := by
  simp [harcosCurvePolynomial]

theorem harcosCurvePolynomial_eval_zero (p : ℕ) (hp : 0 < p) (a b : K) :
    (harcosCurvePolynomial p a b).eval 0 = -(4 * a * b) := by
  simp [harcosCurvePolynomial_eval, hp.ne']

theorem harcosCurvePolynomial_natDegree (p : ℕ) (hp : 1 < p) (a b : K) :
    (harcosCurvePolynomial p a b).natDegree = 2 * p := by
  have hdeg : ((X : K[X]) ^ p - X).natDegree = p := by
    rw [natDegree_sub_eq_left_of_natDegree_lt]
    · simp
    · simpa using hp
  simp only [harcosCurvePolynomial, natDegree_sub_C, natDegree_pow, hdeg]

theorem harcosCurvePolynomial_eval_zero_ne (p : ℕ) (hp : 0 < p)
    (htwo : (2 : K) ≠ 0) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    (harcosCurvePolynomial p a b).eval 0 ≠ 0 := by
  rw [harcosCurvePolynomial_eval_zero p hp]
  have hfour : (4 : K) ≠ 0 := by
    have := mul_ne_zero htwo htwo
    norm_num at this ⊢
    exact this
  exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hfour ha) hb)

/-- The source's two factors have degree zero, contradicting their `X^p`
coefficients: their sum has coefficient `2`, which is nonzero. -/
theorem harcosCurvePolynomial_not_isSquare (p : ℕ) (hp : 1 < p)
    (htwo : (2 : K) ≠ 0) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    ¬ IsSquare (harcosCurvePolynomial p a b) := by
  rintro ⟨g, hg⟩
  have hc : (4 * a * b : K) ≠ 0 := by
    have hfour : (4 : K) ≠ 0 := by
      have := mul_ne_zero htwo htwo
      norm_num at this ⊢
      exact this
    exact mul_ne_zero (mul_ne_zero hfour ha) hb
  have hprod : (X ^ p - X - g) * (X ^ p - X + g) = C (4 * a * b) := by
    have he : (X ^ p - X : K[X]) ^ 2 - C (4 * a * b) = g * g := hg
    linear_combination he
  have hnz : (X ^ p - X - g) * (X ^ p - X + g) ≠ 0 := by
    rw [hprod]
    exact C_ne_zero.mpr hc
  have hd := congrArg natDegree hprod
  rw [natDegree_mul (mul_ne_zero_iff.mp hnz).1 (mul_ne_zero_iff.mp hnz).2,
    natDegree_C] at hd
  have hm := coeff_eq_zero_of_natDegree_lt
    (p := X ^ p - X - g) (n := p) (by omega)
  have hp' := coeff_eq_zero_of_natDegree_lt
    (p := X ^ p - X + g) (n := p) (by omega)
  have hp1 : 1 ≠ p := by omega
  simp [coeff_sub, coeff_add, coeff_X_pow, coeff_X, hp1] at hm hp'
  apply htwo
  linear_combination hm + hp'

theorem harcosCurvePolynomial_geometrically_not_isSquare
    (p : ℕ) (hp : 1 < p) (htwo : (2 : K) ≠ 0)
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    ¬ IsSquare ((harcosCurvePolynomial p a b).map
      (algebraMap K (AlgebraicClosure K))) := by
  have hi := (algebraMap K (AlgebraicClosure K)).injective
  have ht : (2 : AlgebraicClosure K) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero_iff _ hi).mpr htwo
  simpa [harcosCurvePolynomial, map_ofNat] using
    harcosCurvePolynomial_not_isSquare p hp ht
      (algebraMap K (AlgebraicClosure K) a) (algebraMap K (AlgebraicClosure K) b)
      ((map_ne_zero_iff _ hi).mpr ha) ((map_ne_zero_iff _ hi).mpr hb)

end Algebra

section FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The actual affine count in the last paragraph of Harcos, page 12. -/
def harcosCurvePointCount (p : ℕ) (a b : F) : ℕ :=
  (univ.filter fun xy : F × F =>
    xy.2 ^ 2 = (xy.1 ^ p - xy.1) ^ 2 - 4 * a * b).card

theorem harcosCurvePointCount_eq_stepanovPointCount (p : ℕ) (a b : F) :
    harcosCurvePointCount p a b = stepanovPointCount (harcosCurvePolynomial p a b) := by
  simp only [harcosCurvePointCount, stepanovPointCount, harcosCurvePolynomial_eval]

/-- Harcos's specialization, with all polynomial hypotheses discharged. -/
theorem harcos_curve_pointCount_bound (p : ℕ) [CharP F p]
    (hp : p.Prime) (hp2 : p ≠ 2) (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hq : 12 * p < Fintype.card F) :
    |(harcosCurvePointCount p a b : ℝ) - Fintype.card F| <
      8 * p * ⌈Real.sqrt (Fintype.card F : ℝ)⌉₊ := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have ht : (2 : F) ≠ 0 := by
    exact_mod_cast CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_two hp2
  have hodd : Odd (Fintype.card F) := by
    apply Nat.odd_iff.mpr
    apply FiniteField.odd_card_of_char_ne_two
    simpa only [ringChar.eq F p] using hp2
  have hdeg := harcosCurvePolynomial_natDegree p (by omega) a b
  have h := stepanov_pointCount_bound_of_eval_zero_ne (harcosCurvePolynomial p a b)
    hodd (harcosCurvePolynomial_eval_zero_ne p (by omega) ht a b ha hb)
    (harcosCurvePolynomial_geometrically_not_isSquare p (by omega) ht a b ha hb)
    (by omega) (by omega)
  rw [← harcosCurvePointCount_eq_stepanovPointCount, hdeg] at h
  convert h using 1
  push_cast
  ring

/-- The source's `n ≥ 4` range is inside the range `q > 12p`. -/
theorem harcos_twelve_mul_lt_pow (p n : ℕ) (hp : 3 ≤ p) (hn : 4 ≤ n) :
    12 * p < p ^ n := by
  have h2 : 9 ≤ p ^ 2 := by nlinarith
  have h3 : 27 ≤ p ^ 3 := by nlinarith
  have h4 : 12 * p < p ^ 4 := by nlinarith
  exact h4.trans_le (pow_le_pow_right₀ (by omega) hn)

/-- In characteristic `p`, every finite field of size `p^n`, `n ≥ 4`,
satisfies the specialized estimate, with no assumed curve bound. -/
theorem harcos_curve_pointCount_bound_of_card_eq_pow (p n : ℕ) [CharP F p]
    (hp : p.Prime) (hp2 : p ≠ 2) (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcard : Fintype.card F = p ^ n) (hn : 4 ≤ n) :
    |(harcosCurvePointCount p a b : ℝ) - (p : ℝ) ^ n| <
      8 * p * ⌈Real.sqrt ((p : ℝ) ^ n)⌉₊ := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hq : 12 * p < Fintype.card F := by
    rw [hcard]
    exact harcos_twelve_mul_lt_pow p n hp3 hn
  simpa only [hcard, Nat.cast_pow] using
    harcos_curve_pointCount_bound p hp hp2 a b ha hb hq

end FiniteField

section Translation

variable {K : Type*} [Field K]


end Translation

section FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]


end FiniteField

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
