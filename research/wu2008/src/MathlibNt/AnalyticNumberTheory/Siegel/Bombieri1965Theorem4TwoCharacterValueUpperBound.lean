import MathlibNt.AnalyticNumberTheory.Siegel.Bombieri1965Theorem4TwoCharacterSingleAsymptotic
import MathlibNt.AnalyticNumberTheory.Siegel.Bombieri1965Theorem4TwoCharacterInduction
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLPrincipalEulerCorrectionLogBound

/-!
# Subpower upper bounds for the actual two-character residue

The target character's original L-value is retained. Its induction correction,
and the other two L-values at the common modulus, cost only logarithms.
No coprimality or primitivity is needed for these upper bounds.
-/

open Complex Finset

namespace DirichletCharacter

variable {q Q : ℕ}

/-- Harmonic truncation at the modulus gives a logarithmic bound even for
imprimitive nonprincipal characters. -/
theorem norm_LFunction_one_le_log_add_three [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ‖χ.LFunction 1‖ ≤ Real.log q + 3 := by
  have hsum : ‖∑ n ∈ Ioc 0 q, χ n / (n : ℂ)‖ ≤ 1 + Real.log q := by
    calc
      _ ≤ ∑ n ∈ Ioc 0 q, ‖χ n / (n : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Ioc 0 q, (n : ℝ)⁻¹ := by
        apply sum_le_sum
        intro n _
        rw [norm_div, Complex.norm_natCast, ← one_div]
        exact div_le_div_of_nonneg_right (norm_le_one χ n) (Nat.cast_nonneg n)
      _ = (harmonic q : ℝ) := by
        have hI : Ioc 0 q = Icc 1 q := by ext n; simp; omega
        rw [hI]
        simpa only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using
          congrArg (fun x : ℚ => (x : ℝ)) (harmonic_eq_sum_Icc (n := q)).symm
      _ ≤ 1 + Real.log q := by exact_mod_cast harmonic_le_one_add_log q
  have htail : ‖χ.LFunction 1 - ∑ n ∈ Ioc 0 q, χ n / (n : ℂ)‖ ≤ 2 :=
    (norm_LFunction_one_sub_sum_Ioc_div_le χ hχ q).trans
      ((div_le_iff₀ (by positivity)).mpr (by linarith))
  calc
    ‖χ.LFunction 1‖ ≤
        ‖χ.LFunction 1 - ∑ n ∈ Ioc 0 q, χ n / (n : ℂ)‖ +
          ‖∑ n ∈ Ioc 0 q, χ n / (n : ℂ)‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (χ.LFunction 1 - ∑ n ∈ Ioc 0 q, χ n / (n : ℂ))
        (∑ n ∈ Ioc 0 q, χ n / (n : ℂ))
    _ ≤ 2 + (1 + Real.log q) := add_le_add htail hsum
    _ = Real.log q + 3 := by ring

/-- Inducing any character to a nonzero common modulus has logarithmic
Euler loss at one, including overlapping levels. -/
theorem norm_inductionEulerProduct_one_le_one_add_log
    (χ : DirichletCharacter ℂ q) (Q : ℕ) [NeZero Q] :
    ‖inductionEulerProduct χ Q 1‖ ≤ 1 + Real.log Q := by
  have h := norm_inductionEulerProduct_le χ Q 1
  simp only [ofReal_one, Real.rpow_neg_one] at h
  exact h.trans (prod_one_add_inv_primeFactors_le_one_add_log Q
    (Nat.one_le_iff_ne_zero.mpr (NeZero.ne Q)))

/-- An explicit subpower majorant valid on the entire interval `[1, ∞)`. -/
theorem log_add_three_le_subpower {a x : ℝ} (ha : 0 < a) (hx : 1 ≤ x) :
    Real.log x + 3 ≤ (3 + 1 / a) * x ^ a := by
  have hp : 1 ≤ x ^ a := Real.one_le_rpow hx ha.le
  have hl := Real.log_le_rpow_div (by linarith : 0 ≤ x) ha
  calc
    Real.log x + 3 ≤ x ^ a / a + 3 * x ^ a := by linarith
    _ = (3 + 1 / a) * x ^ a := by ring

/-- Arbitrarily small positive powers bound all nonprincipal L-values
uniformly in the modulus. -/
theorem norm_LFunction_one_le_subpower [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {a : ℝ} (ha : 0 < a) :
    ‖χ.LFunction 1‖ ≤ (3 + 1 / a) * (q : ℝ) ^ a :=
  (norm_LFunction_one_le_log_add_three χ hχ).trans
    (log_add_three_le_subpower ha (by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)))

/-- The target's missing Euler factors also have arbitrarily small power cost. -/
theorem norm_inductionEulerProduct_one_le_subpower
    (χ : DirichletCharacter ℂ q) (Q : ℕ) [NeZero Q] {a : ℝ} (ha : 0 < a) :
    ‖inductionEulerProduct χ Q 1‖ ≤ (3 + 1 / a) * (Q : ℝ) ^ a := by
  have h := norm_inductionEulerProduct_one_le_one_add_log χ Q
  exact (h.trans (by linarith : 1 + Real.log Q ≤ Real.log Q + 3)).trans
    (log_add_three_le_subpower ha (by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne Q)))

/-- For a quadratic nonprincipal character its norm is its positive real value. -/
theorem norm_LFunction_one_eq_re_of_quadratic [NeZero q]
    {χ : DirichletCharacter ℂ q} (hquad : χ ^ 2 = 1) (hχ : χ ≠ 1) :
    ‖χ.LFunction 1‖ = (χ.LFunction 1).re := by
  have hr : χ.LFunction 1 = ((χ.LFunction 1).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using LFunction_apply_one_im_eq_zero_of_sq_eq_one hquad hχ
  calc
    _ = ‖((χ.LFunction 1).re : ℂ)‖ := congrArg norm hr
    _ = _ := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (LFunction_apply_one_re_pos_of_sq_eq_one hquad hχ)]

/-- Only the target's L-value is pulled back to its original modulus.
The correction remains explicit; the other two factors are bounded at `Q`. -/
theorem twoCharacterResidue_re_le_original_value_mul_subpower
    [NeZero q] [NeZero Q] (hq : q ∣ Q)
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ Q)
    (hχ : χ ≠ 1) (hquad : χ ^ 2 = 1) (hψ : ψ ≠ 1)
    (hprod : changeLevel hq χ * ψ ≠ 1) {a : ℝ} (ha : 0 < a) :
    (twoCharacterResidue (changeLevel hq χ) ψ).re ≤
      (χ.LFunction 1).re * ((3 + 1 / a) ^ 3 * (Q : ℝ) ^ (3 * a)) := by
  have hE := norm_inductionEulerProduct_one_le_subpower χ Q ha
  have hψB := norm_LFunction_one_le_subpower ψ hψ ha
  have hprodB := norm_LFunction_one_le_subpower (changeLevel hq χ * ψ) hprod ha
  have hχpos := LFunction_apply_one_re_pos_of_sq_eq_one hquad hχ
  calc
    _ ≤ ‖twoCharacterResidue (changeLevel hq χ) ψ‖ := re_le_norm _
    _ = (χ.LFunction 1).re * ‖inductionEulerProduct χ Q 1‖ *
        ‖ψ.LFunction 1‖ * ‖(changeLevel hq χ * ψ).LFunction 1‖ := by
      rw [twoCharacterResidue, LFunction_changeLevel hq χ (Or.inl hχ)]
      simp only [norm_mul, inductionEulerProduct,
        norm_LFunction_one_eq_re_of_quadratic hquad hχ]
    _ ≤ (χ.LFunction 1).re * ((3 + 1 / a) * (Q : ℝ) ^ a) *
        ((3 + 1 / a) * (Q : ℝ) ^ a) * ((3 + 1 / a) * (Q : ℝ) ^ a) := by
      gcongr
    _ = _ := by
      rw [mul_comm (3 : ℝ) a, Real.rpow_mul (Nat.cast_nonneg Q)]
      norm_num
      ring

end DirichletCharacter
