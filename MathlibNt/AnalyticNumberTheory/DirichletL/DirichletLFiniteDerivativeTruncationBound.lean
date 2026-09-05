import PrimeNumberTheoremAnd.ZetaBounds
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Finite Dirichlet-L derivative truncation bound

The finite derivative sum is bounded by majorizing every twisted summand.  In
particular, this does not compare the norm of a twisted sum with the norm of the
corresponding untwisted sum.
-/

open Complex Finset

namespace DirichletLFiniteDerivativeTruncationBound

variable {q : ℕ}

/-- The finite derivative truncation has the same elementary majorant as the
zeta truncation, uniformly in the Dirichlet character. -/
theorem norm_derivative_truncation_le (χ : DirichletCharacter ℂ q)
    {A C σ t : ℝ} (hA : A ∈ Set.Ioc 0 (1 / 2))
    (σ_ge : 1 - A / Real.log |t| ≤ σ) (t_gt : 3 < |t|) (hC : 2 ≤ C) :
    let N := ⌊|t|⌋₊
    ‖∑ n ∈ Finset.range (N + 1),
        (-(Complex.log n) * (n : ℂ) ^ (-(σ + t * I))) * χ n‖
      ≤ Real.exp A * C * (Real.log |t|) ^ 2 := by
  intro N
  obtain ⟨Npos, N_le_t, _, _, σPos, _⟩ := UpperBnd_aux hA t_gt σ_ge
  have logt_gt := logt_gt_one t_gt.le
  have logN_pos : 0 ≤ Real.log N := Real.log_nonneg (by norm_cast)
  have fact0 {n : ℕ} (hn : n ≤ N) : n ≤ |t| := by
    linarith [(by exact_mod_cast hn : (n : ℝ) ≤ N)]
  have fact1 {n : ℕ} (hn : n ≤ N) :
      ‖(n : ℂ) ^ (-(σ + t * I))‖ ≤ (n : ℝ)⁻¹ * A.exp :=
    ZetaBnd_aux2 hA.1 σPos (fact0 hn) σ_ge
  have fact2 {n : ℕ} (hn : n ≤ N) : Real.log n ≤ Real.log |t| := by
    cases n
    · simp only [CharP.cast_eq_zero, Real.log_zero]
      linarith
    · exact Real.log_le_log (by exact_mod_cast Nat.add_one_pos _) (fact0 hn)
  have fact3_base (n : ℕ) (hn : n ≤ N) :
      ‖-(Complex.log n) * (n : ℂ) ^ (-(σ + t * I))‖
        ≤ (n : ℝ)⁻¹ * Real.exp A * Real.log |t| := by
    rw [norm_mul, norm_neg, mul_comm]
    convert! mul_le_mul (fact1 hn) (fact2 hn) (Real.log_natCast_nonneg n) (by positivity)
    exact norm_complex_log_ofNat n
  have fact3 (n : ℕ) (hn : n ≤ N) :
      ‖(-(Complex.log n) * (n : ℂ) ^ (-(σ + t * I))) * χ n‖
        ≤ (n : ℝ)⁻¹ * Real.exp A * Real.log |t| := by
    calc
      ‖(-(Complex.log n) * (n : ℂ) ^ (-(σ + t * I))) * χ n‖ =
          ‖-(Complex.log n) * (n : ℂ) ^ (-(σ + t * I))‖ * ‖χ n‖ := norm_mul _ _
      _ ≤ ‖-(Complex.log n) * (n : ℂ) ^ (-(σ + t * I))‖ * 1 :=
        mul_le_mul_of_nonneg_left (χ.norm_le_one n) (norm_nonneg _)
      _ = ‖-(Complex.log n) * (n : ℂ) ^ (-(σ + t * I))‖ := mul_one _
      _ ≤ (n : ℝ)⁻¹ * Real.exp A * Real.log |t| := fact3_base n hn
  have hsum := norm_sum_le_of_le (Finset.range (N + 1))
    (by simp only [Finset.mem_range, Nat.lt_succ_iff]; exact fact3)
  rw [← Finset.sum_mul, ← Finset.sum_mul, mul_comm _ A.exp, mul_assoc] at hsum
  rw [mul_assoc]
  apply le_trans hsum <| (mul_le_mul_iff_right₀ A.exp_pos).mpr ?_
  rw [pow_two, ← mul_assoc, Finset.range_eq_Ico, ← Finset.Icc_eq_Ico,
    harmonic_eq_sum_Icc0]
  apply le_trans (mul_le_mul (h₁ := harmonic_le_one_add_log (n := N))
    (le_refl (Real.log |t|)) (by linarith) (by linarith))
  apply (mul_le_mul_iff_left₀ (by linarith)).mpr
  rw [(by ring : C * Real.log |t| =
      Real.log |t| + (C - 1) * Real.log |t|),
    ← one_mul <| Real.log (N : ℝ)]
  refine add_le_add logt_gt.le <|
    mul_le_mul (by linarith) ?_ (by positivity) (by linarith)
  exact Real.log_le_log (by positivity) N_le_t

end DirichletLFiniteDerivativeTruncationBound
