import MathlibNt.Wu2008DoubleSieve.SecondFunctionalContinuousCube

namespace Wu2008DoubleSieve
open Set MeasureTheory
open scoped BigOperators

/-- Literal closed Lebesgue rectangle. -/
def continuousRectangle {n : ℕ} (A B : Fin n → ℝ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun i => Icc (A i) (B i))

theorem continuousRectangle_integrable {n : ℕ} (A B : Fin n → ℝ)
    (hA : ∀ i, 1 / 10 ≤ A i) :
    IntegrableOn continuousDensity (continuousRectangle A B) := by
  change Integrable _ ((Measure.pi fun _ : Fin n => (volume : Measure ℝ)).restrict _)
  rw [continuousRectangle, Measure.restrict_pi_pi]
  exact Integrable.fintype_prod (fun i => continuousReciprocal_integrable (hA i))

/-- Fubini for the actual restricted volume, with no mass premise. -/
theorem continuousRectangle_factorization {n : ℕ} (A B : Fin n → ℝ)
    (hAB : ∀ i, A i ≤ B i) :
    (∫ t in continuousRectangle A B, continuousDensity t) =
      ∏ i, ∫ x in A i..B i, 1 / x := by
  change (∫ t, continuousDensity t ∂((Measure.pi fun _ : Fin n => (volume : Measure ℝ)).restrict _)) = _
  rw [continuousRectangle, Measure.restrict_pi_pi]
  unfold continuousDensity
  rw [integral_fintype_prod_eq_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (hAB i)]

theorem continuousReciprocal_nonneg {A B : ℝ} (hA : 1 / 10 ≤ A) :
    0 ≤ ∫ x in Icc A B, 1 / x := by
  apply setIntegral_nonneg measurableSet_Icc
  intro x hx
  exact div_nonneg zero_le_one (by linarith [hx.1])

theorem continuousReciprocal_le {A B : ℝ} (hA : 1 / 10 ≤ A) (hAB : A ≤ B) :
    (∫ x in Icc A B, 1 / x) ≤ 10 * (B - A) := by
  calc
    _ ≤ ∫ _x in Icc A B, (10 : ℝ) := by
      apply setIntegral_mono_on (continuousReciprocal_integrable hA)
        (continuousOn_const.integrableOn_Icc) measurableSet_Icc
      intro x hx
      apply (div_le_iff₀ (by linarith [hx.1] : 0 < x)).mpr
      linarith [hx.1]
    _ = _ := by rw [setIntegral_const, Real.volume_real_Icc_of_le hAB]; simp [mul_comm]

theorem continuousCube_integral_eq_pow (n : ℕ) :
    (∫ t in continuousCube n, continuousDensity t) =
      (∫ x in Icc (1 / 10 : ℝ) (1 / 2), 1 / x) ^ n := by
  change (∫ t, continuousDensity t ∂((Measure.pi fun _ : Fin n => (volume : Measure ℝ)).restrict _)) = _
  rw [continuousCube, Measure.restrict_pi_pi]
  unfold continuousDensity
  rw [integral_fintype_prod_eq_prod]
  simp

theorem continuousCube_integral_bounds (n : ℕ) :
    0 ≤ (∫ t in continuousCube n, continuousDensity t) ∧
      (∫ t in continuousCube n, continuousDensity t) ≤ (4 : ℝ) ^ n := by
  rw [continuousCube_integral_eq_pow]
  have h0 := continuousReciprocal_nonneg (A := (1 / 10 : ℝ)) (B := 1 / 2) (le_refl _)
  have h4 := continuousReciprocal_le (A := (1 / 10 : ℝ)) (B := 1 / 2) (le_refl _) (by norm_num)
  norm_num only [show (10 : ℝ) * (1 / 2 - 1 / 10) = 4 by norm_num] at h4
  exact ⟨pow_nonneg h0 _, pow_le_pow_left₀ h0 h4 _⟩

theorem continuousRectangle_subset_cube {n : ℕ} (A B : Fin n → ℝ)
    (hA : ∀ i, 1 / 10 ≤ A i) (hB : ∀ i, B i ≤ 1 / 2) :
    continuousRectangle A B ⊆ continuousCube n := by
  intro t ht i hi
  exact ⟨(hA i).trans (ht i hi).1, (ht i hi).2.trans (hB i)⟩

/-- The positive-cube interface bundles real integrability with exact factorization. -/
theorem continuousRectangle_exact {n : ℕ} (A B : Fin n → ℝ)
    (hA : ∀ i, 1 / 10 ≤ A i) (hAB : ∀ i, A i ≤ B i) (hB : ∀ i, B i ≤ 1 / 2) :
    continuousRectangle A B ⊆ continuousCube n ∧
      IntegrableOn continuousDensity (continuousRectangle A B) ∧
      (∫ t in continuousRectangle A B, continuousDensity t) =
        ∏ i, ∫ x in A i..B i, 1 / x :=
  ⟨continuousRectangle_subset_cube A B hA hB, continuousRectangle_integrable A B hA,
    continuousRectangle_factorization A B hAB⟩

theorem continuousRectangle_integral_zero (A B : Fin 0 → ℝ) :
    (∫ t in continuousRectangle A B, continuousDensity t) = 1 := by
  rw [continuousRectangle_factorization A B (fun i => Fin.elim0 i)]
  simp

/-- A closed zero-width coordinate has zero continuous mass, not a deleted prime atom. -/
theorem continuousRectangle_integral_degenerate {n : ℕ} (j : Fin n)
    (A B : Fin n → ℝ) (hAB : ∀ i, A i ≤ B i) (hj : A j = B j) :
    (∫ t in continuousRectangle A B, continuousDensity t) = 0 := by
  rw [continuousRectangle_factorization A B hAB]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  rw [hj, intervalIntegral.integral_same]

end Wu2008DoubleSieve
