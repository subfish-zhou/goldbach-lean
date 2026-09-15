import MathlibNt.AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducerPerronAssembly

/-!
# A source contour shift independent of the selected prefix

These are the necessary strengthened versions of the frozen half-step shift:
the coefficient support is bounded by the ambient `x`, not the prefix `y`.
All finite polynomials and both Perron integrals are retained.
-/

noncomputable section
open Classical Complex Finset MeasureTheory
open MathlibNt.SieveTheory.LiuWeight
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
open scoped BigOperators

namespace Wu2004MeanValue

private theorem selected_kernel_inverse_square {q x : ℕ} (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (m H y A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q)
    (hx : 4 ≤ Real.log x) (hy : 1 ≤ y) (hyx : y ≤ x)
    (hAx : A₂ ≤ x) (hHx : H ≤ x) :
    ‖(∫ t in -(panSourceHeight x)..panSourceHeight x,
        halfStepShortKernel f m H y A₁ A₂ k χ (liuPanPerronLine (panSourceSigma x) t)) -
      (∫ t in -(panSourceHeight x)..panSourceHeight x,
        halfStepShortKernel f m H y A₁ A₂ k χ (liuPanPerronLine (1 / 2) t))‖ ≤
      64 / (x : ℝ) ^ 2 := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hy.trans hyx
  have hσ := panSourceSigma_bounds (show 1 ≤ Real.log x by linarith)
  have hT : 0 < panSourceHeight x := Real.exp_pos _
  have hHN := panHalfSum_nonneg H
  have hAN := panHalfSum_nonneg A₂
  have hsumH : panHalfSum H ≤ 2 * Real.sqrt x :=
    (panHalfSum_le H).trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (by exact_mod_cast hHx)) (by norm_num))
  have hsumA : panHalfSum A₂ ≤ 2 * Real.sqrt x :=
    (panHalfSum_le A₂).trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (by exact_mod_cast hAx)) (by norm_num))
  have hpow := halfStep_source_power_le (show 1 ≤ Real.log x by linarith) hy hyx
  have hw : 2 * (panSourceSigma x - 1 / 2) ≤ 4 := by linarith [hσ.2]
  have hY := (halfStep_pos y).le
  have hmain : 2 * (panSourceSigma x - 1 / 2) *
      liuPanPerronHalfStep y ^ panSourceSigma x ≤ 4 * (4 * (x : ℝ) ^ 2) :=
    mul_le_mul hw hpow (Real.rpow_nonneg hY _) (by norm_num)
  refine (halfStepShortKernel_finite_shift_bound f hf m H y A₁ A₂ k χ
    hy hσ.1 hT).trans ?_
  calc
    _ ≤ (4 * (4 * (x : ℝ) ^ 2)) / panSourceHeight x *
        (2 * Real.sqrt x) * (2 * Real.sqrt x) := by
      gcongr
    _ = 64 * (x : ℝ) ^ 3 / panSourceHeight x := by
      calc
        _ = 64 * (x : ℝ) ^ 2 * (Real.sqrt x) ^ 2 / panSourceHeight x := by ring
        _ = _ := by rw [Real.sq_sqrt hx0.le]; ring
    _ ≤ 64 * (x : ℝ) ^ 3 / (x : ℝ) ^ 5 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (halfStep_source_height_ge_fifth hx)
    _ = _ := by field_simp

private theorem selected_short_inverse_square {q x : ℕ} (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (m H y A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q)
    (hx : 4 ≤ Real.log x) (hy : 1 ≤ y) (hyx : y ≤ x)
    (hAx : A₂ ≤ x) (hHx : H ≤ x) :
    ‖halfStepShortIntegral f m H y A₁ A₂ k χ (panSourceSigma x) (panSourceHeight x) -
      halfStepShortIntegral f m H y A₁ A₂ k χ (1 / 2) (panSourceHeight x)‖ ≤
      64 / (x : ℝ) ^ 2 := by
  have hnorm : ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    apply inv_le_one_of_one_le₀
    linarith [Real.one_le_pi_div_two]
  unfold halfStepShortIntegral
  rw [← mul_sub, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hnorm).trans
    (selected_kernel_inverse_square f hf m H y A₁ A₂ k χ hx hy hyx hAx hHx)

/-- The actual prefix source cell has Perron error `388/x²` even when its
complete source block extends beyond the selected prefix. -/
theorem selected_source_cell_perron_shift {q x y : ℕ} (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (m H A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q)
    (hx : 4 ≤ Real.log x) (hy : 1 ≤ y) (hyx : y ≤ x)
    (hAx : A₂ ≤ x) (hHx : H ≤ x) :
    ‖panSourceCharacterAmplitude (panSourceG f m) (panSourceD m) y
        (2 ^ k * A₁) (min (2 ^ (k + 1) * A₁) A₂) χ -
      (halfStepShortIntegral f m H y A₁ A₂ k χ (1 / 2) (panSourceHeight x) +
        halfStepLongIntegral f m H y A₁ A₂ k χ (panSourceSigma x) (panSourceHeight x))‖ ≤
      388 / (x : ℝ) ^ 2 := by
  have hp := source_amplitude_perron f hf m (2 ^ k * A₁)
    (min (2 ^ (k + 1) * A₁) A₂) χ hx hy hyx ((min_le_right _ _).trans hAx)
  rw [perron_integral_eq_short_add_long f m H y A₁ A₂ k χ
    (σ := panSourceSigma x) (T := panSourceHeight x)
    (panSourceSigma_bounds (x := x) (by linarith)).1 (Real.exp_pos _).le
    (hHx.trans (sourceHeight_floor_ge (x := x) (by linarith)))] at hp
  have hc := selected_short_inverse_square f hf m H y A₁ A₂ k χ hx hy hyx hAx hHx
  calc
    _ ≤ ‖panSourceCharacterAmplitude (panSourceG f m) (panSourceD m) y
        (2 ^ k * A₁) (min (2 ^ (k + 1) * A₁) A₂) χ -
      (halfStepShortIntegral f m H y A₁ A₂ k χ (panSourceSigma x) (panSourceHeight x) +
        halfStepLongIntegral f m H y A₁ A₂ k χ (panSourceSigma x) (panSourceHeight x))‖ +
      ‖halfStepShortIntegral f m H y A₁ A₂ k χ (panSourceSigma x) (panSourceHeight x) -
        halfStepShortIntegral f m H y A₁ A₂ k χ (1 / 2) (panSourceHeight x)‖ := by
      convert norm_add_le
        (panSourceCharacterAmplitude (panSourceG f m) (panSourceD m) y
          (2 ^ k * A₁) (min (2 ^ (k + 1) * A₁) A₂) χ -
          (halfStepShortIntegral f m H y A₁ A₂ k χ (panSourceSigma x) (panSourceHeight x) +
            halfStepLongIntegral f m H y A₁ A₂ k χ (panSourceSigma x) (panSourceHeight x)))
        (halfStepShortIntegral f m H y A₁ A₂ k χ (panSourceSigma x) (panSourceHeight x) -
          halfStepShortIntegral f m H y A₁ A₂ k χ (1 / 2) (panSourceHeight x)) using 1
      congr 1
      ring
    _ ≤ 324 * ((x : ℝ) ^ 2)⁻¹ + 64 / (x : ℝ) ^ 2 := add_le_add hp hc
    _ = _ := by ring

end Wu2004MeanValue
