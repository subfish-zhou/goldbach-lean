import MathlibNt.Wu2004MeanValue.MovingIntegral

/-! The short moving kernel is shifted as a genuinely holomorphic function.
Only its pointwise norm estimate uses the frozen-coefficient bound. -/

noncomputable section
open Classical Complex Finset MeasureTheory
open MathlibNt.SieveTheory.LiuWeight
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
open scoped BigOperators

namespace Wu2004MeanValue

private theorem moving_rectangle {q : ℕ} (f : ℕ → ℂ) (v : ℕ → ℕ)
    (x m H A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q)
    {α T : ℝ} (hα : 1 / 2 ≤ α) (hT : 0 ≤ T) :
    I * (∫ t in -T..T, movingShortKernel f v x m H A₁ A₂ k χ (liuPanPerronLine α t)) -
    I * (∫ t in -T..T, movingShortKernel f v x m H A₁ A₂ k χ (liuPanPerronLine (1 / 2) t)) =
    (∫ u in (1 / 2 : ℝ)..α, movingShortKernel f v x m H A₁ A₂ k χ (u + T * I)) -
    (∫ u in (1 / 2 : ℝ)..α, movingShortKernel f v x m H A₁ A₂ k χ (u + (-T) * I)) := by
  have hf := (movingShortKernel_differentiableOn f v x m H A₁ A₂ k χ).mono
    (show {s : ℂ | 1 / 2 ≤ s.re ∧ s.re ≤ α ∧ |s.im| ≤ T} ⊆
      {s : ℂ | 0 < s.re} from fun s hs => by dsimp; linarith [hs.1])
  have hc := Eq21FiniteContour_rectangle_vertical_identity hα hT hf
  have hc' := congrArg (fun z : ℂ => I * z) hc
  rw [← mul_assoc, I_mul_I] at hc'
  simpa [mul_sub, chen1973HorizontalSection, ← perronLine_verticalSection,
    sub_eq_add_neg, add_comm, mul_add] using hc'

private theorem moving_horizontal_pointwise {q x : ℕ} (f : ℕ → ℂ) (v : ℕ → ℕ)
    (hf : ∀ a, ‖f a‖ ≤ 1) (hv : ∀ a, v a ≤ x) (m H A₁ A₂ k : ℕ)
    (χ : PrimitiveCharacter q) (hx : 1 ≤ x) {α T u t : ℝ}
    (hu : 1 / 2 ≤ u) (huα : u ≤ α) (hT : 0 < T) (ht : |t| = T) :
    ‖movingShortKernel f v x m H A₁ A₂ k χ (u + t * I)‖ ≤
      liuPanPerronHalfStep x ^ α / T * panHalfSum H * panHalfSum A₂ := by
  exact halfStepShortKernel_horizontal_pointwise (movingCoefficient f v x (u + t * I))
    (movingCoefficient_norm_le f v x hf hv (by simp; linarith))
    m H x A₁ A₂ k χ hx hu huα hT ht

/-- Finite-height contour bound, uniform in a common moving profile. -/
theorem moving_short_finite_shift_bound {q x : ℕ} (f : ℕ → ℂ) (v : ℕ → ℕ)
    (hf : ∀ a, ‖f a‖ ≤ 1) (hv : ∀ a, v a ≤ x) (m H A₁ A₂ k : ℕ)
    (χ : PrimitiveCharacter q) (hx : 1 ≤ x)
    {α T : ℝ} (hα : 1 / 2 ≤ α) (hT : 0 < T) :
    ‖(∫ t in -T..T, movingShortKernel f v x m H A₁ A₂ k χ (liuPanPerronLine α t)) -
      (∫ t in -T..T, movingShortKernel f v x m H A₁ A₂ k χ
        (liuPanPerronLine (1 / 2) t))‖ ≤
      2 * (α - 1 / 2) * liuPanPerronHalfStep x ^ α / T *
        panHalfSum H * panHalfSum A₂ := by
  have hhorizontal (t : ℝ) (ht : |t| = T) :
      ‖∫ u in (1 / 2 : ℝ)..α, movingShortKernel f v x m H A₁ A₂ k χ (u + t * I)‖ ≤
      (liuPanPerronHalfStep x ^ α / T * panHalfSum H * panHalfSum A₂) * (α - 1 / 2) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (1 / 2 : ℝ)) (b := α)
      (f := fun u : ℝ => movingShortKernel f v x m H A₁ A₂ k χ (u + t * I))
      (C := liuPanPerronHalfStep x ^ α / T * panHalfSum H * panHalfSum A₂) (by
        intro u hu
        rw [Set.uIoc_of_le hα] at hu
        exact moving_horizontal_pointwise f v hf hv m H A₁ A₂ k χ hx
          hu.1.le hu.2 hT ht)
    simpa only [abs_of_nonneg (sub_nonneg.mpr hα)] using h
  have he := moving_rectangle f v x m H A₁ A₂ k χ hα hT.le
  have ht := hhorizontal T (abs_of_pos hT)
  have hb := hhorizontal (-T) (by simp [abs_of_pos hT])
  simp only [Complex.ofReal_neg] at hb
  have hn := congrArg norm he
  rw [← mul_sub, norm_mul, norm_I, one_mul] at hn
  rw [hn]
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ _ := add_le_add ht hb
    _ = _ := by ring

private theorem moving_short_inverse_square {q x : ℕ} (f : ℕ → ℂ) (v : ℕ → ℕ)
    (hf : ∀ a, ‖f a‖ ≤ 1) (hv : ∀ a, v a ≤ x) (m H A₁ A₂ k : ℕ)
    (χ : PrimitiveCharacter q) (hx : 4 ≤ Real.log x) (hAx : A₂ ≤ x) (hHx : H ≤ x) :
    ‖movingShortIntegral f v x m H A₁ A₂ k χ (panSourceSigma x) (panSourceHeight x) -
      movingShortIntegral f v x m H A₁ A₂ k χ (1 / 2) (panSourceHeight x)‖ ≤
      64 / (x : ℝ) ^ 2 := by
  have hxlog : 1 ≤ Real.log x := by linarith
  have hxnat := source_pos_of_log hxlog
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hxnat
  have hσ := panSourceSigma_bounds hxlog
  have hT : 0 < panSourceHeight x := Real.exp_pos _
  have hHN := panHalfSum_nonneg H
  have hAN := panHalfSum_nonneg A₂
  have hsumH : panHalfSum H ≤ 2 * Real.sqrt x :=
    (panHalfSum_le H).trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (by exact_mod_cast hHx)) (by norm_num))
  have hsumA : panHalfSum A₂ ≤ 2 * Real.sqrt x :=
    (panHalfSum_le A₂).trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (by exact_mod_cast hAx)) (by norm_num))
  have hpow := halfStep_source_power_le hxlog hxnat le_rfl
  have hw : 2 * (panSourceSigma x - 1 / 2) ≤ 4 := by linarith [hσ.2]
  have hmain : 2 * (panSourceSigma x - 1 / 2) *
      liuPanPerronHalfStep x ^ panSourceSigma x ≤ 4 * (4 * (x : ℝ) ^ 2) :=
    mul_le_mul hw hpow (Real.rpow_nonneg (halfStep_pos x).le _) (by norm_num)
  have hkernel :
      ‖(∫ t in -(panSourceHeight x)..panSourceHeight x,
          movingShortKernel f v x m H A₁ A₂ k χ (liuPanPerronLine (panSourceSigma x) t)) -
        (∫ t in -(panSourceHeight x)..panSourceHeight x,
          movingShortKernel f v x m H A₁ A₂ k χ (liuPanPerronLine (1 / 2) t))‖ ≤
        64 / (x : ℝ) ^ 2 := by
    refine (moving_short_finite_shift_bound f v hf hv m H A₁ A₂ k χ hxnat hσ.1 hT).trans ?_
    calc
      _ ≤ (4 * (4 * (x : ℝ) ^ 2)) / panSourceHeight x *
          (2 * Real.sqrt x) * (2 * Real.sqrt x) := by gcongr
      _ = 64 * (x : ℝ) ^ 3 / panSourceHeight x := by
        calc
          _ = 64 * (x : ℝ) ^ 2 * (Real.sqrt x) ^ 2 / panSourceHeight x := by ring
          _ = _ := by rw [Real.sq_sqrt hx0.le]; ring
      _ ≤ 64 * (x : ℝ) ^ 3 / (x : ℝ) ^ 5 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (halfStep_source_height_ge_fifth hx)
      _ = _ := by field_simp
  have hnorm : ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    apply inv_le_one_of_one_le₀
    linarith [Real.one_le_pi_div_two]
  unfold movingShortIntegral
  rw [← mul_sub, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hnorm).trans hkernel

/-- The complete moving source cell, with both Perron polynomials retained,
has error `388/x²` after shifting only the short kernel. -/
theorem moving_source_cell_perron_shift {q x : ℕ} (f : ℕ → ℂ) (v : ℕ → ℕ)
    (hf : ∀ a, ‖f a‖ ≤ 1) (hv : ∀ a, 1 ≤ v a ∧ v a ≤ x)
    (m H A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q)
    (hx : 4 ≤ Real.log x) (hAx : A₂ ≤ x) (hHx : H ≤ x) :
    ‖movingAmplitude (panSourceG f m) (panSourceD m) v
        (2 ^ k * A₁) (min (2 ^ (k + 1) * A₁) A₂) χ -
      (movingShortIntegral f v x m H A₁ A₂ k χ (1 / 2) (panSourceHeight x) +
        movingLongIntegral f v x m H A₁ A₂ k χ (panSourceSigma x) (panSourceHeight x))‖ ≤
      388 / (x : ℝ) ^ 2 := by
  have hp := moving_amplitude_perron f hf v m (2 ^ k * A₁)
    (min (2 ^ (k + 1) * A₁) A₂) χ hx (fun a _ => hv a)
    ((min_le_right _ _).trans hAx)
  rw [moving_perron_eq_short_add_long f v x m H A₁ A₂ k χ
    (σ := panSourceSigma x) (T := panSourceHeight x)
    (by linarith [(panSourceSigma_bounds (x := x) (by linarith)).1])
    (hHx.trans (sourceHeight_floor_ge (x := x) (by linarith)))] at hp
  have hc := moving_short_inverse_square f v hf (fun a => (hv a).2) m H A₁ A₂ k χ hx hAx hHx
  calc
    _ ≤ ‖movingAmplitude (panSourceG f m) (panSourceD m) v
        (2 ^ k * A₁) (min (2 ^ (k + 1) * A₁) A₂) χ -
      (movingShortIntegral f v x m H A₁ A₂ k χ (panSourceSigma x) (panSourceHeight x) +
        movingLongIntegral f v x m H A₁ A₂ k χ (panSourceSigma x) (panSourceHeight x))‖ +
      ‖movingShortIntegral f v x m H A₁ A₂ k χ (panSourceSigma x) (panSourceHeight x) -
        movingShortIntegral f v x m H A₁ A₂ k χ (1 / 2) (panSourceHeight x)‖ := by
      convert norm_add_le
        (movingAmplitude (panSourceG f m) (panSourceD m) v
          (2 ^ k * A₁) (min (2 ^ (k + 1) * A₁) A₂) χ -
          (movingShortIntegral f v x m H A₁ A₂ k χ (panSourceSigma x) (panSourceHeight x) +
            movingLongIntegral f v x m H A₁ A₂ k χ (panSourceSigma x) (panSourceHeight x)))
        (movingShortIntegral f v x m H A₁ A₂ k χ (panSourceSigma x) (panSourceHeight x) -
          movingShortIntegral f v x m H A₁ A₂ k χ (1 / 2) (panSourceHeight x)) using 1
      congr 1
      ring
    _ ≤ 324 * ((x : ℝ) ^ 2)⁻¹ + 64 / (x : ℝ) ^ 2 := add_le_add hp hc
    _ = _ := by ring

end Wu2004MeanValue