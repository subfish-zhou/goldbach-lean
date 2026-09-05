import MathlibNt.AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducerShort
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPrimitivePerron

/-!
# The half-step variant of the finite shift in Pan (2.23)

The cutoff is `y + 1/2`, while both finite polynomials retain their complete
source coefficients. This is a boundary-safe variant, not a transcription of
the natural-cutoff integral. No Perron truncation estimate is assumed here.
-/

noncomputable section
open Classical Complex Finset MeasureTheory Set Filter
open MathlibNt.SieveTheory.LiuWeight
open scoped BigOperators Topology

namespace AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer

/-- The complete short-polynomial kernel at the real half-step cutoff. -/
def halfStepShortKernel {q : ℕ} (f : ℕ → ℂ) (m H y A₁ A₂ k : ℕ)
    (χ : PrimitiveCharacter q) (s : ℂ) : ℂ :=
  panDyadicG f m A₁ A₂ k χ s * panShortF₁ m H χ s *
    (liuPanPerronHalfStep y : ℂ) ^ s / s

theorem halfStep_pos (y : ℕ) : 0 < liuPanPerronHalfStep y := by
  unfold liuPanPerronHalfStep
  positivity

theorem perronLine_verticalSection (F : ℂ → ℂ) (σ t : ℝ) :
    F (liuPanPerronLine σ t) = chen1973VerticalSection F σ t := rfl

theorem halfStepShortKernel_differentiableOn {q : ℕ} (f : ℕ → ℂ)
    (m H y A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q) :
    DifferentiableOn ℂ (halfStepShortKernel f m H y A₁ A₂ k χ)
      {s : ℂ | 0 < s.re} := by
  intro s hs
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hy0 : (liuPanPerronHalfStep y : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (halfStep_pos y).ne'
  exact (((panDyadicG_differentiable f m A₁ A₂ k χ s).mul
    (panShortF₁_differentiable m H χ s)).mul
    (differentiableAt_id.const_cpow (Or.inl hy0))).div
    differentiableAt_id hs0 |>.differentiableWithinAt

/-- Exact rectangle identity, with the actual differential `ds = i dt`. -/
theorem halfStepShortKernel_oriented_rectangle {q : ℕ} (f : ℕ → ℂ)
    (m H y A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q)
    {α T : ℝ} (hα : 1 / 2 ≤ α) (hT : 0 ≤ T) :
    I * (∫ t in -T..T, halfStepShortKernel f m H y A₁ A₂ k χ
      (liuPanPerronLine α t)) -
    I * (∫ t in -T..T, halfStepShortKernel f m H y A₁ A₂ k χ
      (liuPanPerronLine (1 / 2) t)) =
    (∫ u in (1 / 2 : ℝ)..α,
      halfStepShortKernel f m H y A₁ A₂ k χ (u + T * I)) -
    (∫ u in (1 / 2 : ℝ)..α,
      halfStepShortKernel f m H y A₁ A₂ k χ (u + (-T) * I)) := by
  have hf := (halfStepShortKernel_differentiableOn f m H y A₁ A₂ k χ).mono
    (show {s : ℂ | 1 / 2 ≤ s.re ∧ s.re ≤ α ∧ |s.im| ≤ T} ⊆
      {s : ℂ | 0 < s.re} from fun s hs => by dsimp; linarith [hs.1])
  have hc := Eq21FiniteContour_rectangle_vertical_identity hα hT hf
  have hc' := congrArg (fun z : ℂ => I * z) hc
  rw [← mul_assoc, I_mul_I] at hc'
  simpa [mul_sub, chen1973HorizontalSection, ← perronLine_verticalSection,
    sub_eq_add_neg, add_comm, mul_add] using hc'

theorem halfStepShortKernel_vertical_integrable {q : ℕ} (f : ℕ → ℂ)
    (m H y A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q)
    {α T v : ℝ} (hT : 0 ≤ T) (hv : v ∈ Set.Icc (1 / 2) α) :
    IntervalIntegrable (fun t => halfStepShortKernel f m H y A₁ A₂ k χ
      (liuPanPerronLine v t)) volume (-T) T := by
  apply Eq21FiniteContour_vertical_intervalIntegrable
    (f := halfStepShortKernel f m H y A₁ A₂ k χ) hT hv
  apply (halfStepShortKernel_differentiableOn f m H y A₁ A₂ k χ).continuousOn.mono
  intro s hs
  dsimp at hs ⊢
  linarith [hs.1]

theorem halfStepShortKernel_horizontal_integrable {q : ℕ} (f : ℕ → ℂ)
    (m H y A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q)
    {α t : ℝ} (hα : 1 / 2 ≤ α) :
    IntervalIntegrable (fun u : ℝ =>
      halfStepShortKernel f m H y A₁ A₂ k χ (u + t * I)) volume (1 / 2) α := by
  apply Eq21FiniteContour_horizontal_intervalIntegrable hα (le_refl |t|)
  apply (halfStepShortKernel_differentiableOn f m H y A₁ A₂ k χ).continuousOn.mono
  intro s hs
  dsimp at hs ⊢
  linarith [hs.1]

/-- Pointwise bounds use the actual source and prime polynomials. -/
theorem halfStepShortKernel_horizontal_pointwise {q : ℕ} (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (m H y A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q)
    (hy : 1 ≤ y) {α T u t : ℝ} (hu : 1 / 2 ≤ u) (huα : u ≤ α)
    (hT : 0 < T) (ht : |t| = T) :
    ‖halfStepShortKernel f m H y A₁ A₂ k χ (u + t * I)‖ ≤
      liuPanPerronHalfStep y ^ α / T * panHalfSum H * panHalfSum A₂ := by
  have hy1 : 1 ≤ liuPanPerronHalfStep y := by
    have : (1 : ℝ) ≤ y := by exact_mod_cast hy
    unfold liuPanPerronHalfStep
    linarith
  have hs : ((u : ℂ) + t * I).re = u := by simp
  have hn : T ≤ ‖(u : ℂ) + t * I‖ := by
    simpa [ht] using Complex.abs_im_le_norm ((u : ℂ) + t * I)
  have hG := panDyadicG_norm_le f hf m A₁ A₂ k χ (u + t * I) (by simpa using hu)
  have hF := panShortF₁_norm_le m H χ (u + t * I) (by simpa using hu)
  have hHN := panHalfSum_nonneg H
  have hAN := panHalfSum_nonneg A₂
  unfold halfStepShortKernel
  rw [norm_div, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (halfStep_pos y), hs]
  calc
    _ ≤ (panHalfSum A₂ * panHalfSum H * liuPanPerronHalfStep y ^ α) / T := by
      apply div_le_div₀ (by positivity)
      · apply mul_le_mul
        · exact mul_le_mul hG hF (norm_nonneg _) (panHalfSum_nonneg _)
        · exact Real.rpow_le_rpow_of_exponent_le hy1 huα
        · positivity
        · positivity
      · exact hT
      · exact hn
    _ = _ := by ring

theorem halfStepShortKernel_horizontal_integral_bound {q : ℕ} (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (m H y A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q)
    (hy : 1 ≤ y) {α T t : ℝ} (hα : 1 / 2 ≤ α) (hT : 0 < T) (ht : |t| = T) :
    ‖∫ u in (1 / 2 : ℝ)..α,
      halfStepShortKernel f m H y A₁ A₂ k χ (u + t * I)‖ ≤
      (liuPanPerronHalfStep y ^ α / T * panHalfSum H * panHalfSum A₂) *
        (α - 1 / 2) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (1 / 2 : ℝ)) (b := α)
    (f := fun u : ℝ => halfStepShortKernel f m H y A₁ A₂ k χ (u + t * I))
    (C := liuPanPerronHalfStep y ^ α / T * panHalfSum H * panHalfSum A₂) (by
      intro u hu
      rw [uIoc_of_le hα] at hu
      exact halfStepShortKernel_horizontal_pointwise f hf m H y A₁ A₂ k χ hy
        hu.1.le hu.2 hT ht)
  rw [abs_of_nonneg (sub_nonneg.mpr hα)] at h
  exact h

/-- The finite shift before any specialization of the height. -/
theorem halfStepShortKernel_finite_shift_bound {q : ℕ} (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (m H y A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q)
    (hy : 1 ≤ y) {α T : ℝ} (hα : 1 / 2 ≤ α) (hT : 0 < T) :
    ‖(∫ t in -T..T, halfStepShortKernel f m H y A₁ A₂ k χ
        (liuPanPerronLine α t)) -
      (∫ t in -T..T, halfStepShortKernel f m H y A₁ A₂ k χ
        (liuPanPerronLine (1 / 2) t))‖ ≤
      2 * (α - 1 / 2) * liuPanPerronHalfStep y ^ α / T *
        panHalfSum H * panHalfSum A₂ := by
  have he := halfStepShortKernel_oriented_rectangle f m H y A₁ A₂ k χ hα hT.le
  have ht := halfStepShortKernel_horizontal_integral_bound f hf m H y A₁ A₂ k χ
    hy hα hT (show |T| = T from abs_of_pos hT)
  have hb := halfStepShortKernel_horizontal_integral_bound f hf m H y A₁ A₂ k χ
    hy hα hT (show |-T| = T by simp [abs_of_pos hT])
  simp only [Complex.ofReal_neg] at hb
  have hn := congrArg norm he
  rw [← mul_sub, norm_mul, norm_I, one_mul] at hn
  rw [hn]
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ _ := add_le_add ht hb
    _ = _ := by ring

/-- A deliberately crude power bound sufficient at the exponential height. -/
theorem halfStep_source_power_le {x y : ℕ} (hx : 1 ≤ Real.log x)
    (hy : 1 ≤ y) (hyx : y ≤ x) :
    liuPanPerronHalfStep y ^ panSourceSigma x ≤ 4 * (x : ℝ) ^ 2 := by
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hyxR : (y : ℝ) ≤ x := by exact_mod_cast hyx
  have hY1 : 1 ≤ liuPanPerronHalfStep y := by
    unfold liuPanPerronHalfStep
    linarith
  have hYx : liuPanPerronHalfStep y ≤ 2 * (x : ℝ) := by
    unfold liuPanPerronHalfStep
    linarith
  calc
    _ ≤ liuPanPerronHalfStep y ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hY1 (panSourceSigma_bounds hx).2
    _ = liuPanPerronHalfStep y ^ (2 : ℕ) := Real.rpow_two _
    _ ≤ (2 * (x : ℝ)) ^ 2 := by gcongr
    _ = _ := by ring

/-- This retains exactly `exp (2 log² x)`; the fifth power merely bounds it. -/
theorem halfStep_source_height_ge_fifth {x : ℕ} (hx : 4 ≤ Real.log x) :
    (x : ℝ) ^ 5 ≤ panSourceHeight x := by
  have hx0 : (0 : ℝ) < x := by
    by_contra h
    have hz : x = 0 := by
      exact_mod_cast (le_antisymm (le_of_not_gt h) (Nat.cast_nonneg x))
    norm_num [hz] at hx
  have hh : 5 * Real.log (x : ℝ) ≤ 2 * (Real.log x) ^ 2 := by nlinarith
  have he := Real.exp_le_exp.mpr hh
  rw [mul_comm (5 : ℝ), Real.exp_mul, Real.exp_log hx0] at he
  rw [← Real.rpow_natCast (x : ℝ) 5]
  exact he

/-- Uniform unnormalized error for the actual full-polynomial contour shift. -/
theorem halfStepShortKernel_source_inverse_square {q x : ℕ} (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (m H y A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q)
    (hx : 4 ≤ Real.log x) (hy : 1 ≤ y) (hyx : y ≤ x)
    (hAy : A₂ ≤ y) (hHx : H ≤ x) :
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
      (Real.sqrt_le_sqrt (by exact_mod_cast hAy.trans hyx)) (by norm_num))
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

/-- The normalized `dt` integral, equivalently `(2πi)⁻¹ ∫ kernel(s) ds`. -/
def halfStepShortIntegral {q : ℕ} (f : ℕ → ℂ) (m H y A₁ A₂ k : ℕ)
    (χ : PrimitiveCharacter q) (σ T : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
    ∫ t in -T..T, halfStepShortKernel f m H y A₁ A₂ k χ (liuPanPerronLine σ t)

/-- The normalized half-step shift has the same absolute constant `64`. -/
theorem halfStepShortIntegral_source_inverse_square {q x : ℕ} (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (m H y A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q)
    (hx : 4 ≤ Real.log x) (hy : 1 ≤ y) (hyx : y ≤ x)
    (hAy : A₂ ≤ y) (hHx : H ≤ x) :
    ‖halfStepShortIntegral f m H y A₁ A₂ k χ (panSourceSigma x) (panSourceHeight x) -
      halfStepShortIntegral f m H y A₁ A₂ k χ (1 / 2) (panSourceHeight x)‖ ≤
      64 / (x : ℝ) ^ 2 := by
  have hnorm : ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    apply inv_le_one_of_one_le₀
    linarith [Real.one_le_pi_div_two]
  unfold halfStepShortIntegral
  rw [← mul_sub, norm_mul]
  calc
    _ ≤ 1 * ‖(∫ t in -(panSourceHeight x)..panSourceHeight x,
        halfStepShortKernel f m H y A₁ A₂ k χ (liuPanPerronLine (panSourceSigma x) t)) -
      (∫ t in -(panSourceHeight x)..panSourceHeight x,
        halfStepShortKernel f m H y A₁ A₂ k χ (liuPanPerronLine (1 / 2) t))‖ :=
      mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    _ ≤ _ := by
      rw [one_mul]
      exact halfStepShortKernel_source_inverse_square f hf m H y A₁ A₂ k χ
        hx hy hyx hAy hHx

end AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
