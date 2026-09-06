import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21FiniteContour
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21FullKernelBudget

noncomputable section
open Classical Complex Finset MeasureTheory Set Filter
open scoped BigOperators ArithmeticFunction Topology
namespace AnalyticNumberTheory.LargeSieve

/-- Exact arbitrary-cutoff tail moment: the cutoff cost is retained. -/
theorem Eq21FiniteContour_powerTail
    {a T : ℝ} (hT : 0 < T) (N : ℕ) (hN : 0 < N) :
    IntegrableOn (fun t : ℝ => a ^ N / t ^ (N + 1)) (Ioi T) ∧
      (∫ t in Ioi T, a ^ N / t ^ (N + 1)) = (a / T) ^ N / (N : ℝ) := by
  have hi := chen1973Lemma6_eq21_scaledLogTail_integrable hT N 0 hN
  have he := chen1973Lemma6_eq21_scaledLogTail_integral hT N 0 hN
  simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one] at hi he
  have hfun : (fun t : ℝ => a ^ N / t ^ (N + 1)) =
      (fun t : ℝ => (a / T) ^ N * (T ^ N / t ^ (N + 1))) := by
    funext t
    rw [div_pow]
    field_simp
  rw [hfun]
  exact ⟨hi.const_mul _, by rw [integral_const_mul, he]; ring⟩

/-- A pointwise true-power majorant yields a genuine tail budget. -/
theorem Eq21FiniteContour_tail_norm_bound
    {f : ℝ → ℂ} {a T C : ℝ} (hT : 0 < T) (N : ℕ) (hN : 0 < N)
    (hf : IntegrableOn f (Ioi T))
    (hpoint : ∀ t ∈ Ioi T, ‖f t‖ ≤ C * (a ^ N / t ^ (N + 1))) :
    ‖∫ t in Ioi T, f t‖ ≤ C * ((a / T) ^ N / (N : ℝ)) := by
  obtain ⟨hg, he⟩ := Eq21FiniteContour_powerTail (a := a) hT N hN
  calc
    _ ≤ ∫ t in Ioi T, ‖f t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi T, C * (a ^ N / t ^ (N + 1)) := by
      apply integral_mono_ae hf.norm (hg.const_mul C)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hpoint t ht
    _ = _ := by rw [integral_const_mul, he]

/-- Pointwise norm estimate for the actual character-weighted term. -/
theorem Eq21FiniteContour_term_norm_le
    {x d : ℕ} (χ : PrimitiveCharacter d) {pp : ℕ × ℕ}
    (hy : 0 < (x : ℝ) / ((pp.1 : ℝ) * pp.2)) {s : ℂ} {M : ℝ}
    (hderiv : ‖chen1973PrimitiveLDeriv d s χ /
      chen1973Lemma6PrimitiveLValue d s χ‖ ≤ M) :
    ‖chen1973Lemma6Eq21TermShiftIntegrand x d χ pp s‖ ≤
      ((x : ℝ) / ((pp.1 : ℝ) * pp.2)) ^ s.re *
        ‖chen1973MellinKernel (x : ℝ) s‖ * M := by
  unfold chen1973Lemma6Eq21TermShiftIntegrand chen1973Lemma6Eq21ShiftIntegrand
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  calc
    _ ≤ 1 * ((((x : ℝ) / ((pp.1 : ℝ) * pp.2)) ^ s.re *
        ‖chen1973MellinKernel (x : ℝ) s‖) * M) := by
      apply mul_le_mul (DirichletCharacter.norm_le_one χ.1 _) _ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hderiv (by positivity)
    _ = _ := one_mul _

/-- Lossless kernel tail on either sign of the imaginary coordinate. -/
theorem Eq21FiniteContour_kernel_tail_abs
    {x : ℕ} (hx : 1 < x) {v t : ℝ} (ht : 0 < |t|) :
    ‖chen1973MellinKernel (x : ℝ) ((v : ℂ) + t * I)‖ ≤
      chen1973PerronScale (x : ℝ) ^ (chen1973PerronOrder (x : ℝ) + 1) /
        |t| ^ (chen1973PerronOrder (x : ℝ) + 2) := by
  by_cases h : 0 ≤ t
  · simpa [abs_of_nonneg h] using
      chen1973Lemma6_eq21_mellinKernel_tail_bound (σ := v) hx (by simpa [abs_of_nonneg h] using ht)
  · have he : ‖chen1973MellinKernel (x : ℝ) ((v : ℂ) + t * I)‖ =
        ‖chen1973MellinKernel (x : ℝ) ((v : ℂ) + (-t) * I)‖ := by
      simpa using chen1973Lemma6_eq21_mellinKernel_norm_neg (x : ℝ) v (-t)
    rw [he]
    simpa [abs_of_neg (lt_of_not_ge h)] using
      chen1973Lemma6_eq21_mellinKernel_tail_bound (σ := v) hx (by linarith : 0 < -t)

/-- Both actual alpha tails separately satisfy the sharp arbitrary-cutoff budget. -/
theorem Eq21FiniteContour_alpha_tails
    {x d : ℕ} (hx : 3 ≤ x) (hd : 1 < d) (χ : PrimitiveCharacter d)
    {pp : ℕ × ℕ} (hy : 0 < (x : ℝ) / ((pp.1 : ℝ) * pp.2))
    {T : ℝ} (hT : 0 < T) :
    let F := chen1973VerticalSection (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp)
      (chen1973Lemma6Alpha x)
    let a := chen1973PerronScale (x : ℝ)
    let N := chen1973PerronOrder (x : ℝ) + 1
    let C := 6 * (Real.log (x : ℝ)) ^ 2 *
      ((x : ℝ) / ((pp.1 : ℝ) * pp.2)) ^ chen1973Lemma6Alpha x
    ‖∫ t in Iio (-T), F t‖ ≤ C * ((a / T) ^ N / (N : ℝ)) ∧
    ‖∫ t in Ioi T, F t‖ ≤ C * ((a / T) ^ N / (N : ℝ)) := by
  let _ : NeZero d := ⟨Nat.ne_zero_of_lt hd⟩
  dsimp only
  let F := chen1973VerticalSection (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp)
    (chen1973Lemma6Alpha x)
  let a := chen1973PerronScale (x : ℝ)
  let N := chen1973PerronOrder (x : ℝ) + 1
  let C := 6 * (Real.log (x : ℝ)) ^ 2 *
    ((x : ℝ) / ((pp.1 : ℝ) * pp.2)) ^ chen1973Lemma6Alpha x
  have hi : Integrable F := chen1973Lemma6_eq21_alphaTerm_integrable hx hd χ hy
  have hp : ∀ t : ℝ, 0 < |t| → ‖F t‖ ≤ C * (a ^ N / |t| ^ (N + 1)) := by
    intro t ht
    have hb := Eq21FiniteContour_term_norm_le χ hy
      (chen1973Lemma6_alphaLogDerivative_le_six_mul_log_sq χ hd hx t)
    have hk := Eq21FiniteContour_kernel_tail_abs (v := chen1973Lemma6Alpha x)
      (by omega : 1 < x) ht
    dsimp only [F, chen1973VerticalSection]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] at hb
    calc
      _ ≤ _ := hb
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hk (by positivity)) (by positivity)
      _ = _ := by dsimp [C, a, N]; ring
  have hplus := Eq21FiniteContour_tail_norm_bound (a := a) (C := C) hT N (Nat.succ_pos _)
    hi.integrableOn (fun t ht => by
      have ht0 := hT.trans ht
      simpa [abs_of_pos ht0] using hp t (abs_pos.mpr ht0.ne'))
  have hminus := Eq21FiniteContour_tail_norm_bound (f := fun t => F (-t)) (a := a) (C := C)
    hT N (Nat.succ_pos _) hi.comp_neg.integrableOn (fun t ht => by
      have ht0 := hT.trans ht
      simpa [abs_neg, abs_of_pos ht0] using hp (-t) (by simpa [abs_neg, abs_of_pos ht0]))
  have hreflect : (∫ t in Iio (-T), F t) = ∫ t in Ioi T, F (-t) := by
    rw [← integral_Iic_eq_integral_Iio]
    have h := integral_comp_neg_Iic (-T) (fun t => F (-t))
    simpa only [neg_neg] using h
  exact ⟨by rw [hreflect]; exact hminus, hplus⟩

/-- Each horizontal edge is paid at the selected height, not via an infinite-height limit. -/
theorem Eq21FiniteContour_horizontal_bound
    {x d : ℕ} (hx : 3 ≤ x) (hd : 1 < d) (χ : PrimitiveCharacter d)
    {pp : ℕ × ℕ} (hp₁ : 0 < pp.1) (hp₂ : 0 < pp.2)
    (hy : 1 < (x : ℝ) / ((pp.1 : ℝ) * pp.2)) {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M)
    (hzero : ∀ s : ℂ, chen1973Lemma6Eq21Sigma x ≤ s.re →
      s.re ≤ chen1973Lemma6Alpha x → |s.im| ≤ T →
      chen1973Lemma6PrimitiveLValue d s χ ≠ 0)
    (hderiv : ∀ s : ℂ, chen1973Lemma6Eq21Sigma x ≤ s.re →
      s.re ≤ chen1973Lemma6Alpha x → |s.im| ≤ T →
      ‖chen1973PrimitiveLDeriv d s χ / chen1973Lemma6PrimitiveLValue d s χ‖ ≤ M) :
    ‖chen1973HorizontalSection (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp)
      (chen1973Lemma6Eq21Sigma x) (chen1973Lemma6Alpha x) T‖ ≤
      2 * (chen1973Lemma6Alpha x - chen1973Lemma6Eq21Sigma x) * M *
        ((x : ℝ) / ((pp.1 : ℝ) * pp.2)) ^ chen1973Lemma6Alpha x *
        (chen1973PerronScale (x : ℝ) / T) ^ (chen1973PerronOrder (x : ℝ) + 1) / T := by
  let y := (x : ℝ) / ((pp.1 : ℝ) * pp.2)
  let a := chen1973PerronScale (x : ℝ)
  let N := chen1973PerronOrder (x : ℝ) + 1
  let C := y ^ chen1973Lemma6Alpha x * (a / T) ^ N / T * M
  have hσα := chen1973Lemma6_eq21_sigma_le_alpha hx
  have hf := (Eq21FiniteContour_term_differentiableOn hx hd χ hp₁ hp₂ hzero).continuousOn
  have hb : ∀ t : ℝ, |t| = T →
      ‖∫ v in chen1973Lemma6Eq21Sigma x..chen1973Lemma6Alpha x,
        chen1973Lemma6Eq21TermShiftIntegrand x d χ pp ((v : ℂ) + t * I)‖ ≤
        C * (chen1973Lemma6Alpha x - chen1973Lemma6Eq21Sigma x) := by
    intro t ht
    have hi := Eq21FiniteContour_horizontal_intervalIntegrable hσα ht.le hf
    have hp : ∀ v ∈ uIoc (chen1973Lemma6Eq21Sigma x) (chen1973Lemma6Alpha x),
        ‖chen1973Lemma6Eq21TermShiftIntegrand x d χ pp ((v : ℂ) + t * I)‖ ≤ C := by
      intro v hv
      rw [uIoc_of_le hσα] at hv
      have hD := hderiv ((v : ℂ) + t * I) (by simpa using hv.1.le)
        (by simpa using hv.2) (by simpa using ht.le)
      have hp := Eq21FiniteContour_term_norm_le χ (zero_lt_one.trans hy) hD
      have hk := Eq21FiniteContour_kernel_tail_abs (x := x) (v := v) (t := t)
        (by omega) (by rw [ht]; exact hT)
      rw [ht] at hk
      have hyv : y ^ v ≤ y ^ chen1973Lemma6Alpha x := Real.rpow_le_rpow_of_exponent_le hy.le hv.2
      calc
        _ ≤ _ := hp
        _ ≤ (y ^ chen1973Lemma6Alpha x * (a ^ N / T ^ (N + 1))) * M := by
          apply mul_le_mul_of_nonneg_right _ hM
          exact mul_le_mul (by simpa using hyv) hk (norm_nonneg _) (by positivity)
        _ = C := by dsimp [C]; rw [div_pow, pow_succ]; ring
    simpa [abs_of_nonneg (sub_nonneg.mpr hσα)] using
      intervalIntegral.norm_integral_le_of_norm_le_const hp
  have hminus := hb (-T) (by simp [abs_of_pos hT])
  have hplus := hb T (abs_of_pos hT)
  simp only [Complex.ofReal_neg] at hminus
  unfold chen1973HorizontalSection
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ _ := add_le_add hminus hplus
    _ = _ := by dsimp [C, y, a, N]; ring

/-- Discard only the smoothing factor; this is not a radial replacement. -/
theorem Eq21FiniteContour_kernel_le_inv {x : ℕ} (hx : 1 < x) {σ t b : ℝ}
    (hσ : 0 ≤ σ) (hb : 0 < b) (hbs : b ≤ ‖(σ : ℂ) + t * I‖) :
    ‖chen1973MellinKernel (x : ℝ) ((σ : ℂ) + t * I)‖ ≤ b⁻¹ := by
  exact eq21_kernel_le_inv hx hσ hb hbs

/-- The short true kernel costs only twice (inverse real part plus log height). -/
theorem Eq21FiniteContour_kernel_short
    {x : ℕ} (hx : 3 ≤ x) {σ T : ℝ} (hσ : 0 < σ) (hT : 1 ≤ T) :
    (∫ t in -T..T, ‖chen1973MellinKernel (x : ℝ) ((σ : ℂ) + t * I)‖) ≤
      2 * (σ⁻¹ + Real.log T) := by
  let K := fun t : ℝ => ‖chen1973MellinKernel (x : ℝ) ((σ : ℂ) + t * I)‖
  have hK : Integrable K := by
    simpa only [pow_zero, mul_one] using
      (chen1973Lemma6_eq21_weightedKernel_full_integrable_and_bound
        (d := 1) hx le_rfl hσ 0).1
  have hhead : (∫ t in (0 : ℝ)..1, K t) ≤ σ⁻¹ := by
    calc
      _ ≤ ∫ _t in (0 : ℝ)..1, σ⁻¹ := by
        apply intervalIntegral.integral_mono_on zero_le_one hK.intervalIntegrable
          intervalIntegrable_const
        intro t _
        apply Eq21FiniteContour_kernel_le_inv (by omega) hσ.le hσ
        simpa [abs_of_pos hσ] using Complex.abs_re_le_norm ((σ : ℂ) + t * I)
      _ = _ := by simp
  have hInv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 1 T := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_id.inv₀
    intro t ht
    rw [uIcc_of_le hT] at ht
    exact ne_of_gt (zero_lt_one.trans_le ht.1)
  have hmid : (∫ t in (1 : ℝ)..T, K t) ≤ Real.log T := by
    calc
      _ ≤ ∫ t in (1 : ℝ)..T, t⁻¹ := by
        apply intervalIntegral.integral_mono_on hT hK.intervalIntegrable hInv
        intro t ht
        have ht0 := zero_lt_one.trans_le ht.1
        apply Eq21FiniteContour_kernel_le_inv (by omega) hσ.le ht0
        simpa [abs_of_pos ht0] using Complex.abs_im_le_norm ((σ : ℂ) + t * I)
      _ = _ := by rw [integral_inv_of_pos zero_lt_one (zero_lt_one.trans_le hT)]; simp
  have hpos : (∫ t in (0 : ℝ)..T, K t) ≤ σ⁻¹ + Real.log T := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hK.intervalIntegrable (a := 0) (b := 1)) (hK.intervalIntegrable (a := 1) (b := T))]
    exact add_le_add hhead hmid
  have heven : ∀ t, K (-t) = K t := by
    intro t
    simpa [K] using chen1973Lemma6_eq21_mellinKernel_norm_neg (x : ℝ) σ t
  have hreflect : (∫ t in -T..0, K t) = ∫ t in (0 : ℝ)..T, K t := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := T) K
    simpa only [heven, neg_zero] using h.symm
  change (∫ t in -T..T, K t) ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hK.intervalIntegrable (a := -T) (b := 0)) (hK.intervalIntegrable (a := 0) (b := T)), hreflect]
  linarith

/-- Actual short sigma edge, requiring the log derivative only in the finite rectangle. -/
theorem Eq21FiniteContour_short_term_bound
    {x d : ℕ} (hx : 3 ≤ x) (hd : 1 < d) (χ : PrimitiveCharacter d)
    {pp : ℕ × ℕ} (hp₁ : 0 < pp.1) (hp₂ : 0 < pp.2)
    (hy : 0 < (x : ℝ) / ((pp.1 : ℝ) * pp.2)) {T M : ℝ} (hT : 1 ≤ T) (hM : 0 ≤ M)
    (hzero : ∀ s : ℂ, chen1973Lemma6Eq21Sigma x ≤ s.re →
      s.re ≤ chen1973Lemma6Alpha x → |s.im| ≤ T →
      chen1973Lemma6PrimitiveLValue d s χ ≠ 0)
    (hderiv : ∀ s : ℂ, chen1973Lemma6Eq21Sigma x ≤ s.re →
      s.re ≤ chen1973Lemma6Alpha x → |s.im| ≤ T →
      ‖chen1973PrimitiveLDeriv d s χ / chen1973Lemma6PrimitiveLValue d s χ‖ ≤ M) :
    ‖∫ t in -T..T, chen1973VerticalSection
      (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp) (chen1973Lemma6Eq21Sigma x) t‖ ≤
      2 * ((x : ℝ) / ((pp.1 : ℝ) * pp.2)) ^ chen1973Lemma6Eq21Sigma x * M *
        ((chen1973Lemma6Eq21Sigma x)⁻¹ + Real.log T) := by
  let σ := chen1973Lemma6Eq21Sigma x
  let y := (x : ℝ) / ((pp.1 : ℝ) * pp.2)
  let K := fun t : ℝ => ‖chen1973MellinKernel (x : ℝ) ((σ : ℂ) + t * I)‖
  let F := chen1973VerticalSection (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp) σ
  have hσ := chen1973Lemma6_eq21_sigma_pos hx
  have hσα := chen1973Lemma6_eq21_sigma_le_alpha hx
  have hT0 := zero_le_one.trans hT
  have hTT : -T ≤ T := by linarith
  have hf := Eq21FiniteContour_vertical_intervalIntegrable hT0 ⟨le_rfl, hσα⟩
    (Eq21FiniteContour_term_differentiableOn hx hd χ hp₁ hp₂ hzero).continuousOn
  have hK : Integrable K := by
    simpa only [pow_zero, mul_one] using
      (chen1973Lemma6_eq21_weightedKernel_full_integrable_and_bound
        (d := 1) hx le_rfl hσ 0).1
  change ‖∫ t in -T..T, F t‖ ≤ _
  calc
    _ ≤ ∫ t in -T..T, ‖F t‖ := intervalIntegral.norm_integral_le_integral_norm hTT
    _ ≤ ∫ t in -T..T, (y ^ σ * M) * K t := by
      apply intervalIntegral.integral_mono_on hTT hf.norm (hK.intervalIntegrable.const_mul _)
      intro t ht
      have hb := Eq21FiniteContour_term_norm_le χ hy
        (hderiv ((σ : ℂ) + t * I) (by simp [σ]) (by simpa [σ] using hσα)
          (by simpa using abs_le.mpr ht))
      simpa [F, K, chen1973VerticalSection, σ, y, mul_assoc, mul_left_comm, mul_comm] using hb
    _ = (y ^ σ * M) * ∫ t in -T..T, K t := intervalIntegral.integral_const_mul _ _
    _ ≤ (y ^ σ * M) * (2 * (σ⁻¹ + Real.log T)) :=
      mul_le_mul_of_nonneg_left (Eq21FiniteContour_kernel_short hx hσ hT) (by positivity)
    _ = _ := by dsimp [y, σ]; ring

/-- W3 (star): complete finite-contour bound on the actual Phi term.
The only analytic inputs concern the finite rectangle. The alpha tails are
unconditional and retain the complete production smoothing order. -/
theorem Eq21FiniteContour_truncated_term_bound
    {x d : ℕ} (hx : 3 ≤ x) (hd : 1 < d) (χ : PrimitiveCharacter d)
    {pp : ℕ × ℕ} (hp₁ : 0 < pp.1) (hp₂ : 0 < pp.2)
    (hy : 1 < (x : ℝ) / ((pp.1 : ℝ) * pp.2)) {T M : ℝ} (hT : 1 ≤ T) (hM : 0 ≤ M)
    (hzero : ∀ s : ℂ, chen1973Lemma6Eq21Sigma x ≤ s.re →
      s.re ≤ chen1973Lemma6Alpha x → |s.im| ≤ T →
      chen1973Lemma6PrimitiveLValue d s χ ≠ 0)
    (hderiv : ∀ s : ℂ, chen1973Lemma6Eq21Sigma x ≤ s.re →
      s.re ≤ chen1973Lemma6Alpha x → |s.im| ≤ T →
      ‖chen1973PrimitiveLDeriv d s χ / chen1973Lemma6PrimitiveLValue d s χ‖ ≤ M) :
    let y := (x : ℝ) / ((pp.1 : ℝ) * pp.2)
    let σ := chen1973Lemma6Eq21Sigma x
    let α := chen1973Lemma6Alpha x
    let a := chen1973PerronScale (x : ℝ)
    let N := chen1973PerronOrder (x : ℝ) + 1
    ‖chen1973Lemma6ActualPhi x d χ pp * χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d)‖ / Real.log y ≤
      y ^ σ * M * (σ⁻¹ + Real.log T) / (Real.pi * Real.log y) +
      y ^ α / (Real.pi * Real.log y) * (a / T) ^ N *
        (6 * (Real.log (x : ℝ)) ^ 2 / (N : ℝ) + (α - σ) * M / T) := by
  let y := (x : ℝ) / ((pp.1 : ℝ) * pp.2)
  let σ := chen1973Lemma6Eq21Sigma x
  let α := chen1973Lemma6Alpha x
  let a := chen1973PerronScale (x : ℝ)
  let N := chen1973PerronOrder (x : ℝ) + 1
  let F := chen1973Lemma6Eq21TermShiftIntegrand x d χ pp
  let V := ∫ t in -T..T, chen1973VerticalSection F σ t
  let H := chen1973HorizontalSection F σ α T
  let Rminus := ∫ t in Iio (-T), chen1973VerticalSection F α t
  let Rplus := ∫ t in Ioi T, chen1973VerticalSection F α t
  have hT0 := zero_lt_one.trans_le hT
  have hy0 := zero_lt_one.trans hy
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hid := Eq21FiniteContour_actualPhi_eq_truncated_with_alpha_tails
    hx hd χ hp₁ hp₂ hT0.le hzero
  have hV := Eq21FiniteContour_short_term_bound hx hd χ hp₁ hp₂ hy0 hT hM hzero hderiv
  have hH := Eq21FiniteContour_horizontal_bound hx hd χ hp₁ hp₂ hy hT0 hM hzero hderiv
  obtain ⟨hRm, hRp⟩ := Eq21FiniteContour_alpha_tails hx hd χ hy0 hT0
  change ‖V‖ ≤ 2 * y ^ σ * M * (σ⁻¹ + Real.log T) at hV
  change ‖H‖ ≤ 2 * (α - σ) * M * y ^ α * (a / T) ^ N / T at hH
  change ‖Rminus‖ ≤ (6 * (Real.log (x : ℝ)) ^ 2 * y ^ α) * ((a / T) ^ N / (N : ℝ)) at hRm
  change ‖Rplus‖ ≤ (6 * (Real.log (x : ℝ)) ^ 2 * y ^ α) * ((a / T) ^ N / (N : ℝ)) at hRp
  change chen1973Lemma6ActualPhi x d χ pp * χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) =
    -(((1 / (2 * Real.pi) : ℝ) : ℂ) * (V + I * H + Rminus + Rplus)) at hid
  have hnorm : ‖V + I * H + Rminus + Rplus‖ ≤
      ((‖V‖ + ‖H‖) + ‖Rminus‖) + ‖Rplus‖ := by
    calc
      _ ≤ ‖V + I * H + Rminus‖ + ‖Rplus‖ := norm_add_le _ _
      _ ≤ (‖V + I * H‖ + ‖Rminus‖) + ‖Rplus‖ := by
        exact add_le_add (norm_add_le (V + I * H) Rminus) le_rfl
      _ ≤ ((‖V‖ + ‖I * H‖) + ‖Rminus‖) + ‖Rplus‖ := by
        exact add_le_add (add_le_add (norm_add_le V (I * H)) le_rfl) le_rfl
      _ = _ := by simp
  have hb := hnorm.trans (add_le_add (add_le_add (add_le_add hV hH) hRm) hRp)
  change _ / Real.log y ≤ _
  rw [hid, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ (1 : ℝ) / (2 * Real.pi) by positivity)]
  calc
    _ ≤ (1 / (2 * Real.pi) *
      ((2 * y ^ σ * M * (σ⁻¹ + Real.log T) +
        2 * (α - σ) * M * y ^ α * (a / T) ^ N / T) +
        (6 * (Real.log (x : ℝ)) ^ 2 * y ^ α) * ((a / T) ^ N / (N : ℝ)) +
        (6 * (Real.log (x : ℝ)) ^ 2 * y ^ α) * ((a / T) ^ N / (N : ℝ)))) / Real.log y := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hb (by positivity)) hlog.le
    _ = _ := by
      change _ = y ^ σ * M * (σ⁻¹ + Real.log T) / (Real.pi * Real.log y) +
        y ^ α / (Real.pi * Real.log y) * (a / T) ^ N *
          (6 * (Real.log (x : ℝ)) ^ 2 / (N : ℝ) + (α - σ) * M / T)
      ring

end AnalyticNumberTheory.LargeSieve
