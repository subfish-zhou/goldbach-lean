import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21ActualShift
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21LogDerivativeFinal

noncomputable section
open Classical Complex Finset MeasureTheory Set Filter
open scoped BigOperators ArithmeticFunction Topology
namespace AnalyticNumberTheory.LargeSieve

theorem Eq21FiniteContour_rectangle_vertical_identity
    {f : ℂ → ℂ} {β α T : ℝ}
    (hβα : β ≤ α)
    (hT : 0 ≤ T)
    (hf : DifferentiableOn ℂ f {s : ℂ | β ≤ s.re ∧ s.re ≤ α ∧ |s.im| ≤ T}) :
    (∫ t in -T..T, chen1973VerticalSection f α t) -
        (∫ t in -T..T, chen1973VerticalSection f β t) =
      I * chen1973HorizontalSection f β α T := by
  have hrect : DifferentiableOn ℂ f
      (Set.uIcc (((β : ℂ) - T * I).re) (((α : ℂ) + T * I).re) ×ℂ
       Set.uIcc (((β : ℂ) - T * I).im) (((α : ℂ) + T * I).im)) := by
    apply hf.mono
    intro z hz
    have hzre : z.re ∈ Set.uIcc β α := by
      simpa [sub_re, mul_re, mul_zero, zero_mul] using hz.1
    have hzim : z.im ∈ Set.uIcc (-T) T := by
      simpa using hz.2
    rw [Set.uIcc_of_le hβα] at hzre
    rw [Set.uIcc_of_le (by linarith : -T ≤ T)] at hzim
    exact ⟨hzre.1, hzre.2, abs_le.mpr hzim⟩
  have hc := integral_boundary_rect_eq_zero_of_differentiableOn f
    ((β : ℂ) - T * I) ((α : ℂ) + T * I) hrect
  simp only [sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
    sub_zero, add_re, sub_im, mul_im, zero_add, mul_one, add_im,
    smul_eq_mul] at hc
  have hc' :
      ((∫ u in β..α, f (u + (-T) * I)) - ∫ u in β..α, f (u + T * I)) +
        I * (∫ t in -T..T, f (α + t * I)) -
        I * (∫ t in -T..T, f (β + t * I)) = 0 := by
    simpa only [zero_add, add_zero, ofReal_neg, sub_eq_add_neg] using hc
  have hc0 : chen1973HorizontalSection f β α T + I *
      ((∫ t in -T..T, chen1973VerticalSection f α t) -
        ∫ t in -T..T, chen1973VerticalSection f β t) = 0 := by
    unfold chen1973HorizontalSection chen1973VerticalSection
    linear_combination hc'
  have hc1 : I *
      ((∫ t in -T..T, chen1973VerticalSection f α t) -
        ∫ t in -T..T, chen1973VerticalSection f β t) =
      -chen1973HorizontalSection f β α T := by
    linear_combination hc0
  calc
    (∫ t in -T..T, chen1973VerticalSection f α t) -
          (∫ t in -T..T, chen1973VerticalSection f β t) =
        (-I) * (I * ((∫ t in -T..T, chen1973VerticalSection f α t) -
          ∫ t in -T..T, chen1973VerticalSection f β t)) := by
            rw [← mul_assoc, neg_mul, Complex.I_mul_I]
            ring
    _ = (-I) * (-chen1973HorizontalSection f β α T) := by rw [hc1]
    _ = I * chen1973HorizontalSection f β α T := by ring

theorem Eq21FiniteContour_mellinKernel_differentiableAt
    {x : ℕ} (hx : 3 ≤ x) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (chen1973MellinKernel (x : ℝ)) s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    simp at hs
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hscale : 0 < chen1973PerronScale (x : ℝ) := by
    unfold chen1973PerronScale
    exact Real.rpow_pos_of_pos hlog _
  have hfac : 1 + s / chen1973PerronScale (x : ℝ) ≠ 0 := by
    have hscale0 : chen1973PerronScale (x : ℝ) ≠ 0 := ne_of_gt hscale
    have hre : (1 + s / chen1973PerronScale (x : ℝ)).re =
        1 + s.re / chen1973PerronScale (x : ℝ) := by
      simp [div_re]
      field_simp [hscale0]
    have hpos : 0 < (1 + s / chen1973PerronScale (x : ℝ)).re := by
      rw [hre]
      positivity
    exact fun h => by rw [h] at hpos; simp at hpos
  unfold chen1973MellinKernel
  apply (differentiableAt_const (c := (1 : ℂ))).div
  · fun_prop
  · exact mul_ne_zero hs0 (pow_ne_zero _ hfac)


/-- Holomorphy of the actual term, using only nonvanishing on this rectangle. -/
theorem Eq21FiniteContour_term_differentiableOn
    {x d : ℕ} (hx : 3 ≤ x) (hd : 1 < d) (χ : PrimitiveCharacter d)
    {pp : ℕ × ℕ} (hp₁ : 0 < pp.1) (hp₂ : 0 < pp.2) {T : ℝ}
    (hzero : ∀ s : ℂ, chen1973Lemma6Eq21Sigma x ≤ s.re →
      s.re ≤ chen1973Lemma6Alpha x → |s.im| ≤ T →
      chen1973Lemma6PrimitiveLValue d s χ ≠ 0) :
    DifferentiableOn ℂ (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp)
      {s : ℂ | chen1973Lemma6Eq21Sigma x ≤ s.re ∧
        s.re ≤ chen1973Lemma6Alpha x ∧ |s.im| ≤ T} := by
  let _ : NeZero d := ⟨Nat.ne_zero_of_lt hd⟩
  have hχ : χ.1 ≠ 1 := primitiveCharacter_ne_one hd χ
  have hy : 0 < (x : ℝ) / ((pp.1 : ℝ) * pp.2) :=
    div_pos (by exact_mod_cast (show 0 < x by omega))
      (mul_pos (by exact_mod_cast hp₁) (by exact_mod_cast hp₂))
  intro s hs
  have hspos := (chen1973Lemma6_eq21_sigma_pos hx).trans_le hs.1
  have hLglobal : Differentiable ℂ χ.1.LFunction := χ.1.differentiable_LFunction hχ
  have hL0 : χ.1.LFunction s ≠ 0 := by
    simpa only [chen1973Lemma6PrimitiveLValue, dif_pos hd] using
      hzero s hs.1 hs.2.1 hs.2.2
  unfold chen1973Lemma6Eq21TermShiftIntegrand chen1973Lemma6Eq21ShiftIntegrand
  simp only [chen1973PrimitiveLDeriv, chen1973Lemma6PrimitiveLValue, dif_pos hd]
  exact ((differentiableAt_const _).mul
    (((differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast hy.ne'))).mul
      (Eq21FiniteContour_mellinKernel_differentiableAt hx hspos)).mul
      (hLglobal.deriv.differentiableAt.div (hLglobal s) hL0))).differentiableWithinAt

/-- Every finite vertical section is integrable before Cauchy is applied. -/
theorem Eq21FiniteContour_vertical_intervalIntegrable
    {f : ℂ → ℂ} {β α T v : ℝ} (hT : 0 ≤ T) (hv : v ∈ Icc β α)
    (hf : ContinuousOn f {s : ℂ | β ≤ s.re ∧ s.re ≤ α ∧ |s.im| ≤ T}) :
    IntervalIntegrable (chen1973VerticalSection f v) volume (-T) T := by
  apply ContinuousOn.intervalIntegrable
  apply hf.comp (by fun_prop : ContinuousOn (fun t : ℝ => (v : ℂ) + t * I) (uIcc (-T) T))
  intro t ht
  rw [uIcc_of_le (by linarith : -T ≤ T)] at ht
  simpa using (show β ≤ v ∧ v ≤ α ∧ |t| ≤ T from ⟨hv.1, hv.2, abs_le.mpr ht⟩)

/-- Every finite horizontal section is integrable on the genuine rectangle. -/
theorem Eq21FiniteContour_horizontal_intervalIntegrable
    {f : ℂ → ℂ} {β α T t : ℝ} (hβα : β ≤ α) (ht : |t| ≤ T)
    (hf : ContinuousOn f {s : ℂ | β ≤ s.re ∧ s.re ≤ α ∧ |s.im| ≤ T}) :
    IntervalIntegrable (fun v : ℝ => f ((v : ℂ) + t * I)) volume β α := by
  apply ContinuousOn.intervalIntegrable
  apply hf.comp (by fun_prop : ContinuousOn (fun v : ℝ => (v : ℂ) + t * I) (uIcc β α))
  intro v hv
  rw [uIcc_of_le hβα] at hv
  simpa using (show β ≤ v ∧ v ≤ α ∧ |t| ≤ T from ⟨hv.1, hv.2, ht⟩)

/-- Finite middle interval and two open tails, for an actually integrable function. -/
theorem Eq21FiniteContour_integral_split {f : ℝ → ℂ} (hf : Integrable f) (T : ℝ) :
    (∫ t : ℝ, f t) = (∫ t in -T..T, f t) +
      (∫ t in Iio (-T), f t) + ∫ t in Ioi T, f t := by
  have h₁ := intervalIntegral.integral_Iic_add_Ioi
    (hf.integrableOn : IntegrableOn f (Iic T)) (hf.integrableOn : IntegrableOn f (Ioi T))
  have h₂ := intervalIntegral.integral_Iio_sub_Iio'
    (hf.integrableOn : IntegrableOn f (Iio T)) (hf.integrableOn : IntegrableOn f (Iio (-T)))
  rw [integral_Iic_eq_integral_Iio] at h₁
  linear_combination -h₁ + h₂

/-- W2: exact signed decomposition of ActualPhi, with BOTH high tails on alpha.
No sigma high-tail object or full-height nonvanishing is assumed. -/
theorem Eq21FiniteContour_actualPhi_eq_truncated_with_alpha_tails
    {x d : ℕ} (hx : 3 ≤ x) (hd : 1 < d) (χ : PrimitiveCharacter d)
    {pp : ℕ × ℕ} (hp₁ : 0 < pp.1) (hp₂ : 0 < pp.2)
    {T : ℝ} (hT : 0 ≤ T)
    (hzero : ∀ s : ℂ, chen1973Lemma6Eq21Sigma x ≤ s.re →
      s.re ≤ chen1973Lemma6Alpha x → |s.im| ≤ T →
      chen1973Lemma6PrimitiveLValue d s χ ≠ 0) :
    chen1973Lemma6ActualPhi x d χ pp * χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) =
      -(((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ((∫ t in -T..T, chen1973VerticalSection
          (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp) (chen1973Lemma6Eq21Sigma x) t) +
        I * chen1973HorizontalSection (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp)
          (chen1973Lemma6Eq21Sigma x) (chen1973Lemma6Alpha x) T +
        (∫ t in Iio (-T), chen1973VerticalSection
          (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp) (chen1973Lemma6Alpha x) t) +
        ∫ t in Ioi T, chen1973VerticalSection
          (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp) (chen1973Lemma6Alpha x) t)) := by
  have hy : 0 < (x : ℝ) / ((pp.1 : ℝ) * pp.2) :=
    div_pos (by exact_mod_cast (show 0 < x by omega))
      (mul_pos (by exact_mod_cast hp₁) (by exact_mod_cast hp₂))
  have hα := chen1973Lemma6_eq21_alphaTerm_integrable hx hd χ hy
  have hf := Eq21FiniteContour_term_differentiableOn hx hd χ hp₁ hp₂ hzero
  have hσα := chen1973Lemma6_eq21_sigma_le_alpha hx
  have hσint := Eq21FiniteContour_vertical_intervalIntegrable hT
    ⟨le_rfl, hσα⟩ hf.continuousOn
  have hαint := Eq21FiniteContour_vertical_intervalIntegrable hT
    ⟨hσα, le_rfl⟩ hf.continuousOn
  have hbottom := Eq21FiniteContour_horizontal_intervalIntegrable hσα
    (show |-T| ≤ T by simp [abs_of_nonneg hT]) hf.continuousOn
  have htop := Eq21FiniteContour_horizontal_intervalIntegrable hσα
    (show |T| ≤ T by simp [abs_of_nonneg hT]) hf.continuousOn
  have hminus : IntegrableOn (chen1973VerticalSection
      (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp) (chen1973Lemma6Alpha x))
      (Iio (-T)) := hα.integrableOn
  have hplus : IntegrableOn (chen1973VerticalSection
      (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp) (chen1973Lemma6Alpha x))
      (Ioi T) := hα.integrableOn
  have hc := Eq21FiniteContour_rectangle_vertical_identity hσα hT hf
  rw [chen1973Lemma6_eq21_actualPhi_mul_eq_alphaTerm χ hd hx hp₁ hp₂,
    Eq21FiniteContour_integral_split hα T]
  congr 2
  linear_combination hc

end AnalyticNumberTheory.LargeSieve
