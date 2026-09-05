/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation17ContourShift
import MathlibNt.AnalyticNumberTheory.LargeSieve.PrimitiveCharacterElementaryPeriodBound
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Chen 1973, Lemma 6, equation (21): zero-free-to-contour bridge

The corrected transcription of the printed exponent is `1/300`. The left-line
comparison is `1 / sqrt (log x) ≤ c / d^(1/300)`. For fixed positive `c` and
`d ≤ (log x)^100` this is eventually true; the former `3/100` obstruction
was a transcription error, not a defect of the printed conductor scale.
-/

noncomputable section

open Classical Complex Finset MeasureTheory Set Filter
open scoped BigOperators ArithmeticFunction Topology

namespace AnalyticNumberTheory.LargeSieve

/-- The exact comparison putting the line of (21) inside the printed
`d^(-1/300)` strip. A sufficiently-large-x theorem can discharge this
comparison for each fixed positive `c`; zero-freeness is a separate input. -/
def Chen1973Lemma6Eq21ZeroFreeContourBridge (x L : ℕ) (c : ℝ) : Prop :=
  ∀ d ∈ chen1973Lemma6ConductorBlock x L 0,
    1 / Real.sqrt (Real.log x) ≤ c / (d : ℝ) ^ ((1 : ℝ) / 300)

/-- The bridge comparison is exactly the inclusion of the printed left line in
the printed zero-free half-plane. -/
theorem chen1973Lemma6_eq21_sigma_ge_zeroFreeBoundary
    {x L d : ℕ} {c : ℝ}
    (hbridge : Chen1973Lemma6Eq21ZeroFreeContourBridge x L c)
    (hd : d ∈ chen1973Lemma6ConductorBlock x L 0) :
    1 - c / (d : ℝ) ^ ((1 : ℝ) / 300) ≤ chen1973Lemma6Eq21Sigma x := by
  unfold Chen1973Lemma6Eq21ZeroFreeContourBridge at hbridge
  unfold chen1973Lemma6Eq21Sigma
  linarith [hbridge d hd]

/-- Consequently every point on the equation-(21) line is nonzero. -/
theorem chen1973Lemma6_eq21_leftLine_nonvanishing
    {x L d : ℕ} {c : ℝ}
    (hzero : Chen1973Lemma6Eq21ZeroFreeInput x L c)
    (hbridge : Chen1973Lemma6Eq21ZeroFreeContourBridge x L c)
    (hd : d ∈ chen1973Lemma6ConductorBlock x L 0)
    (χ : PrimitiveCharacter d) (t : ℝ) :
    chen1973Lemma6PrimitiveLValue d (chen1973Lemma6Eq21Line x t) χ ≠ 0 := by
  exact hzero.2 d hd χ _ (by
    rw [chen1973Lemma6_eq21_line_re]
    exact chen1973Lemma6_eq21_sigma_ge_zeroFreeBoundary hbridge hd)

/-- Nonvanishing on the whole closed vertical strip from the printed left line
to the source Bromwich line `α = 1 + 1 / log x`. -/
theorem chen1973Lemma6_eq21_rectangle_nonvanishing
    {x L d : ℕ} {c : ℝ}
    (hzero : Chen1973Lemma6Eq21ZeroFreeInput x L c)
    (hbridge : Chen1973Lemma6Eq21ZeroFreeContourBridge x L c)
    (hd : d ∈ chen1973Lemma6ConductorBlock x L 0)
    (χ : PrimitiveCharacter d) {s : ℂ}
    (hs : chen1973Lemma6Eq21Sigma x ≤ s.re ∧
      s.re ≤ chen1973Lemma6Alpha x) :
    chen1973Lemma6PrimitiveLValue d s χ ≠ 0 := by
  apply hzero.2 d hd χ s
  exact (chen1973Lemma6_eq21_sigma_ge_zeroFreeBoundary hbridge hd).trans hs.1

/-- For the literal source range `x ≥ 3`, the printed left edge remains in
the open right half-plane. -/
theorem chen1973Lemma6_eq21_sigma_pos {x : ℕ} (hx : 3 ≤ x) :
    0 < chen1973Lemma6Eq21Sigma x := by
  have hxR : Real.exp 1 < (x : ℝ) :=
    Real.exp_one_lt_three.trans_le (by exact_mod_cast hx)
  have hlog : 1 < Real.log (x : ℝ) :=
    (Real.lt_log_iff_exp_lt (by exact_mod_cast (show 0 < x by omega))).2 hxR
  have hsqrt : 1 < Real.sqrt (Real.log (x : ℝ)) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
    exact hlog
  have hinv : 1 / Real.sqrt (Real.log (x : ℝ)) < 1 := by
    rw [div_lt_iff₀ (by positivity : 0 < Real.sqrt (Real.log (x : ℝ)))]
    simpa using hsqrt
  unfold chen1973Lemma6Eq21Sigma
  linarith

/-- The left edge never exceeds the right edge `1`. -/
theorem chen1973Lemma6_eq21_sigma_le_one (x : ℕ) :
    chen1973Lemma6Eq21Sigma x ≤ 1 := by
  unfold chen1973Lemma6Eq21Sigma
  exact sub_le_self _ (by positivity)

/-- The printed left edge lies to the left of the source Bromwich line
`α = 1 + 1 / log x`.  The weaker comparison with `1` remains available as a
separate elementary lemma. -/
theorem chen1973Lemma6_eq21_sigma_le_alpha
    {x : ℕ} (hx : 3 ≤ x) :
    chen1973Lemma6Eq21Sigma x ≤ chen1973Lemma6Alpha x := by
  exact (chen1973Lemma6_eq21_sigma_le_one x).trans (by
    unfold chen1973Lemma6Alpha
    have hlog : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < x by omega))
    linarith [one_div_pos.mpr hlog])

/-- The literal logarithmic-derivative integrand shifted in equation (21), with
`y = x/(p₁p₂)` supplied separately so positivity is visible to the analytic
API. -/
def chen1973Lemma6Eq21ShiftIntegrand
    (x d : ℕ) (χ : PrimitiveCharacter d) (y : ℝ) (s : ℂ) : ℂ :=
  ((y : ℂ) ^ s * chen1973MellinKernel (x : ℝ) s) *
    (chen1973PrimitiveLDeriv d s χ / chen1973Lemma6PrimitiveLValue d s χ)

private theorem eq21_mellinKernel_differentiableAt
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

/-- Under the explicit bridge, the actual logarithmic-derivative integrand is
holomorphic on the full closed strip between the equation-(21) line and the
source Bromwich line `α = 1 + 1 / log x`.
No zero-free statement stronger than the printed input is assumed. -/
theorem differentiableOn_chen1973Lemma6Eq21ShiftIntegrand_strip
    {x L B k m l₂ d : ℕ} {c y : ℝ}
    (P : Chen1973Lemma6Eq21SourceParameters x L B k m l₂)
    (hzero : Chen1973Lemma6Eq21ZeroFreeInput x L c)
    (hbridge : Chen1973Lemma6Eq21ZeroFreeContourBridge x L c)
    (hd : d ∈ chen1973Lemma6ConductorBlock x L 0)
    (χ : PrimitiveCharacter d) (hy : 0 < y) :
    DifferentiableOn ℂ (chen1973Lemma6Eq21ShiftIntegrand x d χ y)
      {s : ℂ | chen1973Lemma6Eq21Sigma x ≤ s.re ∧
        s.re ≤ chen1973Lemma6Alpha x} := by
  let _ : NeZero d := ⟨Nat.ne_zero_of_lt (chen1973Lemma6_eq21_one_lt_conductor hd)⟩
  have hd1 := chen1973Lemma6_eq21_one_lt_conductor hd
  have hχ : χ.1 ≠ 1 := primitiveCharacter_ne_one hd1 χ
  intro s hs
  have hspos : 0 < s.re := (chen1973Lemma6_eq21_sigma_pos P.hx).trans_le hs.1
  have hLglobal : Differentiable ℂ χ.1.LFunction := χ.1.differentiable_LFunction hχ
  have hL : DifferentiableAt ℂ χ.1.LFunction s := hLglobal s
  have hL0 : χ.1.LFunction s ≠ 0 := by
    simpa only [chen1973Lemma6PrimitiveLValue, dif_pos hd1] using
      chen1973Lemma6_eq21_rectangle_nonvanishing hzero hbridge hd χ hs
  unfold chen1973Lemma6Eq21ShiftIntegrand
  simp only [chen1973PrimitiveLDeriv, chen1973Lemma6PrimitiveLValue, dif_pos hd1]
  exact (((differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast hy.ne'))).mul
    (eq21_mellinKernel_differentiableAt P.hx hspos)).mul
      (hLglobal.deriv.differentiableAt.div hL hL0)).differentiableWithinAt

/-- The finite equation-(21) contour shift on the actual rectangle.  This is a
Cauchy--Goursat equality, not an assumed contour-majorization inequality. -/
theorem chen1973Lemma6_eq21_finite_contour_shift
    {x L B k m l₂ d : ℕ} {c y T : ℝ}
    (P : Chen1973Lemma6Eq21SourceParameters x L B k m l₂)
    (hzero : Chen1973Lemma6Eq21ZeroFreeInput x L c)
    (hbridge : Chen1973Lemma6Eq21ZeroFreeContourBridge x L c)
    (hd : d ∈ chen1973Lemma6ConductorBlock x L 0)
    (χ : PrimitiveCharacter d) (hy : 0 < y) :
    (∫ t in -T..T, chen1973VerticalSection
        (chen1973Lemma6Eq21ShiftIntegrand x d χ y) (chen1973Lemma6Alpha x) t) -
      (∫ t in -T..T, chen1973VerticalSection
        (chen1973Lemma6Eq21ShiftIntegrand x d χ y)
          (chen1973Lemma6Eq21Sigma x) t) =
      I * chen1973HorizontalSection
        (chen1973Lemma6Eq21ShiftIntegrand x d χ y)
          (chen1973Lemma6Eq21Sigma x) (chen1973Lemma6Alpha x) T := by
  apply chen1973_finite_rectangle_vertical_identity
    (f := chen1973Lemma6Eq21ShiftIntegrand x d χ y)
    (β := chen1973Lemma6Eq21Sigma x) (α := chen1973Lemma6Alpha x) (T := T)
  · exact chen1973Lemma6_eq21_sigma_le_alpha P.hx
  · exact differentiableOn_chen1973Lemma6Eq21ShiftIntegrand_strip
      P hzero hbridge hd χ hy

/-- Passing to infinite vertical lines using the existing contour
infrastructure.  Integrability of the two vertical sections and the explicit
horizontal-edge decay are the precise remaining analytic limit inputs. -/
theorem chen1973Lemma6_eq21_full_contour_shift
    {x L B k m l₂ d : ℕ} {c y C : ℝ}
    (P : Chen1973Lemma6Eq21SourceParameters x L B k m l₂)
    (hzero : Chen1973Lemma6Eq21ZeroFreeInput x L c)
    (hbridge : Chen1973Lemma6Eq21ZeroFreeContourBridge x L c)
    (hd : d ∈ chen1973Lemma6ConductorBlock x L 0)
    (χ : PrimitiveCharacter d) (hy : 0 < y) (hC : 0 ≤ C)
    (hleft : Integrable (chen1973VerticalSection
      (chen1973Lemma6Eq21ShiftIntegrand x d χ y) (chen1973Lemma6Eq21Sigma x)))
    (hright : Integrable (chen1973VerticalSection
      (chen1973Lemma6Eq21ShiftIntegrand x d χ y) (chen1973Lemma6Alpha x)))
    (hhoriz : ∀ T : ℝ, 0 ≤ T →
      ‖chen1973HorizontalSection (chen1973Lemma6Eq21ShiftIntegrand x d χ y)
        (chen1973Lemma6Eq21Sigma x) (chen1973Lemma6Alpha x) T‖ ≤ C / (1 + T ^ 2)) :
    (∫ t : ℝ, chen1973VerticalSection
      (chen1973Lemma6Eq21ShiftIntegrand x d χ y) (chen1973Lemma6Alpha x) t) =
      ∫ t : ℝ, chen1973VerticalSection
        (chen1973Lemma6Eq21ShiftIntegrand x d χ y)
          (chen1973Lemma6Eq21Sigma x) t := by
  apply chen1973_full_vertical_integral_shift
    (f := chen1973Lemma6Eq21ShiftIntegrand x d χ y)
    (β := chen1973Lemma6Eq21Sigma x) (α := chen1973Lemma6Alpha x) (C := C)
  · exact chen1973Lemma6_eq21_sigma_le_alpha P.hx
  · exact hC
  · exact differentiableOn_chen1973Lemma6Eq21ShiftIntegrand_strip
      P hzero hbridge hd χ hy
  · exact hleft
  · exact hright
  · exact hhoriz

/-- The literal term integrand inside `chen1973Lemma6Eq21VerticalIntegral`.
The finite character value is retained, rather than factored out before the
contour deformation. -/
def chen1973Lemma6Eq21TermShiftIntegrand
    (x d : ℕ) (χ : PrimitiveCharacter d) (pp : ℕ × ℕ) (s : ℂ) : ℂ :=
  χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) *
    chen1973Lemma6Eq21ShiftIntegrand x d χ
      ((x : ℝ) / ((pp.1 : ℝ) * pp.2)) s

/-- The source vertical integral is exactly the left-line integral of the
literal shifted term. -/
theorem chen1973Lemma6_eq21_verticalIntegral_eq_termShift
    (x d : ℕ) (χ : PrimitiveCharacter d) (pp : ℕ × ℕ) :
    chen1973Lemma6Eq21VerticalIntegral x d χ pp =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, chen1973VerticalSection
          (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp)
          (chen1973Lemma6Eq21Sigma x) t := by
  unfold chen1973Lemma6Eq21VerticalIntegral chen1973Lemma6Eq21TermShiftIntegrand
    chen1973Lemma6Eq21ShiftIntegrand chen1973VerticalSection
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  simp only [chen1973Lemma6Eq21Line, ofReal_div, ofReal_mul, Nat.cast_mul]
  ac_rfl

/-- The literal term is holomorphic on the same strip. -/
theorem differentiableOn_chen1973Lemma6Eq21TermShiftIntegrand_strip
    {x L B k m l₂ d : ℕ} {c : ℝ}
    (P : Chen1973Lemma6Eq21SourceParameters x L B k m l₂)
    (hzero : Chen1973Lemma6Eq21ZeroFreeInput x L c)
    (hbridge : Chen1973Lemma6Eq21ZeroFreeContourBridge x L c)
    (hd : d ∈ chen1973Lemma6ConductorBlock x L 0)
    (χ : PrimitiveCharacter d) {pp : ℕ × ℕ}
    (hp₁ : 0 < pp.1) (hp₂ : 0 < pp.2) :
    DifferentiableOn ℂ (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp)
      {s : ℂ | chen1973Lemma6Eq21Sigma x ≤ s.re ∧
        s.re ≤ chen1973Lemma6Alpha x} := by
  unfold chen1973Lemma6Eq21TermShiftIntegrand
  have hy : 0 < (x : ℝ) / ((pp.1 : ℝ) * pp.2) := by
    have hx0 : 0 < x := lt_of_lt_of_le (by omega) P.hx
    exact div_pos (by exact_mod_cast hx0)
      (mul_pos (by exact_mod_cast hp₁) (by exact_mod_cast hp₂))
  exact (differentiableOn_const
    (c := χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d))).mul
      (differentiableOn_chen1973Lemma6Eq21ShiftIntegrand_strip
        P hzero hbridge hd χ hy)

/-- Actual finite contour-shift equality for one literal equation-(21) term. -/
theorem chen1973Lemma6_eq21_term_finite_contour_shift
    {x L B k m l₂ d : ℕ} {c T : ℝ}
    (P : Chen1973Lemma6Eq21SourceParameters x L B k m l₂)
    (hzero : Chen1973Lemma6Eq21ZeroFreeInput x L c)
    (hbridge : Chen1973Lemma6Eq21ZeroFreeContourBridge x L c)
    (hd : d ∈ chen1973Lemma6ConductorBlock x L 0)
    (χ : PrimitiveCharacter d) {pp : ℕ × ℕ}
    (hp₁ : 0 < pp.1) (hp₂ : 0 < pp.2) :
    (∫ t in -T..T, chen1973VerticalSection
        (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp) (chen1973Lemma6Alpha x) t) -
      (∫ t in -T..T, chen1973VerticalSection
        (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp)
          (chen1973Lemma6Eq21Sigma x) t) =
      I * chen1973HorizontalSection
        (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp)
          (chen1973Lemma6Eq21Sigma x) (chen1973Lemma6Alpha x) T := by
  apply chen1973_finite_rectangle_vertical_identity
    (f := chen1973Lemma6Eq21TermShiftIntegrand x d χ pp)
    (β := chen1973Lemma6Eq21Sigma x) (α := chen1973Lemma6Alpha x) (T := T)
  · exact chen1973Lemma6_eq21_sigma_le_alpha P.hx
  · exact differentiableOn_chen1973Lemma6Eq21TermShiftIntegrand_strip
      P hzero hbridge hd χ hp₁ hp₂

/-- Full-line contour shift for the literal term.  The horizontal limit is
paid through the existing `C/(1+T²)` infrastructure. -/
theorem chen1973Lemma6_eq21_term_full_contour_shift
    {x L B k m l₂ d : ℕ} {c C : ℝ}
    (P : Chen1973Lemma6Eq21SourceParameters x L B k m l₂)
    (hzero : Chen1973Lemma6Eq21ZeroFreeInput x L c)
    (hbridge : Chen1973Lemma6Eq21ZeroFreeContourBridge x L c)
    (hd : d ∈ chen1973Lemma6ConductorBlock x L 0)
    (χ : PrimitiveCharacter d) {pp : ℕ × ℕ}
    (hp₁ : 0 < pp.1) (hp₂ : 0 < pp.2) (hC : 0 ≤ C)
    (hleft : Integrable (chen1973VerticalSection
      (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp)
        (chen1973Lemma6Eq21Sigma x)))
    (hright : Integrable (chen1973VerticalSection
      (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp) (chen1973Lemma6Alpha x)))
    (hhoriz : ∀ T : ℝ, 0 ≤ T →
      ‖chen1973HorizontalSection
        (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp)
        (chen1973Lemma6Eq21Sigma x) (chen1973Lemma6Alpha x) T‖ ≤ C / (1 + T ^ 2)) :
    (∫ t : ℝ, chen1973VerticalSection
      (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp) (chen1973Lemma6Alpha x) t) =
      ∫ t : ℝ, chen1973VerticalSection
        (chen1973Lemma6Eq21TermShiftIntegrand x d χ pp)
          (chen1973Lemma6Eq21Sigma x) t := by
  apply chen1973_full_vertical_integral_shift
    (f := chen1973Lemma6Eq21TermShiftIntegrand x d χ pp)
    (β := chen1973Lemma6Eq21Sigma x) (α := chen1973Lemma6Alpha x) (C := C)
  · exact chen1973Lemma6_eq21_sigma_le_alpha P.hx
  · exact hC
  · exact differentiableOn_chen1973Lemma6Eq21TermShiftIntegrand_strip
      P hzero hbridge hd χ hp₁ hp₂
  · exact hleft
  · exact hright
  · exact hhoriz

end AnalyticNumberTheory.LargeSieve
