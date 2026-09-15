/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equations16And17
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
# Chen 1973, Lemma 6, equation (17): the `L' S` contour shift

This file isolates the honest complex-analytic deformation used in (17).  The
integrand is the actual product
`L'(s,χ) S(H,s,χ) y^s K_x(s)`, with `K_x` Chen's rational Mellin kernel.
The proof never divides by `L` on the beta line.
-/

noncomputable section

open Classical Complex Finset MeasureTheory Set Filter
open scoped BigOperators ArithmeticFunction Topology

namespace AnalyticNumberTheory.LargeSieve

/-- The actual holomorphic factor shifted in the second term of (16). -/
def chen1973Lemma6Eq17ShiftIntegrand {d : ℕ} [NeZero d]
    (x H : ℕ) (y : ℝ) (χ : PrimitiveCharacter d) (s : ℂ) : ℂ :=
  deriv χ.1.LFunction s * chen1973Lemma6MobiusPartialSum H s χ *
    ((y : ℂ) ^ s * chen1973MellinKernel (x : ℝ) s)

private theorem eq17_beta_pos {x : ℕ} (hx : 1 < x) :
    0 < chen1973Lemma6Beta x := by
  unfold chen1973Lemma6Beta
  have hlog : 0 < Real.log x := Real.log_pos (by exact_mod_cast hx)
  positivity

private theorem eq17_scale_pos {x : ℕ} (hx : 1 < x) :
    0 < chen1973PerronScale (x : ℝ) := by
  unfold chen1973PerronScale
  exact Real.rpow_pos_of_pos (Real.log_pos (by exact_mod_cast hx)) _

private theorem differentiableAt_mobiusPartialSum {d H : ℕ} [NeZero d]
    (χ : PrimitiveCharacter d) (s : ℂ) :
    DifferentiableAt ℂ (fun z => chen1973Lemma6MobiusPartialSum H z χ) s := by
  unfold chen1973Lemma6MobiusPartialSum
  apply DifferentiableAt.fun_sum
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n))
  have hpow : (n : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hn0)
  have hnum : DifferentiableAt ℂ (fun _ : ℂ =>
      (((ArithmeticFunction.moebius n : ℤ) : ℂ)) * χ.1 (n : ZMod d)) s :=
    differentiableAt_const _
  exact hnum.div (differentiableAt_id.const_cpow (Or.inl hn0)) hpow

private theorem differentiableAt_mellinKernel_of_pos_re
    {x : ℕ} (hx : 1 < x) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (chen1973MellinKernel (x : ℝ)) s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    simp at hs
  have ha : 0 < chen1973PerronScale (x : ℝ) := eq17_scale_pos hx
  have hfac : 1 + s / chen1973PerronScale (x : ℝ) ≠ 0 := by
    have ha0 : chen1973PerronScale (x : ℝ) ≠ 0 := ne_of_gt ha
    have hreal : (1 + s / chen1973PerronScale (x : ℝ)).re =
        1 + s.re / chen1973PerronScale (x : ℝ) := by
      simp [div_re]
      field_simp [ha0]
    have hpos : 0 < (1 + s / chen1973PerronScale (x : ℝ)).re := by
      rw [hreal]
      positivity
    exact fun h => by rw [h] at hpos; simp at hpos
  unfold chen1973MellinKernel
  apply (differentiableAt_const (c := (1 : ℂ))).div
  · fun_prop
  · exact mul_ne_zero hs0 (pow_ne_zero _ hfac)

/-- For a nonprincipal primitive character, the actual `L' S` integrand is
holomorphic throughout Chen's closed strip.  Primitivity is part of the type;
nonprincipality is used only to make `L` entire.  No beta-line nonvanishing
assumption occurs. -/
theorem differentiableOn_chen1973Lemma6Eq17ShiftIntegrand_strip
    {d x H : ℕ} [NeZero d] (χ : PrimitiveCharacter d) (hχ : χ.1 ≠ 1)
    (hx : 1 < x) {y : ℝ} (hy : 0 < y) :
    DifferentiableOn ℂ (chen1973Lemma6Eq17ShiftIntegrand x H y χ)
      {s : ℂ | chen1973Lemma6Beta x ≤ s.re ∧ s.re ≤ chen1973Lemma6Alpha x} := by
  intro s hs
  have hsre : 0 < s.re := (eq17_beta_pos hx).trans_le hs.1
  unfold chen1973Lemma6Eq17ShiftIntegrand
  exact (((χ.1.differentiable_LFunction hχ).deriv.differentiableAt.mul
    (differentiableAt_mobiusPartialSum χ s)).mul
      ((differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast hy.ne'))).mul
        (differentiableAt_mellinKernel_of_pos_re hx hsre))).differentiableWithinAt

/-- A vertical section of a complex integrand. -/
def chen1973VerticalSection (f : ℂ → ℂ) (σ t : ℝ) : ℂ :=
  f (σ + t * I)

/-- The two horizontal sides of the rectangle, oriented from beta to alpha. -/
def chen1973HorizontalSection (f : ℂ → ℂ) (β α T : ℝ) : ℂ :=
  (∫ u in β..α, f (u + (-T) * I)) - ∫ u in β..α, f (u + T * I)

/-- Cauchy--Goursat on the finite rectangle, rewritten as a vertical-line
identity. -/
theorem chen1973_finite_rectangle_vertical_identity
    {f : ℂ → ℂ} {β α T : ℝ}
    (hβα : β ≤ α)
    (hf : DifferentiableOn ℂ f {s : ℂ | β ≤ s.re ∧ s.re ≤ α}) :
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
    rwa [Set.uIcc_of_le hβα] at hzre
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
  apply mul_left_cancel₀ Complex.I_ne_zero
  rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  exact eq_neg_of_add_eq_zero_right hc0

private theorem tendsto_norm_le_inv_one_add_sq
    {g : ℝ → ℂ} {C : ℝ} (_hC : 0 ≤ C)
    (hg : ∀ T : ℝ, 0 ≤ T → ‖g T‖ ≤ C / (1 + T ^ 2)) :
    Tendsto g atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun T => norm_nonneg (g T))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact hg T hT
  · have hden : Tendsto (fun T : ℝ => 1 + T ^ 2) atTop atTop := by
      exact tendsto_const_nhds.add_atTop (tendsto_pow_atTop (by norm_num))
    exact tendsto_const_nhds.div_atTop hden

/-- Full Bochner contour shift.  The only quantitative hypotheses are the two
explicit horizontal-side estimates produced from Chen's rational kernel.  They
are strictly weaker than the desired integral equality and expose the exact
remaining growth estimate for `L' S`; no conclusion-equivalent premise is
accepted. -/
theorem chen1973_full_vertical_integral_shift
    {f : ℂ → ℂ} {β α C : ℝ} (hβα : β ≤ α) (hC : 0 ≤ C)
    (hhol : DifferentiableOn ℂ f {s : ℂ | β ≤ s.re ∧ s.re ≤ α})
    (hβint : Integrable (chen1973VerticalSection f β))
    (hαint : Integrable (chen1973VerticalSection f α))
    (hhoriz : ∀ T : ℝ, 0 ≤ T →
      ‖chen1973HorizontalSection f β α T‖ ≤ C / (1 + T ^ 2)) :
    (∫ t : ℝ, chen1973VerticalSection f α t) =
      ∫ t : ℝ, chen1973VerticalSection f β t := by
  let Vα : ℝ → ℂ := fun T => ∫ t in -T..T, chen1973VerticalSection f α t
  let Vβ : ℝ → ℂ := fun T => ∫ t in -T..T, chen1973VerticalSection f β t
  let Horiz : ℝ → ℂ := fun T => chen1973HorizontalSection f β α T
  have hrect (T : ℝ) : Vα T - Vβ T = I * Horiz T :=
    chen1973_finite_rectangle_vertical_identity hβα hhol
  have hVα : Tendsto Vα atTop (𝓝 (∫ t : ℝ, chen1973VerticalSection f α t)) := by
    simpa [Vα] using intervalIntegral_tendsto_integral hαint
      tendsto_neg_atTop_atBot tendsto_id
  have hVβ : Tendsto Vβ atTop (𝓝 (∫ t : ℝ, chen1973VerticalSection f β t)) := by
    simpa [Vβ] using intervalIntegral_tendsto_integral hβint
      tendsto_neg_atTop_atBot tendsto_id
  have hH : Tendsto Horiz atTop (𝓝 0) :=
    tendsto_norm_le_inv_one_add_sq hC (by simpa [Horiz] using hhoriz)
  have hdiff : Tendsto (fun T => Vα T - Vβ T) atTop (𝓝 0) := by
    have hIH : Tendsto (fun T => I * Horiz T) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hH)
    apply hIH.congr'
    exact Eventually.of_forall fun T => (hrect T).symm
  have hlim := hVα.sub hVβ
  have hz : (∫ t : ℝ, chen1973VerticalSection f α t) -
      (∫ t : ℝ, chen1973VerticalSection f β t) = 0 :=
    tendsto_nhds_unique hlim hdiff
  exact sub_eq_zero.mp hz

/-- Equation-(17)'s actual `L' S` contour shift, from Chen's alpha line to his
beta line.  Holomorphy is discharged internally from nonprincipality; callers
supply only Bochner integrability and the horizontal kernel-decay estimate. -/
theorem chen1973Lemma6_eq17_LDerivS_contour_shift
    {d x H : ℕ} [NeZero d] (χ : PrimitiveCharacter d) (hχ : χ.1 ≠ 1)
    (hx : 1 < x) {y C : ℝ} (hy : 0 < y) (hC : 0 ≤ C)
    (hβint : Integrable (chen1973VerticalSection
      (chen1973Lemma6Eq17ShiftIntegrand x H y χ) (chen1973Lemma6Beta x)))
    (hαint : Integrable (chen1973VerticalSection
      (chen1973Lemma6Eq17ShiftIntegrand x H y χ) (chen1973Lemma6Alpha x)))
    (hhoriz : ∀ T : ℝ, 0 ≤ T →
      ‖chen1973HorizontalSection (chen1973Lemma6Eq17ShiftIntegrand x H y χ)
        (chen1973Lemma6Beta x) (chen1973Lemma6Alpha x) T‖ ≤
          C / (1 + T ^ 2)) :
    (∫ t : ℝ, chen1973VerticalSection
      (chen1973Lemma6Eq17ShiftIntegrand x H y χ) (chen1973Lemma6Alpha x) t) =
    ∫ t : ℝ, chen1973VerticalSection
      (chen1973Lemma6Eq17ShiftIntegrand x H y χ) (chen1973Lemma6Beta x) t := by
  refine chen1973_full_vertical_integral_shift ?_ hC
    (differentiableOn_chen1973Lemma6Eq17ShiftIntegrand_strip χ hχ hx hy)
    hβint hαint hhoriz
  unfold chen1973Lemma6Beta chen1973Lemma6Alpha
  linarith

end AnalyticNumberTheory.LargeSieve
