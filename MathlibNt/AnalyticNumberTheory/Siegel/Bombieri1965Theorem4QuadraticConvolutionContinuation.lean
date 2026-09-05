import MathlibNt.AnalyticNumberTheory.Siegel.Bombieri1965Theorem4QuadraticConvolutionAsymptotic
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticValueAtOnePositive
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Mellin continuation of the quadratic convolution

This is a modern analytic argument using the proved square-root error in the
summatory convolution, rather than a transcription of Bombieri's proof.
-/

open Complex Finset Filter MeasureTheory Set Asymptotics
open scoped Topology

namespace AnalyticNumberTheory.LargeSieve.Bombieri1965Theorem4

open DirichletCharacter

variable {q : ℕ} [NeZero q]

/-- The actual summatory error, with the actual value of the Dirichlet L-function. -/
noncomputable def quadraticConvolutionError (χ : DirichletCharacter ℂ q) (t : ℝ) : ℝ :=
  quadraticSiegelConvolutionSummatory χ ⌊t⌋₊ - t * (χ.LFunction 1).re

/-- The integrand in the continued convolution formula. -/
noncomputable def quadraticConvolutionErrorKernel
    (χ : DirichletCharacter ℂ q) (s : ℂ) (t : ℝ) : ℂ :=
  (quadraticConvolutionError χ t : ℂ) * (t : ℂ) ^ (-(s + 1))

/-- The Mellin error integral, with lower endpoint one. -/
noncomputable def quadraticConvolutionErrorIntegral
    (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∫ t in Ioi (1 : ℝ), quadraticConvolutionErrorKernel χ s t

/-- Cutoff used only to apply the ordinary Mellin transform API. -/
noncomputable def quadraticConvolutionCutoffError
    (χ : DirichletCharacter ℂ q) : ℝ → ℂ :=
  (Ioi (1 : ℝ)).indicator fun t => (quadraticConvolutionError χ t : ℂ)

theorem measurable_quadraticConvolutionError (χ : DirichletCharacter ℂ q) :
    Measurable (quadraticConvolutionError χ) := by
  exact ((StronglyMeasurable.of_discrete (f := quadraticSiegelConvolutionSummatory χ)).measurable.comp
    measurable_id.nat_floor).sub (measurable_id.mul_const _)

theorem measurable_quadraticConvolutionCutoffError (χ : DirichletCharacter ℂ q) :
    Measurable (quadraticConvolutionCutoffError χ) :=
  (Complex.measurable_ofReal.comp (measurable_quadraticConvolutionError χ)).indicator
    measurableSet_Ioi

theorem IsPrimitive.abs_quadraticConvolutionError_le
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {t : ℝ} (ht : 1 ≤ t) :
    |quadraticConvolutionError χ t| ≤ 81 * q * Real.sqrt t :=
  IsPrimitive.abs_quadratic_convolution_floor_sub_LValue_main_le χ hprim hχ ht

theorem IsPrimitive.norm_quadraticConvolutionCutoffError_le
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (t : ℝ) :
    ‖quadraticConvolutionCutoffError χ t‖ ≤ 81 * q * Real.sqrt t := by
  by_cases ht : 1 < t
  · simpa [quadraticConvolutionCutoffError, ht] using
      IsPrimitive.abs_quadraticConvolutionError_le χ hprim hχ ht.le
  · simp [quadraticConvolutionCutoffError, ht]
    positivity

theorem IsPrimitive.locallyIntegrable_quadraticConvolutionCutoffError
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    LocallyIntegrable (quadraticConvolutionCutoffError χ) := by
  refine (show Continuous (fun t : ℝ => 81 * (q : ℝ) * Real.sqrt t) by
    fun_prop).locallyIntegrable.mono
      (measurable_quadraticConvolutionCutoffError χ).aestronglyMeasurable ?_
  filter_upwards [] with t
  exact (IsPrimitive.norm_quadraticConvolutionCutoffError_le χ hprim hχ t).trans
    (Real.le_norm_self _)

theorem IsPrimitive.quadraticConvolutionCutoffError_isBigO_atTop
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    quadraticConvolutionCutoffError χ =O[atTop] (fun t : ℝ => t ^ (1 / 2 : ℝ)) := by
  refine isBigO_iff.mpr ⟨81 * q, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simpa [Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht _)]
    using IsPrimitive.norm_quadraticConvolutionCutoffError_le χ hprim hχ t

theorem quadraticConvolutionCutoffError_isBigO_zero
    (χ : DirichletCharacter ℂ q) (b : ℝ) :
    quadraticConvolutionCutoffError χ =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ b) := by
  refine isBigO_iff.mpr ⟨0, ?_⟩
  filter_upwards [((eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
    nhdsWithin_le_nhds)] with t ht
  simp [quadraticConvolutionCutoffError, not_lt.mpr ht.le]

private theorem cutoff_mellin_kernel (χ : DirichletCharacter ℂ q) (s : ℂ) :
    (fun t : ℝ => (t : ℂ) ^ (-s - 1) • quadraticConvolutionCutoffError χ t) =
      (Ioi (1 : ℝ)).indicator (quadraticConvolutionErrorKernel χ s) := by
  funext t
  by_cases ht : 1 < t
  · simp [quadraticConvolutionCutoffError, quadraticConvolutionErrorKernel, ht,
      smul_eq_mul, sub_eq_add_neg, mul_comm, add_comm]
  · simp [quadraticConvolutionCutoffError, ht]

theorem mellin_quadraticConvolutionCutoffError
    (χ : DirichletCharacter ℂ q) (s : ℂ) :
    mellin (quadraticConvolutionCutoffError χ) (-s) =
      quadraticConvolutionErrorIntegral χ s := by
  rw [mellin, cutoff_mellin_kernel, setIntegral_indicator measurableSet_Ioi]
  simp only [Ioi_inter_Ioi, max_eq_right (show (0 : ℝ) ≤ 1 by norm_num)]
  rfl

theorem IsPrimitive.mellinConvergent_quadraticConvolutionCutoffError
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    MellinConvergent (quadraticConvolutionCutoffError χ) (-s) := by
  apply mellinConvergent_of_isBigO_rpow
    ((IsPrimitive.locallyIntegrable_quadraticConvolutionCutoffError χ hprim hχ).locallyIntegrableOn _)
    (a := -(1 / 2)) (b := -s.re - 1)
  · simpa using IsPrimitive.quadraticConvolutionCutoffError_isBigO_atTop χ hprim hχ
  · simp only [neg_re]; linarith
  · exact quadraticConvolutionCutoffError_isBigO_zero χ _
  · simp only [neg_re]; linarith

/-- Absolute convergence of the genuine summatory-error integral in `Re s > 1/2`. -/
theorem IsPrimitive.integrableOn_quadraticConvolutionErrorKernel
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    IntegrableOn (quadraticConvolutionErrorKernel χ s) (Ioi (1 : ℝ)) := by
  have h := IsPrimitive.mellinConvergent_quadraticConvolutionCutoffError χ hprim hχ hs
  rw [MellinConvergent, cutoff_mellin_kernel,
    integrableOn_indicator_iff measurableSet_Ioi] at h
  simpa only [Ioi_inter_Ioi, max_eq_left (show (0 : ℝ) ≤ 1 by norm_num)] using h

/-- Holomorphy comes from the Mellin transform convergence strip, not from an
assumed identity with a continued L-function. -/
theorem IsPrimitive.differentiableAt_quadraticConvolutionErrorIntegral
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ (quadraticConvolutionErrorIntegral χ) s := by
  have hm : DifferentiableAt ℂ (mellin (quadraticConvolutionCutoffError χ)) (-s) := by
    apply mellin_differentiableAt_of_isBigO_rpow
      ((IsPrimitive.locallyIntegrable_quadraticConvolutionCutoffError χ hprim hχ).locallyIntegrableOn _)
      (a := -(1 / 2)) (b := -s.re - 1)
    · simpa using IsPrimitive.quadraticConvolutionCutoffError_isBigO_atTop χ hprim hχ
    · simp only [neg_re]; linarith
    · exact quadraticConvolutionCutoffError_isBigO_zero χ _
    · simp only [neg_re]; linarith
  simpa only [Function.comp_def, mellin_quadraticConvolutionCutoffError] using
    hm.comp s differentiableAt_id.neg

omit [NeZero q] in
theorem quadraticSiegelConvolution_ofReal_eq_zetaMul
    (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1) (n : ℕ) :
    (quadraticSiegelConvolution χ n : ℂ) = χ.zetaMul n := by
  apply Complex.ext
  · rfl
  · exact (zetaMul_im_eq_zero_of_sq_eq_one χ hquad n).symm

omit [NeZero q] in
theorem quadraticSiegelConvolutionSummatory_ofReal_eq_sum_zetaMul
    (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1) (n : ℕ) :
    (quadraticSiegelConvolutionSummatory χ n : ℂ) =
      ∑ k ∈ Finset.Icc 1 n, χ.zetaMul k := by
  simp only [quadraticSiegelConvolutionSummatory, ofReal_sum,
    quadraticSiegelConvolution_ofReal_eq_zetaMul χ hquad]

theorem IsPrimitive.quadraticSiegelConvolutionSummatory_isBigO
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    quadraticSiegelConvolutionSummatory χ =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
  refine isBigO_iff.mpr ⟨79 * q + |(χ.LFunction 1).re|, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt : Real.sqrt (n : ℝ) ≤ n :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have he := IsPrimitive.abs_quadratic_convolution_sub_LValue_main_le χ hprim hχ n
  have htriangle := abs_add_le
    (quadraticSiegelConvolutionSummatory χ n - (n : ℝ) * (χ.LFunction 1).re)
    ((n : ℝ) * (χ.LFunction 1).re)
  rw [sub_add_cancel, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))] at htriangle
  simp only [Real.norm_eq_abs, Real.rpow_one,
    abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  have hbound := mul_le_mul_of_nonneg_left hsqrt (show (0 : ℝ) ≤ 79 * q by positivity)
  nlinarith

theorem IsPrimitive.sum_zetaMul_isBigO
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, χ.zetaMul k) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
  have h := IsPrimitive.quadraticSiegelConvolutionSummatory_isBigO χ hprim hχ
  rw [isBigO_iff] at h ⊢
  obtain ⟨C, hC⟩ := h
  refine ⟨C, hC.mono fun n hn => ?_⟩
  simpa only [← quadraticSiegelConvolutionSummatory_ofReal_eq_sum_zetaMul χ hquad,
    Complex.norm_real] using hn

private theorem mul_error_cpow (t : ℝ) (ht : 0 < t) (s : ℂ) :
    (t : ℂ) * (t : ℂ) ^ (-(s + 1)) = (t : ℂ) ^ (-s) := by
  calc
    _ = (t : ℂ) ^ (1 : ℂ) * (t : ℂ) ^ (-(s + 1)) := by rw [cpow_one]
    _ = (t : ℂ) ^ ((1 : ℂ) + -(s + 1)) :=
      (cpow_add _ _ (ofReal_ne_zero.mpr ht.ne')).symm
    _ = _ := by congr 1; ring

private theorem summatory_kernel_split
    (χ : DirichletCharacter ℂ q) (s : ℂ) {t : ℝ} (ht : 1 < t) :
    (quadraticSiegelConvolutionSummatory χ ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      quadraticConvolutionErrorKernel χ s t +
        ((χ.LFunction 1).re : ℂ) * (t : ℂ) ^ (-s) := by
  rw [quadraticConvolutionErrorKernel, quadraticConvolutionError, ofReal_sub, ofReal_mul,
    sub_mul, ← mul_error_cpow t (by linarith) s]
  ring

/-- Identification with the ordinary absolutely convergent Dirichlet product.
This is the starting open set for analytic continuation. -/
theorem IsPrimitive.riemannZeta_mul_LFunction_eq_errorIntegral_of_one_lt_re
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * χ.LFunction s =
      ((χ.LFunction 1).re : ℂ) * s / (s - 1) +
        s * quadraticConvolutionErrorIntegral χ s := by
  have hid := LSeries_eq_mul_integral (fun n => χ.zetaMul n)
    (r := 1) (by norm_num) hs (χ.LSeriesSummable_zetaMul hs)
    (IsPrimitive.sum_zetaMul_isBigO χ hprim hχ hquad)
  rw [← riemannZeta_mul_LFunction_eq_LSeries_zetaMul χ hs] at hid
  simp only [← quadraticSiegelConvolutionSummatory_ofReal_eq_sum_zetaMul χ hquad] at hid
  have hsplit :
      (∫ t in Ioi (1 : ℝ),
        (quadraticSiegelConvolutionSummatory χ ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) =
        quadraticConvolutionErrorIntegral χ s +
          ((χ.LFunction 1).re : ℂ) * (-(1 : ℂ) / (-s + 1)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => summatory_kernel_split χ s ht)]
    rw [integral_add
      (IsPrimitive.integrableOn_quadraticConvolutionErrorKernel χ hprim hχ (by linarith))
      ((integrableOn_Ioi_cpow_of_lt (by simpa using (neg_lt_neg hs))
        (by norm_num : (0 : ℝ) < 1)).const_mul ((χ.LFunction 1).re : ℂ)),
      integral_const_mul, integral_Ioi_cpow_of_lt (by simpa using (neg_lt_neg hs))
        (by norm_num : (0 : ℝ) < 1)]
    simp only [ofReal_one, one_cpow]
    rfl
  rw [hid, hsplit]
  have hm : -s + 1 = -(s - 1) := by ring
  rw [hm, div_neg, neg_div, neg_neg]
  ring

/-- The pole-cleared product identity on the entire half-plane `Re s > 1/2`.
The equality on `Re s > 1` is continued by the identity theorem, using the
holomorphic Mellin error and the entire regularization `riemannZeta₁`. -/
theorem IsPrimitive.riemannZeta₁_mul_LFunction_eq_errorIntegral
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) {s : ℂ} (hs : 1 / 2 < s.re) :
    riemannZeta₁ s * χ.LFunction s =
      ((χ.LFunction 1).re : ℂ) * s +
        (s - 1) * s * quadraticConvolutionErrorIntegral χ s := by
  let U : Set ℂ := {z | 1 / 2 < z.re}
  let F : ℂ → ℂ := fun z => ((χ.LFunction 1).re : ℂ) * z +
    (z - 1) * z * quadraticConvolutionErrorIntegral χ z
  let G : ℂ → ℂ := fun z => riemannZeta₁ z * χ.LFunction z
  have hUopen : IsOpen U := continuous_re.isOpen_preimage _ isOpen_Ioi
  have hFdiff : DifferentiableOn ℂ F U := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    have hE := IsPrimitive.differentiableAt_quadraticConvolutionErrorIntegral χ hprim hχ hz
    dsimp [F]
    fun_prop
  have hF : AnalyticOnNhd ℂ F U := hFdiff.analyticOnNhd hUopen
  have hG : AnalyticOnNhd ℂ G U :=
    (differentiable_riemannZeta₁.mul (χ.differentiable_LFunction hχ)).differentiableOn.analyticOnNhd
      isOpen_univ |>.mono (subset_univ U)
  have hpre : IsPreconnected U := (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  have htwo : (2 : ℂ) ∈ U := by norm_num [U]
  have hevent : G =ᶠ[𝓝 (2 : ℂ)] F := by
    filter_upwards [eventually_of_mem
      ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
        (by norm_num : (1 : ℝ) < (2 : ℂ).re)) (fun z hz => hz)] with z hz
    have hz1 : z ≠ 1 := by
      intro h
      rw [h] at hz
      norm_num at hz
    have hzeta : riemannZeta₁ z = (z - 1) * riemannZeta z := by
      rw [riemannZeta_eq_inv_sub_mul hz1, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hz1),
        one_mul]
    dsimp [F, G]
    rw [hzeta, mul_assoc,
      IsPrimitive.riemannZeta_mul_LFunction_eq_errorIntegral_of_one_lt_re χ hprim hχ hquad hz]
    field_simp
  exact hG.eqOn_of_preconnected_of_eventuallyEq hF hpre htwo hevent hs

/-- The actual continued product, represented by an absolutely convergent
summatory-error integral throughout `Re s > 1/2`, away from its pole. -/
theorem IsPrimitive.riemannZeta_mul_LFunction_eq_errorIntegral
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s * χ.LFunction s =
      ((χ.LFunction 1).re : ℂ) * s / (s - 1) +
        s * quadraticConvolutionErrorIntegral χ s := by
  rw [riemannZeta_eq_inv_sub_mul hs1, mul_assoc,
    IsPrimitive.riemannZeta₁_mul_LFunction_eq_errorIntegral χ hprim hχ hquad hs]
  field_simp

end AnalyticNumberTheory.LargeSieve.Bombieri1965Theorem4
