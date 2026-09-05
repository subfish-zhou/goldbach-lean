import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation17AlphaBridge
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation17ShiftPayments
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation17Conjugation
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation17CorrectedKernel
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLRightHalfPlaneBounds
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLTwistedSmoothedPerron
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

noncomputable section

open Classical Complex Finset MeasureTheory Set Filter
open scoped BigOperators ArithmeticFunction Topology
open DirichletLAbelWeightVariation
open DirichletLConditionalDerivativeSeries
open DirichletLConditionalDerivativeAnalyticContinuation

namespace AnalyticNumberTheory.LargeSieve


/-- Assembly-facing alias for the rigorous **corrected-source** kernel.  The
conductor level is retained only to keep the equation-(17) integral API aligned
with the surrounding block notation. -/
def chen1973Lemma6Eq17CorrectedRadialKernel (x _level : ℕ) (s : ℂ) : ℝ :=
  chen1973Lemma6Eq17CorrectedKernel x s

private def eq17LinearKernel (x : ℕ) (s : ℂ) : ℝ :=
  ‖s‖ * (1 + ‖s‖ / chen1973PerronScale (x : ℝ))

private theorem eq17LinearKernel_pos {x : ℕ} (hx : 1 < x)
    {σ v : ℝ} (hσ : 0 < σ) :
    0 < eq17LinearKernel x (σ + v * I) := by
  unfold eq17LinearKernel
  have hs : 0 < ‖((σ : ℂ) + (v : ℂ) * I)‖ := by
    rw [norm_pos_iff]
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  exact mul_pos hs (by
    have := chen1973Lemma6_eq17_perronScale_pos hx
    positivity)

private theorem chen1973Lemma6_eq17_correctedRadialKernel_pos
    {x level : ℕ} (hx : 1 < x) {σ v : ℝ} (hσ : 0 < σ) :
    0 < chen1973Lemma6Eq17CorrectedRadialKernel x level (σ + v * I) := by
  unfold chen1973Lemma6Eq17CorrectedRadialKernel chen1973Lemma6Eq17CorrectedKernel
  have hs : 0 < ‖((σ : ℂ) + (v : ℂ) * I)‖ := by
    rw [norm_pos_iff]
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hA := chen1973Lemma6_eq17_perronScale_pos hx
  exact mul_pos hs (by positivity)

private theorem chen1973Lemma6_eq17_radialKernel_le_two_correctedRadialKernel
    {x level : ℕ} (hx : 3 ≤ x) (s : ℂ) :
    eq17LinearKernel x s ≤
      2 * chen1973Lemma6Eq17CorrectedRadialKernel x level s := by
  let A := chen1973PerronScale (x : ℝ)
  let u := ‖s‖ / A
  let N := chen1973PerronOrder (x : ℝ) + 1
  have hA : 0 < A := chen1973Lemma6_eq17_perronScale_pos (by omega : 1 < x)
  have hu : 0 ≤ u := div_nonneg (norm_nonneg _) hA.le
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hbase : 1 + u ≤ 2 * (1 + u ^ N) := by
    rcases le_total u 1 with hu1 | h1u
    · have hupow : 0 ≤ u ^ N := pow_nonneg hu _
      nlinarith
    · have hupow : u ≤ u ^ N := by
        simpa using pow_le_pow_right₀ h1u hN
      nlinarith [pow_nonneg hu N]
  unfold eq17LinearKernel chen1973Lemma6Eq17CorrectedRadialKernel
    chen1973Lemma6Eq17CorrectedKernel
  dsimp [A, u, N] at hbase ⊢
  nlinarith [mul_le_mul_of_nonneg_left hbase (norm_nonneg s)]

private theorem chen1973Lemma6_eq17_correctedRadialKernel_inv_le_two_radialKernel_inv
    {x level : ℕ} (hx : 3 ≤ x) {s : ℂ}
    (hcorrected : 0 < chen1973Lemma6Eq17CorrectedRadialKernel x level s)
    (hradial : 0 < eq17LinearKernel x s) :
    (chen1973Lemma6Eq17CorrectedRadialKernel x level s)⁻¹ ≤
      2 * (eq17LinearKernel x s)⁻¹ := by
  have hcmp := chen1973Lemma6_eq17_radialKernel_le_two_correctedRadialKernel
    (x := x) (level := level) hx s
  calc
    (chen1973Lemma6Eq17CorrectedRadialKernel x level s)⁻¹ =
        1 / chen1973Lemma6Eq17CorrectedRadialKernel x level s := by rw [one_div]
    _ ≤ 2 / eq17LinearKernel x s :=
      (div_le_div_iff₀ hcorrected hradial).2 (by simpa using hcmp)
    _ = 2 * (eq17LinearKernel x s)⁻¹ := by rw [div_eq_mul_inv]

private theorem chen1973Lemma6_eq17_mellinKernel_norm_le_correctedRadialKernel
    {x level : ℕ} (hx : 3 ≤ x) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖chen1973MellinKernel (x : ℝ) s‖ ≤
      2 / chen1973Lemma6Eq17CorrectedRadialKernel x level s := by
  let A := chen1973PerronScale (x : ℝ)
  let N := chen1973PerronOrder (x : ℝ) + 1
  have hA : 0 < A := chen1973Lemma6_eq17_perronScale_pos (by omega : 1 < x)
  have hN : 2 ≤ N := by
    dsimp [N]
    have := (chen1973Lemma6_eq17_one_le_log_and_order hx).2
    omega
  by_cases hs0 : s = 0
  · subst s
    simp [chen1973MellinKernel, chen1973Lemma6Eq17CorrectedRadialKernel,
      chen1973Lemma6Eq17CorrectedKernel]
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  let u : ℝ := ‖s‖ / A
  have hu : 0 ≤ u := div_nonneg (norm_nonneg _) hA.le
  have hcomplex_one : 1 ≤ ‖1 + s / (A : ℂ)‖ :=
    chen1973Lemma6_eq17_one_le_norm_one_add_div hA hs
  have hcomplex_u : u ≤ ‖1 + s / (A : ℂ)‖ := by
    have hsq : u ^ 2 ≤ ‖1 + s / (A : ℂ)‖ ^ 2 := by
      have hnormsq : ‖1 + s / (A : ℂ)‖ ^ 2 =
          (1 + s.re / A) ^ 2 + (s.im / A) ^ 2 := by
        rw [Complex.sq_norm]
        simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re,
          Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
          add_zero, Complex.add_im, Complex.one_im, zero_add, Complex.div_im,
          pow_two]
        field_simp [hA.ne']
        ring
      have hsnormsq : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
        rw [Complex.sq_norm]
        simp [Complex.normSq_apply, pow_two]
      rw [hnormsq]
      dsimp [u]
      rw [div_pow, hsnormsq]
      field_simp [hA.ne']
      nlinarith
    exact (sq_le_sq₀ hu (norm_nonneg _)).mp hsq
  have honepow : (1 : ℝ) ≤ ‖1 + s / (A : ℂ)‖ ^ N := by
    simpa using pow_le_pow_right₀ hcomplex_one (Nat.zero_le N)
  have hupow : u ^ N ≤ ‖1 + s / (A : ℂ)‖ ^ N := by
    exact pow_le_pow_left₀ hu hcomplex_u N
  have hrad : 1 + u ^ N ≤ 2 * ‖1 + s / (A : ℂ)‖ ^ N := by
    nlinarith
  unfold chen1973MellinKernel chen1973Lemma6Eq17CorrectedRadialKernel
  rw [norm_div, norm_one, norm_mul, norm_pow]
  change 1 / (‖s‖ * ‖1 + s / (A : ℂ)‖ ^ N) ≤
    2 / (‖s‖ * (1 + u ^ N))
  have hcpos : 0 < ‖1 + s / (A : ℂ)‖ ^ N := pow_pos (zero_lt_one.trans_le hcomplex_one) _
  have hrpos : 0 < 1 + u ^ N := by positivity
  rw [div_le_div_iff₀ (mul_pos hsn hcpos) (mul_pos hsn hrpos)]
  nlinarith [mul_le_mul_of_nonneg_left hrad hsn.le]

private theorem chen1973Lemma6_eq17_correctedRadialKernel_inv_le_cauchy
    {x level : ℕ} (hx : 3 ≤ x) {σ v : ℝ} (hσ : 0 < σ)
    (hσupper : σ ≤ 2) :
    (chen1973Lemma6Eq17CorrectedRadialKernel x level (σ + v * I))⁻¹ ≤
      2 * σ⁻¹ * (1 + (v / chen1973PerronScale (x : ℝ)) ^ 2)⁻¹ := by
  let A := chen1973PerronScale (x : ℝ)
  let r := ‖((σ : ℂ) + (v : ℂ) * I)‖
  let u := r / A
  let N := chen1973PerronOrder (x : ℝ) + 1
  have hA : 0 < A := chen1973Lemma6_eq17_perronScale_pos (by omega : 1 < x)
  have hr : 0 ≤ r := norm_nonneg _
  have hσr : σ ≤ r := by
    have hrsq := chen1973Lemma6_eq17_vertical_norm_sq σ v
    dsimp [r]
    nlinarith [sq_nonneg v, sq_nonneg (‖((σ : ℂ) + (v : ℂ) * I)‖ - σ)]
  have hu : 0 ≤ u := div_nonneg hr hA.le
  have hN : 2 ≤ N := by
    dsimp [N]
    have := (chen1973Lemma6_eq17_one_le_log_and_order hx).2
    omega
  have hu2 : u ^ 2 ≤ 1 + u ^ N := by
    rcases le_total u 1 with hu1 | h1u
    · have : u ^ 2 ≤ 1 := by nlinarith [sq_nonneg u, mul_self_le_mul_self hu hu1]
      exact this.trans (le_add_of_nonneg_right (pow_nonneg hu _))
    · exact (pow_le_pow_right₀ h1u hN).trans (le_add_of_nonneg_left (by norm_num))
  have hvu : (v / A) ^ 2 ≤ u ^ 2 := by
    have hrsq := chen1973Lemma6_eq17_vertical_norm_sq σ v
    dsimp [u, r]
    field_simp [hA.ne']
    nlinarith [sq_nonneg σ]
  have hden : (1 / 2 : ℝ) * σ * (1 + (v / A) ^ 2) ≤
      chen1973Lemma6Eq17CorrectedRadialKernel x level (σ + v * I) := by
    unfold chen1973Lemma6Eq17CorrectedRadialKernel chen1973Lemma6Eq17CorrectedKernel
    change (1 / 2 : ℝ) * σ * (1 + (v / A) ^ 2) ≤ r * (1 + u ^ N)
    have hsmall : (1 / 2 : ℝ) * (1 + (v / A) ^ 2) ≤ 1 + u ^ N := by
      nlinarith [hvu, hu2, pow_nonneg hu N]
    calc
      (1 / 2 : ℝ) * σ * (1 + (v / A) ^ 2) =
          σ * ((1 / 2 : ℝ) * (1 + (v / A) ^ 2)) := by ring
      _ ≤ σ * (1 + u ^ N) := mul_le_mul_of_nonneg_left hsmall hσ.le
      _ ≤ r * (1 + u ^ N) := mul_le_mul_of_nonneg_right hσr (by positivity)
  have hkpos := chen1973Lemma6_eq17_correctedRadialKernel_pos
    (x := x) (level := level) (v := v) (by omega : 1 < x) hσ
  have hcpos : 0 < (1 / 2 : ℝ) * σ * (1 + (v / A) ^ 2) := by positivity
  calc
    (chen1973Lemma6Eq17CorrectedRadialKernel x level (σ + v * I))⁻¹ ≤
        ((1 / 2 : ℝ) * σ * (1 + (v / A) ^ 2))⁻¹ :=
      by simpa [one_div] using one_div_le_one_div_of_le hcpos hden
    _ = 2 * σ⁻¹ * (1 + (v / A) ^ 2)⁻¹ := by
      field_simp [hσ.ne', show 1 + (v / A) ^ 2 ≠ 0 by positivity]

private theorem chen1973Lemma6Eq17CorrectedRadialKernel_reflection
    (x level : ℕ) (a v : ℝ) :
    chen1973Lemma6Eq17CorrectedRadialKernel x level (a + (-v) * I) =
      chen1973Lemma6Eq17CorrectedRadialKernel x level (a + v * I) := by
  unfold chen1973Lemma6Eq17CorrectedRadialKernel chen1973Lemma6Eq17CorrectedKernel
  have hs : ‖(a : ℂ) + -(v : ℂ) * I‖ = ‖(a : ℂ) + (v : ℂ) * I‖ := by
    simp [Complex.norm_def, Complex.normSq_apply]
  rw [hs]

def chen1973Lemma6Eq17CorrectedRadialFirstIntegral
    (x L level B k m H : ℕ) : ℝ :=
  ∫ v in Ioi (0 : ℝ), chen1973Lemma6A x L level B k m H
      (chen1973Lemma6Alpha x + v * I) /
    chen1973Lemma6Eq17CorrectedRadialKernel x level (chen1973Lemma6Alpha x + v * I)

def chen1973Lemma6Eq17CorrectedRadialSecondIntegral
    (x L level B k m H : ℕ) : ℝ :=
  ∫ v in Ioi (0 : ℝ), chen1973Lemma6B x L level B k m H
      (chen1973Lemma6Beta x + v * I) /
    chen1973Lemma6Eq17CorrectedRadialKernel x level (chen1973Lemma6Beta x + v * I)

def chen1973Lemma6Eq17CorrectedRadialFirstFullIntegral
    (x L level B k m H : ℕ) : ℝ :=
  ∫ v : ℝ, chen1973Lemma6A x L level B k m H
      (chen1973Lemma6Alpha x + v * I) /
    chen1973Lemma6Eq17CorrectedRadialKernel x level (chen1973Lemma6Alpha x + v * I)

def chen1973Lemma6Eq17CorrectedRadialSecondFullIntegral
    (x L level B k m H : ℕ) : ℝ :=
  ∫ v : ℝ, chen1973Lemma6B x L level B k m H
      (chen1973Lemma6Beta x + v * I) /
    chen1973Lemma6Eq17CorrectedRadialKernel x level (chen1973Lemma6Beta x + v * I)

private theorem integral_eq_two_mul_Ioi_of_even_corrected (f : ℝ → ℝ)
    (heven : ∀ v, f (-v) = f v) :
    (∫ v : ℝ, f v) = 2 * ∫ v in Ioi (0 : ℝ), f v := by
  have habs : f = fun v => f |v| := by
    funext v
    rcases le_total 0 v with hv | hv
    · rw [abs_of_nonneg hv]
    · rw [abs_of_nonpos hv, heven]
  calc
    (∫ v : ℝ, f v) = ∫ v : ℝ, f |v| :=
      integral_congr_ae (ae_of_all _ fun v => congrFun habs v)
    _ = 2 * ∫ v in Ioi (0 : ℝ), f v := integral_comp_abs

set_option maxHeartbeats 800000 in
theorem chen1973Lemma6Eq17CorrectedRadialFirstFullIntegral_eq_two_mul_half
    {x L level B k m H : ℕ} (hlevel : 1 ≤ level) (hx : 1 < x) :
    chen1973Lemma6Eq17CorrectedRadialFirstFullIntegral x L level B k m H =
      2 * chen1973Lemma6Eq17CorrectedRadialFirstIntegral x L level B k m H := by
  unfold chen1973Lemma6Eq17CorrectedRadialFirstFullIntegral
    chen1973Lemma6Eq17CorrectedRadialFirstIntegral
  apply integral_eq_two_mul_Ioi_of_even_corrected
  intro v
  rw [ofReal_neg, chen1973Lemma6A_reflection hlevel]
  · rw [chen1973Lemma6Eq17CorrectedRadialKernel_reflection]
  · unfold chen1973Lemma6Alpha
    have : 0 < Real.log x := Real.log_pos (by exact_mod_cast hx)
    positivity

set_option maxHeartbeats 800000 in
theorem chen1973Lemma6Eq17CorrectedRadialSecondFullIntegral_eq_two_mul_half
    {x L level B k m H : ℕ} (hlevel : 1 ≤ level) (hx : 1 < x) :
    chen1973Lemma6Eq17CorrectedRadialSecondFullIntegral x L level B k m H =
      2 * chen1973Lemma6Eq17CorrectedRadialSecondIntegral x L level B k m H := by
  unfold chen1973Lemma6Eq17CorrectedRadialSecondFullIntegral
    chen1973Lemma6Eq17CorrectedRadialSecondIntegral
  apply integral_eq_two_mul_Ioi_of_even_corrected
  intro v
  rw [ofReal_neg, chen1973Lemma6B_reflection hlevel]
  · rw [chen1973Lemma6Eq17CorrectedRadialKernel_reflection]
  · unfold chen1973Lemma6Beta
    have : 0 < Real.log x := Real.log_pos (by exact_mod_cast hx)
    positivity

def chen1973Lemma6Equation17CorrectedRadialRHS
    (x L level B k m H : ℕ) : ℝ :=
  12 * x * (Real.log x) ^ 2 *
      chen1973Lemma6Eq17CorrectedRadialFirstIntegral x L level B k m H +
    2 * (x : ℝ) ^ ((1 : ℝ) / 2) *
      chen1973Lemma6Eq17CorrectedRadialSecondIntegral x L level B k m H

def Chen1973Equation17CorrectedRadialContourMajorization
    (x L level B k m H : ℕ) : Prop :=
  chen1973Lemma6NmBlockActual x L level B k m ≤
    chen1973Lemma6Equation17CorrectedRadialRHS x L level B k m H

/-- The pointwise alpha-line logarithmic-derivative estimate paid by the
external `(log x)^2` factor in the corrected equation-(17) assembly.  The
explicit absolute constant `6` comes from the absolute twisted von Mangoldt
series; the current source quantity `A` remains free of `L'/L`. -/
def Chen1973Equation17AlphaLogDerivativePayment
    (x L level : ℕ) : Prop :=
  ∀ d ∈ chen1973Lemma6ConductorBlock x L level,
    ∀ χ : PrimitiveCharacter d, ∀ t : ℝ,
      ‖chen1973PrimitiveLDeriv d (chen1973Lemma6Alpha x + t * I) χ /
        chen1973Lemma6PrimitiveLValue d
          (chen1973Lemma6Alpha x + t * I) χ‖ ≤ 6 * (Real.log x) ^ 2

private theorem one_lt_of_mem_conductorBlock
    {x L level d : ℕ} (hlevel : 1 ≤ level)
    (hd : d ∈ chen1973Lemma6ConductorBlock x L level) :
    1 < d := by
  by_cases hzero : level = 0
  · omega
  · simp [chen1973Lemma6ConductorBlock, hzero, chen1973Lemma6DyadicShell] at hd
    omega

private theorem primitiveCharacter_ne_one_of_one_lt
    {d : ℕ} [NeZero d] (hd : 1 < d) (χ : PrimitiveCharacter d) :
    χ.1 ≠ 1 := by
  intro hχ
  have hprim := χ.2
  rw [DirichletCharacter.IsPrimitive, hχ,
    DirichletCharacter.conductor_one] at hprim
  omega

private theorem alpha_pos {x : ℕ} (hx : 3 ≤ x) :
    0 < chen1973Lemma6Alpha x := by
  unfold chen1973Lemma6Alpha
  have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  positivity

private theorem beta_pos {x : ℕ} (hx : 3 ≤ x) :
    0 < chen1973Lemma6Beta x := by
  unfold chen1973Lemma6Beta
  have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  positivity

private theorem xDivPrimePair_cpow_eq
    {x : ℕ} (_hx : 0 < x) {pp : ℕ × ℕ} (hp₁ : 0 < pp.1) (hp₂ : 0 < pp.2)
    (s : ℂ) :
    (((x : ℝ) / ((pp.1 : ℝ) * pp.2) : ℂ) ^ s) =
      (x : ℂ) ^ s / ((pp.1 * pp.2 : ℂ) ^ s) := by
  have hmul := @mul_cpow_ofReal_nonneg
    (a := (x : ℝ) / ((pp.1 : ℝ) * pp.2)) (b := ((pp.1 * pp.2 : ℕ) : ℝ))
    (r := s) (div_nonneg (Nat.cast_nonneg _) (by positivity)) (Nat.cast_nonneg _)
  push_cast at hmul
  apply (eq_div_iff (Complex.cpow_ne_zero_iff.mpr (Or.inl (by
    exact_mod_cast (Nat.mul_pos hp₁ hp₂).ne')))).2
  simpa [div_mul_cancel₀, hp₁.ne', hp₂.ne'] using hmul.symm

private theorem norm_scaledKernel_alpha_le
    {x level : ℕ} (hx : 3 ≤ x) (t : ℝ) :
    ‖((((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (x : ℂ) ^ (chen1973Lemma6Alpha x + t * I)) *
        chen1973MellinKernel (x : ℝ) (chen1973Lemma6Alpha x + t * I))‖ ≤
      x /
        chen1973Lemma6Eq17CorrectedRadialKernel x level (chen1973Lemma6Alpha x + t * I) := by
  have hx1 : 1 < x := by omega
  have hxR : 0 < (x : ℝ) := by positivity
  have hαre : 0 ≤ (chen1973Lemma6Alpha x + t * I : ℂ).re := by
    have hα0 : 0 ≤ chen1973Lemma6Alpha x := (alpha_pos hx).le
    simpa using hα0
  have hkernel :=
    chen1973Lemma6_eq17_mellinKernel_norm_le_correctedRadialKernel (x := x) (level := level) hx
      (s := chen1973Lemma6Alpha x + t * I) hαre
  have hpow := chen1973Lemma6_eq17_rpow_alpha hx1

  have hconst :
      (2 / (2 * Real.pi)) * Real.exp 1 ≤ 1 := by
    have he : Real.exp 1 < 3 := Real.exp_one_lt_three
    have hp : 3 < Real.pi := Real.pi_gt_three
    rw [show (2 / (2 * Real.pi) : ℝ) = 1 / Real.pi by field_simp]
    simpa [div_eq_mul_inv, mul_comm] using
      (div_le_one Real.pi_pos).2 (he.trans hp).le
  have hkernelPos :
      0 < chen1973Lemma6Eq17CorrectedRadialKernel x level (chen1973Lemma6Alpha x + t * I) := by
    exact chen1973Lemma6_eq17_correctedRadialKernel_pos (x := x) (level := level) hx1 (alpha_pos hx)
  have hcpow :
      ‖(x : ℂ) ^ (chen1973Lemma6Alpha x + t * I)‖ =
        (x : ℝ) ^ chen1973Lemma6Alpha x := by
    change ‖((x : ℝ) : ℂ) ^ (chen1973Lemma6Alpha x + t * I)‖ = _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxR]
    simp
  calc
    ‖((((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (x : ℂ) ^ (chen1973Lemma6Alpha x + t * I)) *
          chen1973MellinKernel (x : ℝ) (chen1973Lemma6Alpha x + t * I))‖
      = ((1 / (2 * Real.pi) : ℝ) *
          (x : ℝ) ^ chen1973Lemma6Alpha x) *
          ‖chen1973MellinKernel (x : ℝ) (chen1973Lemma6Alpha x + t * I)‖ := by
            rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (by positivity), hcpow]
    _ ≤ ((1 / (2 * Real.pi) : ℝ) * (x : ℝ) ^ chen1973Lemma6Alpha x) *
          (2 /
            chen1973Lemma6Eq17CorrectedRadialKernel x level (chen1973Lemma6Alpha x + t * I)) := by
            gcongr
    _ = ((2 / (2 * Real.pi)) * (x : ℝ) ^ chen1973Lemma6Alpha x) /
          chen1973Lemma6Eq17CorrectedRadialKernel x level (chen1973Lemma6Alpha x + t * I) := by
            ring_nf
    _ ≤ (x : ℝ) /
          chen1973Lemma6Eq17CorrectedRadialKernel x level (chen1973Lemma6Alpha x + t * I) := by
            rw [hpow]
            have hx0 : 0 ≤ (x : ℝ) := by positivity
            have htmp :
                ((2 / (2 * Real.pi)) * Real.exp 1) * (x : ℝ) ≤
                  (x : ℝ) := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using
                (mul_le_mul_of_nonneg_left hconst hx0)
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              div_le_div_of_nonneg_right htmp hkernelPos.le

/-- The original beta-line prefactor is `sqrt x` (Chen p.121). -/
theorem chen1973Lemma6_eq17_scaledKernel_beta_le_source
    {x level : ℕ} (hx : 3 ≤ x) (t : ℝ) :
    ‖((((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (x : ℂ) ^ (chen1973Lemma6Beta x + t * I)) *
        chen1973MellinKernel (x : ℝ) (chen1973Lemma6Beta x + t * I))‖ ≤
      (x : ℝ) ^ ((1 : ℝ) / 2) /
        chen1973Lemma6Eq17CorrectedRadialKernel x level (chen1973Lemma6Beta x + t * I) := by
  have hx1 : 1 < x := by omega
  have hxR : 0 < (x : ℝ) := by positivity
  have hβre : 0 ≤ (chen1973Lemma6Beta x + t * I : ℂ).re := by
    have hβ0 : 0 ≤ chen1973Lemma6Beta x := (beta_pos hx).le
    simpa using hβ0
  have hkernel :=
    chen1973Lemma6_eq17_mellinKernel_norm_le_correctedRadialKernel (x := x) (level := level) hx
      (s := chen1973Lemma6Beta x + t * I) hβre
  have hpow := chen1973Lemma6_eq17_rpow_beta hx1
  have hconst :
      (2 / (2 * Real.pi)) * Real.exp 1 ≤ 1 := by
    have he : Real.exp 1 < 3 := Real.exp_one_lt_three
    have hp : 3 < Real.pi := Real.pi_gt_three
    rw [show (2 / (2 * Real.pi) : ℝ) = 1 / Real.pi by field_simp]
    simpa [div_eq_mul_inv, mul_comm] using
      (div_le_one Real.pi_pos).2 (he.trans hp).le
  have hkernelPos :
      0 < chen1973Lemma6Eq17CorrectedRadialKernel x level (chen1973Lemma6Beta x + t * I) := by
    exact chen1973Lemma6_eq17_correctedRadialKernel_pos (x := x) (level := level) hx1 (beta_pos hx)
  have hcpow :
      ‖(x : ℂ) ^ (chen1973Lemma6Beta x + t * I)‖ =
        (x : ℝ) ^ chen1973Lemma6Beta x := by
    change ‖((x : ℝ) : ℂ) ^ (chen1973Lemma6Beta x + t * I)‖ = _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxR]
    simp
  calc
    ‖((((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (x : ℂ) ^ (chen1973Lemma6Beta x + t * I)) *
          chen1973MellinKernel (x : ℝ) (chen1973Lemma6Beta x + t * I))‖
      = ((1 / (2 * Real.pi) : ℝ) *
          (x : ℝ) ^ chen1973Lemma6Beta x) *
          ‖chen1973MellinKernel (x : ℝ) (chen1973Lemma6Beta x + t * I)‖ := by
            rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (by positivity), hcpow]
    _ ≤ ((1 / (2 * Real.pi) : ℝ) * (x : ℝ) ^ chen1973Lemma6Beta x) *
          (2 /
            chen1973Lemma6Eq17CorrectedRadialKernel x level (chen1973Lemma6Beta x + t * I)) := by
            gcongr
    _ = ((2 / (2 * Real.pi)) * (x : ℝ) ^ chen1973Lemma6Beta x) /
          chen1973Lemma6Eq17CorrectedRadialKernel x level (chen1973Lemma6Beta x + t * I) := by
            ring_nf
    _ ≤ (x : ℝ) ^ ((1 : ℝ) / 2) /
          chen1973Lemma6Eq17CorrectedRadialKernel x level (chen1973Lemma6Beta x + t * I) := by
            rw [hpow]
            have hmain :
                ((2 / (2 * Real.pi)) * Real.exp 1) * Real.sqrt (x : ℝ) ≤
                  (x : ℝ) ^ ((1 : ℝ) / 2) := by
              have hconst' :
                  ((2 / (2 * Real.pi)) * Real.exp 1) * Real.sqrt (x : ℝ) ≤
                    1 * Real.sqrt (x : ℝ) := by
                have hsqrt0 : 0 ≤ Real.sqrt (x : ℝ) := Real.sqrt_nonneg _
                exact mul_le_mul_of_nonneg_right hconst hsqrt0
              simpa only [one_mul, Real.sqrt_eq_rpow] using hconst'
            simpa [mul_assoc] using div_le_div_of_nonneg_right hmain hkernelPos.le

private theorem integrable_inv_eq17Kernel_line
    {x level : ℕ} (hx : 3 ≤ x) {σ : ℝ} (hσ : 0 < σ) (hσupper : σ ≤ 2) :
    Integrable (fun t : ℝ =>
      (chen1973Lemma6Eq17CorrectedRadialKernel x level (σ + t * I))⁻¹) := by
  let a := chen1973PerronScale (x : ℝ)
  have ha : 0 < a := chen1973Lemma6_eq17_perronScale_pos (by omega : 1 < x)
  have hdom : Integrable (fun t : ℝ =>
      2 * σ⁻¹ * (1 + (t / a) ^ 2)⁻¹) := by
    have hbase : Integrable (fun t : ℝ => (1 + ((a⁻¹) * t) ^ 2)⁻¹) :=
      integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero ha.ne')
    convert hbase.const_mul (2 * σ⁻¹) using 1
    funext t
    simp [a, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hmeas : AEStronglyMeasurable (fun t : ℝ =>
      (chen1973Lemma6Eq17CorrectedRadialKernel x level (σ + t * I))⁻¹) := by
    apply Continuous.aestronglyMeasurable
    apply Continuous.inv₀
    · unfold chen1973Lemma6Eq17CorrectedRadialKernel chen1973Lemma6Eq17CorrectedKernel
      fun_prop
    · intro t ht
      exact (chen1973Lemma6_eq17_correctedRadialKernel_pos (x := x) (level := level)
        (by omega : 1 < x) hσ (v := t)).ne' ht
  apply Integrable.mono' hdom hmeas
  filter_upwards with t
  have hpos := chen1973Lemma6_eq17_correctedRadialKernel_pos
    (x := x) (level := level) (by omega : 1 < x) hσ (v := t)
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
  exact chen1973Lemma6_eq17_correctedRadialKernel_inv_le_cauchy
    (x := x) (level := level) (v := t) hx hσ hσupper

private theorem integrable_scaledKernel_alpha
    {x level : ℕ} (hx : 3 ≤ x) :
    Integrable (fun t : ℝ =>
      (x : ℂ) ^ (chen1973Lemma6Alpha x + t * I) *
        chen1973MellinKernel (x : ℝ) (chen1973Lemma6Alpha x + t * I)) := by
  have hx1 : 1 < x := by omega
  have hxR : 0 < (x : ℝ) := by positivity
  have hα : 0 < chen1973Lemma6Alpha x := alpha_pos hx
  have hα2 : chen1973Lemma6Alpha x ≤ 2 := by
    have hlog1 := (chen1973Lemma6_eq17_one_le_log_and_order hx).1
    unfold chen1973Lemma6Alpha
    have hlog : 0 < Real.log (x : ℝ) := lt_of_lt_of_le zero_lt_one hlog1
    have hinv : 1 / Real.log (x : ℝ) ≤ 1 := (div_le_one hlog).2 hlog1
    linarith
  let C : ℝ := (x : ℝ) ^ chen1973Lemma6Alpha x * 2
  have hdom : Integrable (fun t : ℝ =>
      C * (chen1973Lemma6Eq17CorrectedRadialKernel x level
        (chen1973Lemma6Alpha x + t * I))⁻¹) :=
    (integrable_inv_eq17Kernel_line (x := x) (level := level)
      hx hα hα2).const_mul C
  have hmeas : AEStronglyMeasurable (fun t : ℝ =>
      (x : ℂ) ^ (chen1973Lemma6Alpha x + t * I) *
        chen1973MellinKernel (x : ℝ) (chen1973Lemma6Alpha x + t * I)) := by
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · fun_prop (disch := exact Or.inl (by exact_mod_cast hxR.ne'))
    · unfold chen1973MellinKernel
      apply Continuous.div continuous_const
      · fun_prop
      · intro t
        have hsre : 0 < (chen1973Lemma6Alpha x + t * I : ℂ).re := by
          simpa using hα
        apply mul_ne_zero
        · intro hs
          have := congrArg Complex.re hs
          simp at this
          linarith
        · apply pow_ne_zero
          intro hs
          have hscale := chen1973Lemma6_eq17_perronScale_pos hx1
          have hre := congrArg Complex.re hs
          simp [Complex.div_re] at hre
          field_simp [hscale.ne'] at hre
          nlinarith
  apply Integrable.mono' hdom hmeas
  filter_upwards with t
  have hkernel := chen1973Lemma6_eq17_mellinKernel_norm_le_correctedRadialKernel
    (x := x) (level := level) hx
    (s := chen1973Lemma6Alpha x + t * I) (by
      have : 0 ≤ chen1973Lemma6Alpha x := hα.le
      simpa using this)
  have hcpow :
      ‖(x : ℂ) ^ (chen1973Lemma6Alpha x + t * I)‖ =
        (x : ℝ) ^ chen1973Lemma6Alpha x := by
    change ‖((x : ℝ) : ℂ) ^ (chen1973Lemma6Alpha x + t * I)‖ = _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxR]
    simp
  rw [norm_mul, hcpow]
  simpa [C, div_eq_mul_inv, mul_assoc] using
    mul_le_mul_of_nonneg_left hkernel (Real.rpow_nonneg hxR.le _)

private theorem integrable_alphaNegLogDerivIntegrand
    {x d level : ℕ} [NeZero d] (χ : PrimitiveCharacter d) (hd : 1 < d)
    (hχ : χ.1 ≠ 1)
    (hx : 3 ≤ x) (pp : ℕ × ℕ) (hp₁ : 0 < pp.1) (hp₂ : 0 < pp.2) :
    Integrable (chen1973Lemma6AlphaNegLogDerivIntegrand x d χ pp) := by
  rcases pp with ⟨p₁, p₂⟩
  let α := chen1973Lemma6Alpha x
  let X : ℝ := (x : ℝ) / ((p₁ : ℝ) * p₂)
  let kernel : ℝ → ℂ := fun t =>
    (X : ℂ) ^ (α + t * I) *
      chen1973MellinKernel (x : ℝ) (α + t * I)
  let coeff : ℕ → ℝ := fun n =>
    ‖DirichletCharacter.twistedVonMangoldtCoeff χ.1 n /
      (n : ℂ) ^ ((α : ℝ) : ℂ)‖
  have hα : 1 < α := by
    dsimp [α, chen1973Lemma6Alpha]
    have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
    linarith [one_div_pos.mpr hlog]
  have hcoeff : Summable coeff := by
    have h := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ.1 (by
      simpa only [Complex.ofReal_re] using hα :
        1 < (((α : ℝ) : ℂ)).re)
    rw [LSeriesSummable] at h
    convert h.norm using 1
    ext n
    by_cases hn : n = 0
    · simp [coeff, DirichletCharacter.twistedVonMangoldtCoeff, hn, LSeries.term]
    · simp [coeff, DirichletCharacter.twistedVonMangoldtCoeff, hn, LSeries.term, mul_comm]
  have hnorm_eq (n : ℕ) (t : ℝ) :
      ‖DirichletCharacter.twistedVonMangoldtCoeff χ.1 n /
          (n : ℂ) ^ (α + t * I)‖ = coeff n := by
    have hα0 : α ≠ 0 := by linarith
    by_cases hn : n = 0
    · simp [coeff, DirichletCharacter.twistedVonMangoldtCoeff, hn]
    · unfold coeff
      rw [Complex.norm_div, Complex.norm_div,
        Complex.norm_natCast_cpow_of_re_ne_zero,
        Complex.norm_natCast_cpow_of_re_ne_zero]
      · simp [α]
      · simpa only [Complex.ofReal_re] using hα0
      · simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
          sub_zero, add_zero] using hα0
  have hlogMeas : AEStronglyMeasurable (fun t : ℝ =>
      -deriv χ.1.LFunction (α + t * I) /
        χ.1.LFunction (α + t * I)) := by
    have hseries : AEStronglyMeasurable (fun t : ℝ =>
        ∑' n : ℕ, DirichletCharacter.twistedVonMangoldtCoeff χ.1 n /
          (n : ℂ) ^ (α + t * I)) := by
      apply AEStronglyMeasurable.tsum
      intro n
      by_cases hn : n = 0
      · simpa [DirichletCharacter.twistedVonMangoldtCoeff, hn] using
          (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : ℝ => (0 : ℂ)))
      · apply Continuous.aestronglyMeasurable
        fun_prop (disch := simp [hn])
    apply hseries.congr
    filter_upwards with t
    exact (DirichletCharacter.neg_logDeriv_LFunction_eq_tsum_twistedVonMangoldtCoeff
      χ.1 (by simpa [α] using hα)).symm
  have hlogBound : ∀ t : ℝ,
      ‖-deriv χ.1.LFunction (α + t * I) /
          χ.1.LFunction (α + t * I)‖ ≤ ∑' n, coeff n := by
    intro t
    rw [DirichletCharacter.neg_logDeriv_LFunction_eq_tsum_twistedVonMangoldtCoeff
      χ.1 (by simpa [α] using hα)]
    calc
      _ ≤ ∑' n : ℕ,
          ‖DirichletCharacter.twistedVonMangoldtCoeff χ.1 n /
            (n : ℂ) ^ (α + t * I)‖ :=
        norm_tsum_le_tsum_norm (by
          apply Summable.congr hcoeff
          intro n
          exact (hnorm_eq n t).symm)
      _ = ∑' n, coeff n := tsum_congr (hnorm_eq · t)
  have hkernel : Integrable kernel := by
    have hfactor (t : ℝ) :
        kernel t =
          ((p₁ * p₂ : ℂ) ^ (-(α + t * I))) *
            ((x : ℂ) ^ (α + t * I) *
              chen1973MellinKernel (x : ℝ) (α + t * I)) := by
      dsimp [kernel, X]
      have hdiv := xDivPrimePair_cpow_eq (pp := (p₁, p₂))
        (by omega : 0 < x) hp₁ hp₂ (α + t * I)
      push_cast at hdiv ⊢
      rw [hdiv]
      rw [Complex.cpow_neg]
      ring
    have hbase := integrable_scaledKernel_alpha (x := x) (level := level) hx
    have hmeas : AEStronglyMeasurable (fun t : ℝ =>
        (p₁ * p₂ : ℂ) ^ (-(α + t * I))) := by
      apply Continuous.aestronglyMeasurable
      fun_prop (disch := exact Or.inl (by
        exact_mod_cast (Nat.mul_pos hp₁ hp₂).ne'))
    have hbound : ∀ t : ℝ,
        ‖(p₁ * p₂ : ℂ) ^ (-(α + t * I))‖ ≤
          ((p₁ * p₂ : ℕ) : ℝ) ^ (-α) := by
      intro t
      rw [show (↑p₁ * ↑p₂ : ℂ) = ((((p₁ * p₂ : ℕ) : ℝ) : ℂ)) by
        push_cast; rfl]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
      simp
    exact (hbase.bdd_mul hmeas (ae_of_all _ hbound)).congr
      (ae_of_all _ fun t => (hfactor t).symm)
  have hraw : Integrable (fun t : ℝ =>
      (-deriv χ.1.LFunction (α + t * I) /
          χ.1.LFunction (α + t * I)) * kernel t) :=
    (hkernel.bdd_mul hlogMeas (ae_of_all _ hlogBound)).congr
      (ae_of_all _ fun t => by ring)
  unfold chen1973Lemma6AlphaNegLogDerivIntegrand
  simp only [chen1973PrimitiveLDeriv, chen1973Lemma6PrimitiveLValue, dif_pos hd]
  simpa [kernel, X, α] using hraw

private def eq17OrigCharacterIntegrand
    (x d B k m : ℕ) (χ : PrimitiveCharacter d) (t : ℝ) : ℂ :=
  ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
    (Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ *
      chen1973Lemma6AlphaNegLogDerivIntegrand x d χ pp t *
      χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d)

private def eq17SecondAlphaCharacterIntegrand
    (x d B k m H : ℕ) (χ : PrimitiveCharacter d) (t : ℝ) : ℂ :=
  ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
    (Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ *
      ((-chen1973PrimitiveLDeriv d (chen1973Lemma6Alpha x + t * I) χ *
          chen1973Lemma6MobiusPartialSum H (chen1973Lemma6Alpha x + t * I) χ) *
        (((x : ℝ) / ((pp.1 : ℝ) * pp.2) : ℂ) ^
            (chen1973Lemma6Alpha x + t * I) *
          chen1973MellinKernel (x : ℝ) (chen1973Lemma6Alpha x + t * I))) *
      χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d)

private def eq17SecondBetaCharacterIntegrand
    (x d B k m H : ℕ) (χ : PrimitiveCharacter d) (t : ℝ) : ℂ :=
  ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
    (Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ *
      ((-chen1973PrimitiveLDeriv d (chen1973Lemma6Beta x + t * I) χ *
          chen1973Lemma6MobiusPartialSum H (chen1973Lemma6Beta x + t * I) χ) *
        (((x : ℝ) / ((pp.1 : ℝ) * pp.2) : ℂ) ^
            (chen1973Lemma6Beta x + t * I) *
          chen1973MellinKernel (x : ℝ) (chen1973Lemma6Beta x + t * I))) *
      χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d)

private def eq17FirstCharacterIntegrand
    (x d B k m H : ℕ) (χ : PrimitiveCharacter d) (t : ℝ) : ℂ :=
  eq17OrigCharacterIntegrand x d B k m χ t -
    eq17SecondAlphaCharacterIntegrand x d B k m H χ t

private theorem eq17FirstCharacterIntegrand_eq_collected
    {x d B k m H : ℕ} [NeZero d] (χ : PrimitiveCharacter d)
    (hd : 1 < d) (hχ : χ.1 ≠ 1) (hx : 3 ≤ x) (t : ℝ) :
    eq17FirstCharacterIntegrand x d B k m H χ t =
      (-chen1973PrimitiveLDeriv d (chen1973Lemma6Alpha x + t * I) χ /
          chen1973Lemma6PrimitiveLValue d (chen1973Lemma6Alpha x + t * I) χ *
        (1 - chen1973Lemma6PrimitiveLValue d
            (chen1973Lemma6Alpha x + t * I) χ *
          chen1973Lemma6MobiusPartialSum H
            (chen1973Lemma6Alpha x + t * I) χ)) *
      ((x : ℂ) ^ (chen1973Lemma6Alpha x + t * I) *
        chen1973MellinKernel (x : ℝ) (chen1973Lemma6Alpha x + t * I)) *
      chen1973Lemma6Eq17PairPolynomial x B k m
        (chen1973Lemma6Alpha x + t * I) χ := by
  let s : ℂ := chen1973Lemma6Alpha x + t * I
  have h16 := chen1973Lemma6_equation16_on_alpha (H := H)
    χ hχ x (by omega : 1 < x) t
  have hsplit :
      -chen1973PrimitiveLDeriv d s χ / chen1973Lemma6PrimitiveLValue d s χ =
        (-chen1973PrimitiveLDeriv d s χ / chen1973Lemma6PrimitiveLValue d s χ) *
            (1 - chen1973Lemma6PrimitiveLValue d s χ *
              chen1973Lemma6MobiusPartialSum H s χ) +
          (-chen1973PrimitiveLDeriv d s χ *
            chen1973Lemma6MobiusPartialSum H s χ) := by
    simp only [chen1973PrimitiveLDeriv, chen1973Lemma6PrimitiveLValue, dif_pos hd]
    dsimp [s]
    linear_combination -h16
  unfold eq17FirstCharacterIntegrand eq17OrigCharacterIntegrand
    eq17SecondAlphaCharacterIntegrand
    chen1973Lemma6AlphaNegLogDerivIntegrand
    chen1973Lemma6Eq17PairPolynomial
  rw [← Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pp hpp
  obtain ⟨hp₁, hp₂⟩ := chen1973Lemma6PrimePairShell_pos hpp
  have hdiv := xDivPrimePair_cpow_eq (pp := pp)
    (by omega : 0 < x) hp₁ hp₂ s
  change
    (Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ *
          ((-chen1973PrimitiveLDeriv d s χ /
              chen1973Lemma6PrimitiveLValue d s χ) *
            ((((x : ℝ) / ((pp.1 : ℝ) * pp.2) : ℂ) ^ s) *
              chen1973MellinKernel (x : ℝ) s)) *
          χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) -
        (Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ *
          ((-chen1973PrimitiveLDeriv d s χ *
              chen1973Lemma6MobiusPartialSum H s χ) *
            ((((x : ℝ) / ((pp.1 : ℝ) * pp.2) : ℂ) ^ s) *
              chen1973MellinKernel (x : ℝ) s)) *
          χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) =
      ((-chen1973PrimitiveLDeriv d s χ /
            chen1973Lemma6PrimitiveLValue d s χ) *
          (1 - chen1973Lemma6PrimitiveLValue d s χ *
            chen1973Lemma6MobiusPartialSum H s χ)) *
        ((x : ℂ) ^ s * chen1973MellinKernel (x : ℝ) s) *
        (χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) /
          ((pp.1 * pp.2 : ℂ) ^ s *
            Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2))))
  rw [hdiv]
  nth_rewrite 1 [hsplit]
  push_cast
  ring_nf

private theorem eq17SecondBetaCharacterIntegrand_eq_collected
    {x d B k m H : ℕ} [NeZero d] (χ : PrimitiveCharacter d)
    (hd : 1 < d) (hx : 3 ≤ x) (t : ℝ) :
    eq17SecondBetaCharacterIntegrand x d B k m H χ t =
      (-chen1973PrimitiveLDeriv d (chen1973Lemma6Beta x + t * I) χ *
          chen1973Lemma6MobiusPartialSum H
            (chen1973Lemma6Beta x + t * I) χ) *
      ((x : ℂ) ^ (chen1973Lemma6Beta x + t * I) *
        chen1973MellinKernel (x : ℝ) (chen1973Lemma6Beta x + t * I)) *
      chen1973Lemma6Eq17PairPolynomial x B k m
        (chen1973Lemma6Beta x + t * I) χ := by
  let s : ℂ := chen1973Lemma6Beta x + t * I
  unfold eq17SecondBetaCharacterIntegrand chen1973Lemma6Eq17PairPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pp hpp
  obtain ⟨hp₁, hp₂⟩ := chen1973Lemma6PrimePairShell_pos hpp
  have hdiv := xDivPrimePair_cpow_eq (pp := pp)
    (by omega : 0 < x) hp₁ hp₂ s
  change
    (Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ *
          ((-chen1973PrimitiveLDeriv d s χ *
              chen1973Lemma6MobiusPartialSum H s χ) *
            ((((x : ℝ) / ((pp.1 : ℝ) * pp.2) : ℂ) ^ s) *
              chen1973MellinKernel (x : ℝ) s)) *
          χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) =
      (-chen1973PrimitiveLDeriv d s χ *
          chen1973Lemma6MobiusPartialSum H s χ) *
        ((x : ℂ) ^ s * chen1973MellinKernel (x : ℝ) s) *
        (χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) /
          ((pp.1 * pp.2 : ℂ) ^ s *
            Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2))))
  rw [hdiv]
  push_cast
  ring

private theorem integrable_eq17OrigCharacterIntegrand
    {x d level B k m : ℕ} [NeZero d] (χ : PrimitiveCharacter d)
    (hd : 1 < d) (hχ : χ.1 ≠ 1) (hx : 3 ≤ x) :
    Integrable (eq17OrigCharacterIntegrand x d B k m χ) := by
  unfold eq17OrigCharacterIntegrand
  apply integrable_finsetSum
  intro pp hpp
  obtain ⟨hp₁, hp₂⟩ := chen1973Lemma6PrimePairShell_pos hpp
  exact (((integrable_alphaNegLogDerivIntegrand
    (level := level) χ hd hχ hx pp hp₁ hp₂).const_mul
      (((Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ : ℝ) : ℂ)).mul_const
        (χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d))).congr
          (ae_of_all _ fun _ => by push_cast; ring)

private def eq17SecondPairIntegrand
    (x d H : ℕ) [NeZero d] (pp : ℕ × ℕ) (χ : PrimitiveCharacter d)
    (sigma t : ℝ) : ℂ :=
  (Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ *
    ((-deriv χ.1.LFunction (sigma + t * I) *
        chen1973Lemma6MobiusPartialSum H (sigma + t * I) χ) *
      (((x : ℝ) / ((pp.1 : ℝ) * pp.2) : ℂ) ^ (sigma + t * I) *
        chen1973MellinKernel (x : ℝ) (sigma + t * I))) *
    χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d)

private theorem integrable_eq17SecondPairIntegrand
    {x d H : ℕ} [NeZero d] (χ : PrimitiveCharacter d)
    (hχ : χ.1 ≠ 1) (hx : 3 ≤ x) {pp : ℕ × ℕ}
    (hp₁ : 0 < pp.1) (hp₂ : 0 < pp.2)
    (sigma : ℝ) (hsigma :
      sigma = chen1973Lemma6Alpha x ∨ sigma = chen1973Lemma6Beta x) :
    Integrable (eq17SecondPairIntegrand x d H pp χ sigma) := by
  let y : ℝ := (x : ℝ) / ((pp.1 : ℝ) * pp.2)
  have hy : 0 < y := by positivity
  have hline : chen1973Lemma6Beta x ≤ sigma ∧ sigma ≤ chen1973Lemma6Alpha x := by
    rcases hsigma with rfl | rfl
    · constructor
      · unfold chen1973Lemma6Beta chen1973Lemma6Alpha
        linarith
      · rfl
    · exact ⟨le_rfl, by
        unfold chen1973Lemma6Beta chen1973Lemma6Alpha
        linarith⟩
  have hbase := integrable_chen1973Lemma6Eq17_verticalSection
    (H := H) χ hχ hx hy hline.1 hline.2
  have hconst := (hbase.const_mul
      (-(((Real.log y)⁻¹ : ℝ) : ℂ))).mul_const
        (χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d))
  exact hconst.congr (ae_of_all _ fun t => by
    unfold eq17SecondPairIntegrand chen1973VerticalSection
      chen1973Lemma6Eq17ShiftIntegrand
    dsimp [y]
    push_cast
    ring)

private theorem integrable_eq17SecondCharacterIntegrand
    {x d B k m H : ℕ} [NeZero d] (χ : PrimitiveCharacter d)
    (hχ : χ.1 ≠ 1) (hx : 3 ≤ x)
    (sigma : ℝ) (hsigma :
      sigma = chen1973Lemma6Alpha x ∨ sigma = chen1973Lemma6Beta x) :
    Integrable (fun t : ℝ =>
      ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
        eq17SecondPairIntegrand x d H pp χ sigma t) := by
  apply integrable_finsetSum
  intro pp hpp
  obtain ⟨hp₁, hp₂⟩ := chen1973Lemma6PrimePairShell_pos hpp
  exact integrable_eq17SecondPairIntegrand χ hχ hx hp₁ hp₂ sigma hsigma

private theorem integrable_eq17SecondAlphaCharacterIntegrand
    {x d B k m H : ℕ} [NeZero d] (χ : PrimitiveCharacter d)
    (hd : 1 < d) (hχ : χ.1 ≠ 1) (hx : 3 ≤ x) :
    Integrable (eq17SecondAlphaCharacterIntegrand x d B k m H χ) := by
  unfold eq17SecondAlphaCharacterIntegrand
  simp only [chen1973PrimitiveLDeriv, dif_pos hd]
  exact (integrable_eq17SecondCharacterIntegrand
      (B := B) (k := k) (m := m) (H := H) χ hχ hx
      (chen1973Lemma6Alpha x) (Or.inl rfl)).congr
    (ae_of_all _ fun t => by
      apply Finset.sum_congr rfl
      intro pp hpp
      unfold eq17SecondPairIntegrand
      push_cast
      ring)

private theorem integrable_eq17SecondBetaCharacterIntegrand
    {x d B k m H : ℕ} [NeZero d] (χ : PrimitiveCharacter d)
    (hd : 1 < d) (hχ : χ.1 ≠ 1) (hx : 3 ≤ x) :
    Integrable (eq17SecondBetaCharacterIntegrand x d B k m H χ) := by
  unfold eq17SecondBetaCharacterIntegrand
  simp only [chen1973PrimitiveLDeriv, dif_pos hd]
  exact (integrable_eq17SecondCharacterIntegrand
      (B := B) (k := k) (m := m) (H := H) χ hχ hx
      (chen1973Lemma6Beta x) (Or.inr rfl)).congr
    (ae_of_all _ fun t => by
      apply Finset.sum_congr rfl
      intro pp hpp
      unfold eq17SecondPairIntegrand
      push_cast
      ring)

private theorem integrable_eq17FirstCharacterIntegrand
    {x d level B k m H : ℕ} [NeZero d] (χ : PrimitiveCharacter d)
    (hd : 1 < d) (hχ : χ.1 ≠ 1) (hx : 3 ≤ x) :
    Integrable (eq17FirstCharacterIntegrand x d B k m H χ) :=
  (integrable_eq17OrigCharacterIntegrand (level := level) χ hd hχ hx).sub
    (integrable_eq17SecondAlphaCharacterIntegrand χ hd hχ hx)

private theorem integral_eq17SecondAlpha_eq_beta
    {x d B k m H : ℕ} [NeZero d] (χ : PrimitiveCharacter d)
    (hd : 1 < d) (hχ : χ.1 ≠ 1) (hx : 3 ≤ x) :
    (∫ t : ℝ, eq17SecondAlphaCharacterIntegrand x d B k m H χ t) =
      ∫ t : ℝ, eq17SecondBetaCharacterIntegrand x d B k m H χ t := by
  unfold eq17SecondAlphaCharacterIntegrand eq17SecondBetaCharacterIntegrand
  rw [integral_finsetSum (chen1973Lemma6PrimePairShell x B k m)]
  · rw [integral_finsetSum (chen1973Lemma6PrimePairShell x B k m)]
    · apply Finset.sum_congr rfl
      intro pp hpp
      obtain ⟨hp₁, hp₂⟩ := chen1973Lemma6PrimePairShell_pos hpp
      let y : ℝ := (x : ℝ) / ((pp.1 : ℝ) * pp.2)
      have hy : 0 < y := by positivity
      have hshift :=
        chen1973Lemma6_eq17_LDerivS_contour_shift_unconditional
          (H := H) χ hχ hx hy
      have hconst := congrArg
        (fun z : ℂ => (-(((Real.log y)⁻¹ : ℝ) : ℂ)) *
          z * χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d)) hshift
      simp only [chen1973PrimitiveLDeriv, dif_pos hd]
      calc
        _ =
            (-(((Real.log y)⁻¹ : ℝ) : ℂ)) *
              (∫ t : ℝ, chen1973VerticalSection
                (chen1973Lemma6Eq17ShiftIntegrand x H y χ)
                (chen1973Lemma6Alpha x) t) *
              χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) := by
                rw [← MeasureTheory.integral_const_mul,
                  ← MeasureTheory.integral_mul_const]
                apply integral_congr_ae
                exact ae_of_all _ fun t => by
                  unfold chen1973VerticalSection
                    chen1973Lemma6Eq17ShiftIntegrand
                  dsimp [y]
                  push_cast
                  ring
        _ = (-(((Real.log y)⁻¹ : ℝ) : ℂ)) *
              (∫ t : ℝ, chen1973VerticalSection
                (chen1973Lemma6Eq17ShiftIntegrand x H y χ)
                (chen1973Lemma6Beta x) t) *
              χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) := hconst
        _ = _ := by
                rw [← MeasureTheory.integral_const_mul,
                  ← MeasureTheory.integral_mul_const]
                apply integral_congr_ae
                exact ae_of_all _ fun t => by
                  unfold chen1973VerticalSection
                    chen1973Lemma6Eq17ShiftIntegrand
                  dsimp [y]
                  push_cast
                  ring
    · intro pp hpp
      obtain ⟨hp₁, hp₂⟩ := chen1973Lemma6PrimePairShell_pos hpp
      exact (integrable_eq17SecondPairIntegrand
          (H := H) χ hχ hx hp₁ hp₂
          (chen1973Lemma6Beta x) (Or.inr rfl)).congr
        (ae_of_all _ fun t => by
          unfold eq17SecondPairIntegrand
          simp only [chen1973PrimitiveLDeriv, dif_pos hd]
          )
  · intro pp hpp
    obtain ⟨hp₁, hp₂⟩ := chen1973Lemma6PrimePairShell_pos hpp
    exact (integrable_eq17SecondPairIntegrand
        (H := H) χ hχ hx hp₁ hp₂
        (chen1973Lemma6Alpha x) (Or.inl rfl)).congr
      (ae_of_all _ fun t => by
        unfold eq17SecondPairIntegrand
        simp only [chen1973PrimitiveLDeriv, dif_pos hd]
        )

private def eq17FirstScalarTerm
    (x d level B k m H : ℕ) (χ : PrimitiveCharacter d) (t : ℝ) : ℝ :=
  ‖chen1973Lemma6Eq17PairPolynomial x B k m
      (chen1973Lemma6Alpha x + t * I) χ‖ *
    ‖1 - chen1973Lemma6PrimitiveLValue d
        (chen1973Lemma6Alpha x + t * I) χ *
      chen1973Lemma6MobiusPartialSum H
        (chen1973Lemma6Alpha x + t * I) χ‖ /
    chen1973Lemma6Eq17CorrectedRadialKernel x level (chen1973Lemma6Alpha x + t * I)

private def eq17SecondScalarTerm
    (x d level B k m H : ℕ) (χ : PrimitiveCharacter d) (t : ℝ) : ℝ :=
  ‖chen1973Lemma6Eq17PairPolynomial x B k m
      (chen1973Lemma6Beta x + t * I) χ‖ *
    ‖chen1973PrimitiveLDeriv d (chen1973Lemma6Beta x + t * I) χ *
      chen1973Lemma6MobiusPartialSum H
        (chen1973Lemma6Beta x + t * I) χ‖ /
    chen1973Lemma6Eq17CorrectedRadialKernel x level (chen1973Lemma6Beta x + t * I)

private theorem alphaPrimePairSum_eq_integral
    {x d level B k m : ℕ} [NeZero d] (χ : PrimitiveCharacter d)
    (hd : 1 < d) (hχ : χ.1 ≠ 1) (hx : 3 ≤ x) :
    chen1973Lemma6AlphaNegLogDerivPrimePairSum x d B k m χ =
      ∫ t : ℝ, (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        eq17OrigCharacterIntegrand x d B k m χ t) := by
  unfold chen1973Lemma6AlphaNegLogDerivPrimePairSum
    chen1973Lemma6AlphaNegLogDerivIntegral eq17OrigCharacterIntegrand
  rw [MeasureTheory.integral_const_mul,
    integral_finsetSum (chen1973Lemma6PrimePairShell x B k m)]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro pp hpp
    rw [MeasureTheory.integral_mul_const,
      MeasureTheory.integral_const_mul]
    push_cast
    ring
  · intro pp hpp
    obtain ⟨hp₁, hp₂⟩ := chen1973Lemma6PrimePairShell_pos hpp
    exact (((integrable_alphaNegLogDerivIntegrand
      (level := level) χ hd hχ hx pp hp₁ hp₂).const_mul
        (((Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ : ℝ) : ℂ)).mul_const
          (χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d))).congr
            (ae_of_all _ fun _ => by push_cast; ring)

private theorem integral_orig_eq_first_add_secondBeta
    {x d level B k m H : ℕ} [NeZero d] (χ : PrimitiveCharacter d)
    (hd : 1 < d) (hχ : χ.1 ≠ 1) (hx : 3 ≤ x) :
    (∫ t : ℝ, (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      eq17OrigCharacterIntegrand x d B k m χ t)) =
      (∫ t : ℝ, (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        eq17FirstCharacterIntegrand x d B k m H χ t)) +
      ∫ t : ℝ, (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        eq17SecondBetaCharacterIntegrand x d B k m H χ t) := by
  have hfirst := integrable_eq17FirstCharacterIntegrand
    (level := level) (B := B) (k := k) (m := m) (H := H) χ hd hχ hx
  have hsecond := integrable_eq17SecondAlphaCharacterIntegrand
    (B := B) (k := k) (m := m) (H := H) χ hd hχ hx
  calc
    (∫ t : ℝ, (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      eq17OrigCharacterIntegrand x d B k m χ t)) =
        (∫ t : ℝ, (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          eq17FirstCharacterIntegrand x d B k m H χ t)) +
        ∫ t : ℝ, (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          eq17SecondAlphaCharacterIntegrand x d B k m H χ t) := by
            rw [← MeasureTheory.integral_add
              (hfirst.const_mul _) (hsecond.const_mul _)]
            apply integral_congr_ae
            exact ae_of_all _ fun t => by
              unfold eq17FirstCharacterIntegrand
              ring
    _ = _ := by
      simp_rw [MeasureTheory.integral_const_mul]
      rw [integral_eq17SecondAlpha_eq_beta χ hd hχ hx]

private theorem norm_normalized_first_le
    {x d level B k m H : ℕ} [NeZero d] (χ : PrimitiveCharacter d)
    (hd : 1 < d) (hχ : χ.1 ≠ 1) (hx : 3 ≤ x) (t : ℝ)
    (hlogDeriv :
      ‖chen1973PrimitiveLDeriv d (chen1973Lemma6Alpha x + t * I) χ /
        chen1973Lemma6PrimitiveLValue d
          (chen1973Lemma6Alpha x + t * I) χ‖ ≤ 6 * (Real.log x) ^ 2) :
    ‖(((1 / (2 * Real.pi) : ℝ) : ℂ) *
      eq17FirstCharacterIntegrand x d B k m H χ t)‖ ≤
      6 * x * (Real.log x) ^ 2 *
        eq17FirstScalarTerm x d level B k m H χ t := by
  rw [eq17FirstCharacterIntegrand_eq_collected χ hd hχ hx t]
  unfold eq17FirstScalarTerm
  have hk := norm_scaledKernel_alpha_le (level := level) hx t
  let D : ℝ :=
      ‖chen1973PrimitiveLDeriv d (chen1973Lemma6Alpha x + ↑t * I) χ /
        chen1973Lemma6PrimitiveLValue d
          (chen1973Lemma6Alpha x + ↑t * I) χ‖
  let C : ℝ :=
      ‖1 - chen1973Lemma6PrimitiveLValue d
          (chen1973Lemma6Alpha x + ↑t * I) χ *
        chen1973Lemma6MobiusPartialSum H
          (chen1973Lemma6Alpha x + ↑t * I) χ‖ *
      ‖chen1973Lemma6Eq17PairPolynomial x B k m
        (chen1973Lemma6Alpha x + ↑t * I) χ‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hquot : 0 ≤ (x : ℝ) /
      chen1973Lemma6Eq17CorrectedRadialKernel x level
        (chen1973Lemma6Alpha x + t * I) := by
    exact div_nonneg (by positivity)
      (chen1973Lemma6_eq17_correctedRadialKernel_pos
        (x := x) (level := level) (by omega : 1 < x) (alpha_pos hx)).le
  calc
    _ = (D * C) *
        ‖(((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (x : ℂ) ^ (chen1973Lemma6Alpha x + t * I) *
          chen1973MellinKernel (x : ℝ)
            (chen1973Lemma6Alpha x + t * I))‖ := by
              dsimp [C, D]
              simp only [norm_mul]
              simp only [norm_neg, norm_div, norm_inv]
              ring
    _ ≤ (D * C) * ((x : ℝ) /
          chen1973Lemma6Eq17CorrectedRadialKernel x level
            (chen1973Lemma6Alpha x + t * I)) :=
      mul_le_mul_of_nonneg_left hk (mul_nonneg hD hC)
    _ ≤ ((6 * (Real.log x) ^ 2) * C) * ((x : ℝ) /
          chen1973Lemma6Eq17CorrectedRadialKernel x level
            (chen1973Lemma6Alpha x + t * I)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hlogDeriv hC) hquot
    _ = _ := by dsimp [C, D]; ring

private theorem norm_normalized_second_le
    {x d level B k m H : ℕ} [NeZero d] (χ : PrimitiveCharacter d)
    (hd : 1 < d) (hx : 3 ≤ x) (t : ℝ) :
    ‖(((1 / (2 * Real.pi) : ℝ) : ℂ) *
      eq17SecondBetaCharacterIntegrand x d B k m H χ t)‖ ≤
      (x : ℝ) ^ ((1 : ℝ) / 2) *
        eq17SecondScalarTerm x d level B k m H χ t := by
  rw [eq17SecondBetaCharacterIntegrand_eq_collected χ hd hx t]
  unfold eq17SecondScalarTerm
  have hk := chen1973Lemma6_eq17_scaledKernel_beta_le_source (level := level) hx t
  let C : ℝ :=
      ‖chen1973PrimitiveLDeriv d (chen1973Lemma6Beta x + ↑t * I) χ *
          chen1973Lemma6MobiusPartialSum H
            (chen1973Lemma6Beta x + ↑t * I) χ‖ *
        ‖chen1973Lemma6Eq17PairPolynomial x B k m
          (chen1973Lemma6Beta x + ↑t * I) χ‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ = C *
        ‖(((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (x : ℂ) ^ (chen1973Lemma6Beta x + t * I) *
          chen1973MellinKernel (x : ℝ)
            (chen1973Lemma6Beta x + t * I))‖ := by
              dsimp [C]
              simp only [norm_mul, norm_neg]
              ring
    _ ≤ C * ((x : ℝ) ^ ((1 : ℝ) / 2) /
          chen1973Lemma6Eq17CorrectedRadialKernel x level
            (chen1973Lemma6Beta x + t * I)) :=
      mul_le_mul_of_nonneg_left hk hC
    _ = _ := by dsimp [C]; simp only [norm_mul]; ring

private theorem norm_logCpowWeight_le_two
    {σ t : ℝ} (hσ : 1 / 2 ≤ σ) (n : ℕ) :
    ‖logCpowWeight (σ + I * t) n‖ ≤ 2 := by
  by_cases hn : n = 0
  · simp [hn, logCpowWeight, cpowWeight]
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hnR
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hlogUpper := Real.log_le_rpow_div (x := (n : ℝ))
    (Nat.cast_nonneg n) (by norm_num : (0 : ℝ) < 1 / 2)
  have hpow :
      (n : ℝ) ^ (1 / 2 : ℝ) ≤ (n : ℝ) ^ σ :=
    Real.rpow_le_rpow_of_exponent_le hnR hσ
  unfold logCpowWeight cpowWeight
  rw [norm_mul, norm_neg, norm_real, Real.norm_eq_abs,
    abs_of_nonneg hlog, Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
  simp only [neg_re, add_re, ofReal_re, mul_re, I_re, zero_mul,
    ofReal_im, I_im, mul_one, sub_self, add_zero]
  norm_num
  rw [Real.rpow_neg (Nat.cast_nonneg n)]
  calc
    Real.log (n : ℝ) * ((n : ℝ) ^ σ)⁻¹
        ≤ (2 * (n : ℝ) ^ (1 / 2 : ℝ)) *
            ((n : ℝ) ^ σ)⁻¹ := by
          gcongr
          simpa [div_eq_mul_inv, mul_comm] using hlogUpper
    _ ≤ 2 := by
      have hp : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hnpos _
      have hab :
          (n : ℝ) ^ (1 / 2 : ℝ) * ((n : ℝ) ^ σ)⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one hp]
        exact hpow
      calc
        _ = 2 * ((n : ℝ) ^ (1 / 2 : ℝ) * ((n : ℝ) ^ σ)⁻¹) := by ring
        _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left hab (by norm_num)
        _ = 2 := by norm_num

private theorem norm_logCpowWeight_mul_character_le_two
    {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d)
    {σ t : ℝ} (hσ : 1 / 2 ≤ σ) (n : ℕ) :
    ‖logCpowWeight (σ + I * t) n * χ n‖ ≤ 2 := by
  rw [norm_mul]
  calc
    _ ≤ 2 * 1 := mul_le_mul
      (norm_logCpowWeight_le_two hσ n) (χ.norm_le_one n)
      (norm_nonneg _) (by norm_num)
    _ = 2 := by norm_num

private theorem norm_deriv_LFunction_beta_sublinear
    {x d : ℕ} [NeZero d] (χ : PrimitiveCharacter d)
    (hχ : χ.1 ≠ 1) (hx : 3 ≤ x) (t : ℝ) :
    ‖deriv χ.1.LFunction (chen1973Lemma6Beta x + I * t)‖ ≤
      24 * ((d : ℝ) + 1) *
        (1 + |t|) ^ (1 - 1 / (2 * Real.log x)) := by
  let δ : ℝ := 1 / Real.log x
  let β : ℝ := 1 / 2 + δ
  let U : ℝ := 1 + |t|
  let r : ℝ := Real.sqrt U
  let M : ℕ := ⌈r⌉₊
  let p : ℝ := 1 - δ / 2
  have hlog1 : (1 : ℝ) ≤ Real.log x :=
    (chen1973Lemma6_eq17_one_le_log_and_order hx).1
  have hlog : 0 < Real.log x := zero_lt_one.trans_le hlog1
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hδle : δ ≤ 1 := by
    dsimp [δ]
    exact (div_le_one hlog).2 hlog1
  have hβhalf : 1 / 2 ≤ β := by dsimp [β]; linarith
  have hβpos : 0 < β := lt_of_lt_of_le (by norm_num) hβhalf
  have hpHalf : 1 / 2 ≤ p := by dsimp [p]; linarith
  have hp0 : 0 ≤ p := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans hpHalf
  have hp1 : p < 1 := by dsimp [p]; linarith
  have hU1 : 1 ≤ U := by dsimp [U]; linarith [abs_nonneg t]
  have hUpos : 0 < U := zero_lt_one.trans_le hU1
  have hr1 : 1 ≤ r := by
    dsimp [r]
    simpa using Real.sqrt_le_sqrt hU1
  have hMlower : r ≤ (M : ℝ) := by
    dsimp [M]
    exact Nat.le_ceil r
  have hM1 : 1 ≤ M := by
    exact_mod_cast hr1.trans hMlower
  have hMR1 : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hMpos : (0 : ℝ) < M := zero_lt_one.trans_le hMR1
  have hMupper : (M : ℝ) ≤ 2 * r :=
    (Nat.ceil_lt_two_mul (lt_of_lt_of_le (by norm_num) hr1)).le
  let s : ℂ := β + I * t
  have hsre : s.re = β := by simp [s]
  have hspos : 0 < s.re := by rw [hsre]; exact hβpos
  have hseries :=
    orderedLogDerivativeSeries_eq_deriv_LFunction_of_re_pos
      χ.1 hχ s hspos
  have htail :=
    norm_orderedLogDerivativeSeries_sub_sum_range_le
      χ.1 hχ s hspos (m := M) hM1
  rw [hseries] at htail
  have hprefix :
      ‖∑ n ∈ range M, logCpowWeight s n * χ.1 n‖ ≤ 2 * M := by
    calc
      _ ≤ ∑ n ∈ range M, ‖logCpowWeight s n * χ.1 n‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _n ∈ range M, (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        simpa [s, hsre] using
          norm_logCpowWeight_mul_character_le_two χ.1 hβhalf n
      _ = 2 * M := by simp [mul_comm]
  have hsNorm : ‖s‖ ≤ 2 * U := by
    calc
      ‖s‖ ≤ ‖(β : ℂ)‖ + ‖I * (t : ℂ)‖ := by
        dsimp [s]
        exact norm_add_le _ _
      _ = |β| + |t| := by simp
      _ ≤ 2 * U := by
        rw [abs_of_pos hβpos]
        dsimp [β, U]
        have : δ ≤ 1 := hδle
        linarith [abs_nonneg t]
  have hMnegδ :
      (M : ℝ) ^ (-δ) ≤ U ^ (-δ / 2) := by
    have hrpos : 0 < r := zero_lt_one.trans_le hr1
    calc
      (M : ℝ) ^ (-δ) ≤ r ^ (-δ) :=
        Real.rpow_le_rpow_of_nonpos hrpos hMlower (by linarith)
      _ = U ^ (-δ / 2) := by
        rw [show r = U ^ (1 / 2 : ℝ) by
          simp only [r, Real.sqrt_eq_rpow]]
        rw [← Real.rpow_mul hUpos.le]
        congr 1
        ring
  have hMbeta :
      (M : ℝ) ^ (-β) ≤ (M : ℝ) ^ (-δ) :=
    Real.rpow_le_rpow_of_exponent_le hMR1 (by dsimp [β]; linarith)
  have hlogM :
      Real.log (M : ℝ) ≤ 2 * (M : ℝ) ^ (1 / 2 : ℝ) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (Real.log_le_rpow_div (x := (M : ℝ)) (by positivity)
        (by norm_num : (0 : ℝ) < 1 / 2))
  have hMbetaLog :
      (M : ℝ) ^ (-β) * Real.log (M : ℝ) ≤
        2 * (M : ℝ) ^ (-δ) := by
    calc
      _ ≤ (M : ℝ) ^ (-β) *
          (2 * (M : ℝ) ^ (1 / 2 : ℝ)) := by
            gcongr
      _ = 2 * (M : ℝ) ^ (-δ) := by
        rw [show (M : ℝ) ^ (-β) * (2 * (M : ℝ) ^ (1 / 2 : ℝ)) =
          2 * ((M : ℝ) ^ (-β) * (M : ℝ) ^ (1 / 2 : ℝ)) by ring]
        rw [← Real.rpow_add hMpos]
        dsimp [β]
        ring_nf
  have hbudget :
      logVariationBudget s M ≤ 18 * U ^ p := by
    have hβinv : 1 / β ≤ 2 := by
      rw [div_le_iff₀ hβpos]
      nlinarith
    have hβinvSq : 1 / β ^ 2 ≤ 4 := by
      rw [div_le_iff₀ (sq_pos_of_pos hβpos)]
      nlinarith
    have hUp : 1 ≤ U ^ p := Real.one_le_rpow hU1 hp0
    have hnegToP : U ^ (-δ / 2) ≤ U ^ p :=
      Real.rpow_le_rpow_of_exponent_le hU1 (by dsimp [p]; linarith)
    have hmul :
        U * U ^ (-δ / 2) = U ^ p := by
      calc
        U * U ^ (-δ / 2) =
            U ^ (1 : ℝ) * U ^ (-δ / 2) := by rw [Real.rpow_one]
        _ = U ^ ((1 : ℝ) + (-δ / 2)) := (Real.rpow_add hUpos _ _).symm
        _ = U ^ p := by
          congr 1
          dsimp [p]
          ring
    rw [logVariationBudget, hsre]
    change (M : ℝ) ^ (-β) *
      (1 / β + ‖s‖ * (Real.log (M : ℝ) / β + 1 / β ^ 2)) ≤ _
    have ht1 :
        (M : ℝ) ^ (-β) * (1 / β) ≤
          2 * (M : ℝ) ^ (-δ) := by
      calc
        _ ≤ (M : ℝ) ^ (-δ) * 2 :=
          mul_le_mul hMbeta hβinv (by positivity) (by positivity)
        _ = _ := by ring
    have ht2 :
        ‖s‖ * ((M : ℝ) ^ (-β) * Real.log (M : ℝ)) * (1 / β) ≤
          ‖s‖ * (2 * (M : ℝ) ^ (-δ)) * 2 := by
      gcongr
    have ht3 :
        ‖s‖ * (M : ℝ) ^ (-β) * (1 / β ^ 2) ≤
          ‖s‖ * (M : ℝ) ^ (-δ) * 4 := by
      gcongr
    calc
      _ = (M : ℝ) ^ (-β) * (1 / β) +
          ‖s‖ * ((M : ℝ) ^ (-β) * Real.log (M : ℝ)) * (1 / β) +
          ‖s‖ * (M : ℝ) ^ (-β) * (1 / β ^ 2) := by ring
      _ ≤ 2 * (M : ℝ) ^ (-δ) +
          ‖s‖ * (2 * (M : ℝ) ^ (-δ)) * 2 +
          ‖s‖ * (M : ℝ) ^ (-δ) * 4 :=
        add_le_add (add_le_add ht1 ht2) ht3
      _ = 2 * (M : ℝ) ^ (-δ) +
          ‖s‖ * (2 * (2 * (M : ℝ) ^ (-δ)) +
            4 * (M : ℝ) ^ (-δ)) := by ring
      _ ≤ 2 * U ^ (-δ / 2) +
          (2 * U) * (2 * (2 * U ^ (-δ / 2)) +
            4 * U ^ (-δ / 2)) := by
              have hi :
                  2 * (2 * (M : ℝ) ^ (-δ)) +
                      4 * (M : ℝ) ^ (-δ) ≤
                    2 * (2 * U ^ (-δ / 2)) +
                      4 * U ^ (-δ / 2) := by
                gcongr
              exact add_le_add
                (mul_le_mul_of_nonneg_left hMnegδ (by norm_num))
                (mul_le_mul hsNorm hi (by positivity) (by positivity))
      _ = 2 * U ^ (-δ / 2) + 16 * U * U ^ (-δ / 2) := by ring
      _ = 2 * U ^ (-δ / 2) + 16 * (U * U ^ (-δ / 2)) := by ring
      _ = 2 * U ^ (-δ / 2) + 16 * U ^ p := by rw [hmul]
      _ ≤ 18 * U ^ p := by
        nlinarith
  have hprefixFinal : (2 : ℝ) * M ≤ 4 * U ^ p := by
    calc
      (2 : ℝ) * M ≤ 4 * r := by nlinarith [hMupper]
      _ = 4 * U ^ (1 / 2 : ℝ) := by rw [← Real.sqrt_eq_rpow]
      _ ≤ 4 * U ^ p := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hU1 hpHalf) (by norm_num)
  have htailFinal :
      ‖deriv χ.1.LFunction s -
          ∑ n ∈ range M, logCpowWeight s n * χ.1 n‖ ≤
        20 * d * U ^ p := by
    calc
      _ ≤ (d : ℝ) *
          (‖logCpowWeight s M‖ + logVariationBudget s M) := htail
      _ ≤ (d : ℝ) * (2 + 18 * U ^ p) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add
          (by simpa [s] using norm_logCpowWeight_le_two hβhalf M)
          hbudget
      _ ≤ 20 * d * U ^ p := by
        have hd0 : (0 : ℝ) ≤ d := by positivity
        have hUp : 1 ≤ U ^ p := Real.one_le_rpow hU1 hp0
        nlinarith
  change ‖deriv χ.1.LFunction s‖ ≤ _
  calc
    _ ≤ ‖∑ n ∈ range M, logCpowWeight s n * χ.1 n‖ +
          ‖deriv χ.1.LFunction s -
            ∑ n ∈ range M, logCpowWeight s n * χ.1 n‖ := by
          have := norm_add_le
            (∑ n ∈ range M, logCpowWeight s n * χ.1 n)
            (deriv χ.1.LFunction s -
              ∑ n ∈ range M, logCpowWeight s n * χ.1 n)
          convert this using 1 <;> ring
    _ ≤ 4 * U ^ p + 20 * d * U ^ p :=
      add_le_add (hprefix.trans hprefixFinal) htailFinal
    _ ≤ 24 * ((d : ℝ) + 1) * U ^ p := by
      have hd0 : (0 : ℝ) ≤ d := by positivity
      have hUp0 : 0 ≤ U ^ p := Real.rpow_nonneg hUpos.le _
      nlinarith
    _ = 24 * ((d : ℝ) + 1) *
        (1 + |t|) ^ (1 - 1 / (2 * Real.log x)) := by
      dsimp [U, p, δ]
      congr 2
      ring

set_option maxHeartbeats 3000000 in
private theorem integrable_one_add_abs_rpow {a : ℝ} (ha : a < -1) :
    Integrable (fun t : ℝ => (1 + |t|) ^ a) := by
  have hpos0 : IntegrableOn (fun t : ℝ => (t + 1) ^ a) (Ioi 0) :=
    integrableOn_add_rpow_Ioi_of_lt (a := a) (c := 0) (m := 1) ha (by norm_num)
  have hbase : IntegrableOn (fun t : ℝ => (t + 1) ^ a) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 hpos0
  have hpos : IntegrableOn (fun t : ℝ => (1 + |t|) ^ a) (Ici 0) := by
    exact hbase.congr_fun (fun t ht => by
      rw [abs_of_nonneg (mem_Ici.mp ht)]
      congr 1
      ring) measurableSet_Ici
  have hneg : IntegrableOn (fun t : ℝ => (1 + |t|) ^ a) (Iic 0) := by
    have hbase' : IntegrableOn (fun t : ℝ => (t + 1) ^ a) (Ici (-(0 : ℝ))) := by
      simpa using hbase
    have h : IntegrableOn (fun t : ℝ => ((-t) + 1) ^ a) (Iic 0) :=
      IntegrableOn.comp_neg_Iic
        (f := fun t : ℝ => (t + 1) ^ a) (μ := volume)
        (c := (0 : ℝ)) hbase'
    exact h.congr_fun (fun t ht => by
      rw [abs_of_nonpos (mem_Iic.mp ht)]
      congr 1
      ring) measurableSet_Iic
  rw [← integrableOn_univ, ← Iic_union_Ici (a := (0 : ℝ))]
  exact hneg.union hpos

private theorem integrable_growth_div_radialKernel
    {x level : ℕ} (hx : 3 ≤ x) {σ p : ℝ}
    (hσ : 0 < σ) (hp : p < 1) :
    Integrable (fun t : ℝ =>
      (1 + |t|) ^ p /
        eq17LinearKernel x (σ + t * I)) := by
  let A : ℝ := chen1973PerronScale (x : ℝ)
  let C : ℝ := σ⁻¹ + 2 + A
  have hA : 0 < A := chen1973Lemma6_eq17_perronScale_pos (by omega : 1 < x)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hdom : Integrable (fun t : ℝ =>
      C * (1 + |t|) ^ (p - 2)) :=
    (integrable_one_add_abs_rpow (by linarith)).const_mul C
  have hmeas : AEStronglyMeasurable (fun t : ℝ =>
      (1 + |t|) ^ p /
        eq17LinearKernel x (σ + t * I)) := by
    apply Continuous.aestronglyMeasurable
    apply Continuous.div
    · exact (continuous_const.add continuous_abs).rpow_const
        (fun t => Or.inl (show 1 + |t| ≠ 0 by positivity))
    · unfold eq17LinearKernel
      fun_prop
    · intro t
      exact (eq17LinearKernel_pos
        (x := x) (by omega : 1 < x) hσ (v := t)).ne'
  apply Integrable.mono' hdom hmeas
  filter_upwards with t
  let U : ℝ := 1 + |t|
  let N : ℝ := ‖(σ + t * I : ℂ)‖
  let K : ℝ := eq17LinearKernel x (σ + t * I)
  have hU : 0 < U := by dsimp [U]; positivity
  have hNσ : σ ≤ N := by
    calc
      σ = |σ| := (abs_of_pos hσ).symm
      _ ≤ N := by
        simpa [N] using Complex.abs_re_le_norm (σ + t * I : ℂ)
  have hNt : |t| ≤ N := by
    have hi := Complex.abs_im_le_norm (σ + t * I : ℂ)
    simpa [N] using hi
  have hN : 0 < N := hσ.trans_le hNσ
  have hK :
      K = N * (1 + N / A) := by
    dsimp [K, N]
    unfold eq17LinearKernel
    rfl
  have hKpos : 0 < K := by rw [hK]; positivity
  have hNone : 1 ≤ σ⁻¹ * K := by
    rw [hK]
    have hσK : σ ≤ N * (1 + N / A) := by
      calc
        σ ≤ N := hNσ
        _ = N * 1 := by ring
        _ ≤ N * (1 + N / A) :=
          mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right (div_nonneg hN.le hA.le)) hN.le
    calc
      1 = σ⁻¹ * σ := by field_simp
      _ ≤ σ⁻¹ * (N * (1 + N / A)) :=
        mul_le_mul_of_nonneg_left hσK (inv_nonneg.mpr hσ.le)
  have hNlin : 2 * |t| ≤ 2 * K := by
    have hNK : N ≤ K := by
      rw [hK]
      calc
        N = N * 1 := by ring
        _ ≤ N * (1 + N / A) :=
          mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right (div_nonneg hN.le hA.le)) hN.le
    linarith
  have hNsq : t ^ 2 ≤ A * K := by
    have htN : t ^ 2 ≤ N ^ 2 := by
      nlinarith [hNt, abs_nonneg t, sq_abs t]
    rw [hK]
    have hNN : N ^ 2 ≤ A * (N * (1 + N / A)) := by
      field_simp [hA.ne']
      nlinarith [hN.le]
    exact htN.trans hNN
  have hUK : U ^ 2 ≤ C * K := by
    dsimp [U, C]
    have habssq : |t| ^ 2 = t ^ 2 := sq_abs t
    nlinarith
  have hquot :
      U ^ p / K ≤ C * U ^ (p - 2) := by
    have hU2 : 0 < U ^ 2 := sq_pos_of_pos hU
    rw [div_le_iff₀ hKpos]
    calc
      U ^ p = U ^ (p - 2) * U ^ 2 := by
        rw [← Real.rpow_natCast U 2, ← Real.rpow_add hU]
        ring_nf
      _ ≤ U ^ (p - 2) * (C * K) :=
        mul_le_mul_of_nonneg_left hUK (Real.rpow_nonneg hU.le _)
      _ = (C * U ^ (p - 2)) * K := by ring
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg
    (Real.rpow_nonneg hU.le _) hKpos.le)]
  simpa [U, K] using hquot

private theorem integrable_growth_div_eq17Kernel
    {x level : ℕ} (hx : 3 ≤ x) {σ p : ℝ}
    (hσ : 0 < σ) (hp : p < 1) :
    Integrable (fun t : ℝ =>
      (1 + |t|) ^ p /
        chen1973Lemma6Eq17CorrectedRadialKernel x level (σ + t * I)) := by
  have hold := integrable_growth_div_radialKernel
    (x := x) (level := level) hx hσ hp
  have hdom : Integrable (fun t : ℝ => 2 *
      ((1 + |t|) ^ p /
        eq17LinearKernel x (σ + t * I))) :=
    hold.const_mul 2
  have hmeas : AEStronglyMeasurable (fun t : ℝ =>
      (1 + |t|) ^ p /
        chen1973Lemma6Eq17CorrectedRadialKernel x level (σ + t * I)) := by
    apply Continuous.aestronglyMeasurable
    apply Continuous.div
    · exact (continuous_const.add continuous_abs).rpow_const
        (fun t => Or.inl (show 1 + |t| ≠ 0 by positivity))
    · unfold chen1973Lemma6Eq17CorrectedRadialKernel chen1973Lemma6Eq17CorrectedKernel
      fun_prop
    · intro t
      exact (chen1973Lemma6_eq17_correctedRadialKernel_pos
        (x := x) (level := level) (by omega : 1 < x) hσ (v := t)).ne'
  apply Integrable.mono' hdom hmeas
  filter_upwards with t
  have hs : 0 ≤ (σ + t * I : ℂ).re := by simpa using hσ.le
  have hsource := chen1973Lemma6_eq17_correctedRadialKernel_pos
    (x := x) (level := level) (by omega : 1 < x) hσ (v := t)
  have hradial := eq17LinearKernel_pos
    (x := x) (by omega : 1 < x) hσ (v := t)
  have hinv := chen1973Lemma6_eq17_correctedRadialKernel_inv_le_two_radialKernel_inv
    (x := x) (level := level) hx hsource hradial
  have hnum : 0 ≤ (1 + |t|) ^ p := Real.rpow_nonneg (by positivity) _
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnum hsource.le)]
  calc
    (1 + |t|) ^ p /
        chen1973Lemma6Eq17CorrectedRadialKernel x level (σ + t * I) =
      (1 + |t|) ^ p *
        (chen1973Lemma6Eq17CorrectedRadialKernel x level (σ + t * I))⁻¹ := by
          rw [div_eq_mul_inv]
    _ ≤ (1 + |t|) ^ p * (2 * (eq17LinearKernel x (σ + t * I))⁻¹) :=
      mul_le_mul_of_nonneg_left hinv hnum
    _ = 2 * ((1 + |t|) ^ p / eq17LinearKernel x (σ + t * I)) := by
      rw [div_eq_mul_inv]
      ring

private def eq17PairNormBound
    (x d B k m : ℕ) (χ : PrimitiveCharacter d) (σ : ℝ) : ℝ :=
  ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
    ‖χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) /
      ((pp.1 * pp.2 : ℂ) ^ (σ : ℂ) *
        Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))‖

private theorem norm_pairPolynomial_line_le
    {x d B k m : ℕ} (χ : PrimitiveCharacter d) (σ t : ℝ) :
    ‖chen1973Lemma6Eq17PairPolynomial x B k m (σ + t * I) χ‖ ≤
      eq17PairNormBound x d B k m χ σ := by
  unfold chen1973Lemma6Eq17PairPolynomial eq17PairNormBound
  calc
    _ ≤ ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
        ‖χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) /
          ((pp.1 * pp.2 : ℂ) ^ (σ + t * I) *
            Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))‖ :=
      norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro pp hpp
      obtain ⟨hp₁, hp₂⟩ := chen1973Lemma6PrimePairShell_pos hpp
      rw [norm_div, norm_div, norm_mul, norm_mul]
      congr 2
      rw [show (pp.1 * pp.2 : ℂ) =
        ((((pp.1 * pp.2 : ℕ) : ℝ) : ℂ)) by push_cast; rfl]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
        Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
      simp

private def eq17MobiusNormBound
    (d H : ℕ) (χ : PrimitiveCharacter d) (σ : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 H,
    ‖((ArithmeticFunction.moebius n : ℤ) : ℂ) *
      χ.1 (n : ZMod d) / (n : ℂ) ^ (σ : ℂ)‖

private theorem norm_mobiusPartialSum_line_le
    {d H : ℕ} (χ : PrimitiveCharacter d) (σ t : ℝ) :
    ‖chen1973Lemma6MobiusPartialSum H (σ + t * I) χ‖ ≤
      eq17MobiusNormBound d H χ σ := by
  unfold chen1973Lemma6MobiusPartialSum eq17MobiusNormBound
  calc
    _ ≤ ∑ n ∈ Icc 1 H,
        ‖((ArithmeticFunction.moebius n : ℤ) : ℂ) *
          χ.1 (n : ZMod d) / (n : ℂ) ^ (σ + t * I)‖ :=
      norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnpos : (0 : ℝ) < n := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1)
      rw [norm_div, norm_div]
      congr 1
      change ‖(((n : ℝ) : ℂ) ^ (σ + t * I))‖ =
        ‖(((n : ℝ) : ℂ) ^ (σ : ℂ))‖
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hnpos,
        Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
      simp

private def eq17AlphaLogDerivBound
    (x d : ℕ) (χ : PrimitiveCharacter d) : ℝ :=
  ∑' n : ℕ, ‖DirichletCharacter.twistedVonMangoldtCoeff χ.1 n /
    (n : ℂ) ^ ((chen1973Lemma6Alpha x : ℝ) : ℂ)‖

private theorem norm_alpha_logDeriv_le
    {x d : ℕ} [NeZero d] (χ : PrimitiveCharacter d)
    (hx : 3 ≤ x) (t : ℝ) :
    ‖-deriv χ.1.LFunction (chen1973Lemma6Alpha x + t * I) /
        χ.1.LFunction (chen1973Lemma6Alpha x + t * I)‖ ≤
      eq17AlphaLogDerivBound x d χ := by
  have hα : 1 < chen1973Lemma6Alpha x := by
    unfold chen1973Lemma6Alpha
    have hlog : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < x by omega))
    linarith [one_div_pos.mpr hlog]
  rw [DirichletCharacter.neg_logDeriv_LFunction_eq_tsum_twistedVonMangoldtCoeff
    χ.1 (by simpa using hα)]
  have hs := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ.1
    (by simpa only [Complex.ofReal_re] using hα :
      1 < (((chen1973Lemma6Alpha x : ℝ) : ℂ)).re)
  rw [LSeriesSummable] at hs
  have hnormeq (n : ℕ) :
      ‖DirichletCharacter.twistedVonMangoldtCoeff χ.1 n /
          (n : ℂ) ^ (chen1973Lemma6Alpha x + t * I)‖ =
        ‖DirichletCharacter.twistedVonMangoldtCoeff χ.1 n /
          (n : ℂ) ^ ((chen1973Lemma6Alpha x : ℝ) : ℂ)‖ := by
    by_cases hn : n = 0
    · simp [hn, DirichletCharacter.twistedVonMangoldtCoeff, LSeries.term]
    · rw [norm_div, norm_div,
        Complex.norm_natCast_cpow_of_re_ne_zero,
        Complex.norm_natCast_cpow_of_re_ne_zero]
      · simp
      · simpa only [Complex.ofReal_re] using ne_of_gt (zero_lt_one.trans hα)
      · simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
          sub_zero, add_zero] using ne_of_gt (zero_lt_one.trans hα)
  have hfixed : Summable (fun n : ℕ =>
      ‖DirichletCharacter.twistedVonMangoldtCoeff χ.1 n /
        (n : ℂ) ^ ((chen1973Lemma6Alpha x : ℝ) : ℂ)‖) := by
    apply Summable.congr hs.norm
    intro n
    by_cases hn : n = 0
    · simp [hn, DirichletCharacter.twistedVonMangoldtCoeff, LSeries.term]
    · simp [LSeries.term, hn,
        DirichletCharacter.twistedVonMangoldtCoeff, mul_comm]
  have hcurrent : Summable (fun n : ℕ =>
      ‖DirichletCharacter.twistedVonMangoldtCoeff χ.1 n /
        (n : ℂ) ^ (chen1973Lemma6Alpha x + t * I)‖) :=
    hfixed.congr (fun n => (hnormeq n).symm)
  calc
    _ ≤ ∑' n : ℕ,
        ‖DirichletCharacter.twistedVonMangoldtCoeff χ.1 n /
          (n : ℂ) ^ (chen1973Lemma6Alpha x + t * I)‖ :=
      norm_tsum_le_tsum_norm hcurrent
    _ = eq17AlphaLogDerivBound x d χ := by
      unfold eq17AlphaLogDerivBound
      exact tsum_congr hnormeq

/-- On Chen's alpha line, the absolute twisted von Mangoldt series pays the
logarithmic derivative with the explicit universal constant `6`. -/
theorem chen1973Lemma6_alphaLogDerivative_le_six_mul_log_sq
    {x d : ℕ} [NeZero d] (χ : PrimitiveCharacter d)
    (hd : 1 < d) (hx : 3 ≤ x) (t : ℝ) :
    ‖chen1973PrimitiveLDeriv d (chen1973Lemma6Alpha x + t * I) χ /
        chen1973Lemma6PrimitiveLValue d
          (chen1973Lemma6Alpha x + t * I) χ‖ ≤
      6 * (Real.log x) ^ 2 := by
  have hlog : 1 ≤ Real.log (x : ℝ) := by
    have hxR : Real.exp 1 ≤ (x : ℝ) := by
      have he3 : Real.exp 1 < 3 :=
        Real.exp_one_lt_d9.trans (by norm_num)
      exact he3.le.trans (by exact_mod_cast hx)
    calc
      (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (x : ℝ) := Real.log_le_log (Real.exp_pos 1) hxR
  have hlogpos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le zero_lt_one hlog
  let σ : ℝ := 1 + 1 / (2 * Real.log x)
  have hσ : 1 < σ := by
    dsimp [σ]
    linarith [one_div_pos.mpr (mul_pos two_pos hlogpos)]
  have hα : 1 < chen1973Lemma6Alpha x := by
    unfold chen1973Lemma6Alpha
    linarith [one_div_pos.mpr hlogpos]
  have habs : Summable (fun n : ℕ =>
      ‖DirichletCharacter.twistedVonMangoldtCoeff χ.1 n /
        (n : ℂ) ^ ((chen1973Lemma6Alpha x : ℝ) : ℂ)‖) := by
    have hs := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ.1
      (by simpa only [Complex.ofReal_re] using hα :
        1 < (((chen1973Lemma6Alpha x : ℝ) : ℂ)).re)
    rw [LSeriesSummable] at hs
    apply Summable.congr hs.norm
    intro n
    by_cases hn : n = 0
    · simp [hn, DirichletCharacter.twistedVonMangoldtCoeff, LSeries.term]
    · simp [LSeries.term, hn,
        DirichletCharacter.twistedVonMangoldtCoeff, mul_comm]
  have hseries : eq17AlphaLogDerivBound x d χ ≤
      (2 * Real.log x) * (∑' n : ℕ, (n : ℝ) ^ (-σ)) := by
    unfold eq17AlphaLogDerivBound
    rw [← tsum_mul_left]
    apply Summable.tsum_le_tsum
    · intro n
      by_cases hn : n = 0
      · simp [hn, DirichletCharacter.twistedVonMangoldtCoeff]
        positivity
      have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      rw [norm_div, Complex.norm_natCast_cpow_of_re_ne_zero]
      · rw [DirichletCharacter.twistedVonMangoldtCoeff, norm_mul,
          Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        calc
          ArithmeticFunction.vonMangoldt n * ‖χ.1 (n : ZMod d)‖ /
                (n : ℝ) ^ chen1973Lemma6Alpha x ≤
              ArithmeticFunction.vonMangoldt n /
                (n : ℝ) ^ chen1973Lemma6Alpha x := by
            gcongr
            simpa using mul_le_mul_of_nonneg_left
              (χ.1.norm_le_one (n : ZMod d))
              (ArithmeticFunction.vonMangoldt_nonneg (n := n))
          _ ≤ Real.log n / (n : ℝ) ^ chen1973Lemma6Alpha x := by
            gcongr
            exact ArithmeticFunction.vonMangoldt_le_log
          _ ≤ ((n : ℝ) ^ (1 / (2 * Real.log x)) /
                (1 / (2 * Real.log x))) /
                (n : ℝ) ^ chen1973Lemma6Alpha x := by
            gcongr
            exact Real.log_le_rpow_div (Nat.cast_nonneg n) (by positivity)
          _ = (2 * Real.log x) * (n : ℝ) ^ (-σ) := by
            have heps : (1 / (2 * Real.log x))⁻¹ = 2 * Real.log x := by
              field_simp
            calc
              ((n : ℝ) ^ (1 / (2 * Real.log x)) /
                    (1 / (2 * Real.log x))) /
                    (n : ℝ) ^ chen1973Lemma6Alpha x =
                  (1 / (2 * Real.log x))⁻¹ *
                    ((n : ℝ) ^ (1 / (2 * Real.log x)) /
                      (n : ℝ) ^ chen1973Lemma6Alpha x) := by ring
              _ = (2 * Real.log x) *
                    (n : ℝ) ^ (1 / (2 * Real.log x) -
                      chen1973Lemma6Alpha x) := by
                    rw [heps, Real.rpow_sub hnpos]
              _ = _ := by
                    congr 1
                    dsimp [σ, chen1973Lemma6Alpha]
                    ring
      · simpa only [Complex.ofReal_re] using
          ne_of_gt (zero_lt_one.trans hα)
    · exact habs
    · exact (Real.summable_nat_rpow.mpr (by linarith [hσ])).mul_left _
  have hzeta := tsum_nat_rpow_neg_le σ hσ
  calc
    _ ≤ eq17AlphaLogDerivBound x d χ := by
      simpa [chen1973PrimitiveLDeriv, chen1973Lemma6PrimitiveLValue,
        dif_pos hd] using
        norm_alpha_logDeriv_le χ hx t
    _ ≤ (2 * Real.log x) * (∑' n : ℕ, (n : ℝ) ^ (-σ)) := hseries
    _ ≤ (2 * Real.log x) * (1 + 1 / (σ - 1)) := by gcongr
    _ ≤ 6 * (Real.log x) ^ 2 := by
      dsimp [σ]
      field_simp
      nlinarith [sq_nonneg (Real.log x - 1)]

private theorem continuous_pairPolynomial_line
    {x d B k m : ℕ} (χ : PrimitiveCharacter d) (σ : ℝ) :
    Continuous (fun t : ℝ =>
      chen1973Lemma6Eq17PairPolynomial x B k m (σ + t * I) χ) := by
  unfold chen1973Lemma6Eq17PairPolynomial
  apply continuous_finset_sum
  intro pp hpp
  obtain ⟨hp₁, hp₂⟩ := chen1973Lemma6PrimePairShell_pos hpp
  by_cases hlog :
      Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)) = 0
  · simpa [hlog] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  · apply Continuous.div continuous_const
    · exact Continuous.mul
        (by fun_prop (disch := exact Or.inl (by
          exact_mod_cast (Nat.mul_pos hp₁ hp₂).ne')))
        continuous_const
    · intro t
      exact mul_ne_zero
        (Complex.cpow_ne_zero_iff.mpr (Or.inl (by
          exact_mod_cast (Nat.mul_pos hp₁ hp₂).ne')))
        (ofReal_ne_zero.mpr hlog)

private theorem continuous_mobiusPartialSum_line
    {d H : ℕ} (χ : PrimitiveCharacter d) (σ : ℝ) :
    Continuous (fun t : ℝ =>
      chen1973Lemma6MobiusPartialSum H (σ + t * I) χ) := by
  unfold chen1973Lemma6MobiusPartialSum
  apply continuous_finset_sum
  intro n hn
  have hnpos : 0 < n :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1
  apply Continuous.div continuous_const
  · fun_prop (disch := exact Or.inl (by exact_mod_cast hnpos.ne'))
  · intro t
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hnpos.ne'))

private theorem integrable_eq17FirstScalarTerm
    {x d level B k m H : ℕ} [NeZero d] (χ : PrimitiveCharacter d)
    (hd : 1 < d) (hχ : χ.1 ≠ 1) (hx : 3 ≤ x) :
    Integrable (eq17FirstScalarTerm x d level B k m H χ) := by
  let α := chen1973Lemma6Alpha x
  let CP := eq17PairNormBound x d B k m χ α
  let CS := eq17MobiusNormBound d H χ α
  let CL : ℝ := 1 + 1 / (α - 1)
  let C : ℝ := CP * (1 + CL * CS)
  have hα : 1 < α := by
    dsimp [α, chen1973Lemma6Alpha]
    have hlog : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < x by omega))
    linarith [one_div_pos.mpr hlog]
  have hCP : 0 ≤ CP := by dsimp [CP, eq17PairNormBound]; positivity

  have hCS : 0 ≤ CS := by dsimp [CS, eq17MobiusNormBound]; positivity
  have hCL : 0 ≤ CL := by dsimp [CL]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbase : Integrable (fun t : ℝ =>
      (chen1973Lemma6Eq17CorrectedRadialKernel x level (α + t * I))⁻¹) := by
    have h := integrable_growth_div_eq17Kernel
      (x := x) (level := level) hx (σ := α) (p := 0)
        (zero_lt_one.trans hα) (by norm_num)
    simpa using h
  have hmeas : AEStronglyMeasurable
      (eq17FirstScalarTerm x d level B k m H χ) := by
    unfold eq17FirstScalarTerm
    simp only [chen1973PrimitiveLDeriv, chen1973Lemma6PrimitiveLValue, dif_pos hd]
    apply Continuous.aestronglyMeasurable
    have hline : Continuous (fun t : ℝ => (α + t * I : ℂ)) := by fun_prop
    have hentire := DirichletCharacter.lFunction_entire_of_ne_one hχ
    have hL : Continuous (fun t : ℝ => χ.1.LFunction (α + t * I)) :=
      hentire.continuous.comp hline

    have hP := continuous_pairPolynomial_line
      (x := x) (B := B) (k := k) (m := m) χ α
    have hS := continuous_mobiusPartialSum_line (H := H) χ α
    have hK : Continuous (fun t : ℝ =>
        chen1973Lemma6Eq17CorrectedRadialKernel x level (α + t * I)) := by
      unfold chen1973Lemma6Eq17CorrectedRadialKernel chen1973Lemma6Eq17CorrectedKernel
      fun_prop

    have hKne : ∀ t : ℝ,
        chen1973Lemma6Eq17CorrectedRadialKernel x level (α + t * I) ≠ 0 := by
      intro t
      exact (chen1973Lemma6_eq17_correctedRadialKernel_pos
        (x := x) (level := level) (by omega : 1 < x)
        (zero_lt_one.trans hα) (v := t)).ne'
    exact ((hP.norm.mul
      (continuous_const.sub (hL.mul hS)).norm).div hK hKne)
  apply Integrable.mono' (hbase.const_mul C) hmeas
  filter_upwards with t
  have hP := norm_pairPolynomial_line_le
    (x := x) (B := B) (k := k) (m := m) χ α t

  have hS := norm_mobiusPartialSum_line_le (H := H) χ α t
  have hL := norm_dirichletLFunction_le χ.1 α t hα
  have hOne :
      ‖1 - χ.1.LFunction (α + t * I) *
          chen1973Lemma6MobiusPartialSum H (α + t * I) χ‖ ≤
        1 + CL * CS := by
    calc
      _ ≤ 1 + ‖χ.1.LFunction (α + t * I)‖ *
          ‖chen1973Lemma6MobiusPartialSum H (α + t * I) χ‖ := by
            simpa using norm_sub_le (1 : ℂ)
              (χ.1.LFunction (α + t * I) *
                chen1973Lemma6MobiusPartialSum H (α + t * I) χ)
      _ ≤ 1 + CL * CS := by
        gcongr
        simpa [CL, mul_comm] using hL
  have hKpos := chen1973Lemma6_eq17_correctedRadialKernel_pos
    (x := x) (level := level) (by omega : 1 < x)
    (zero_lt_one.trans hα) (v := t)
  have hterm0 : 0 ≤ eq17FirstScalarTerm x d level B k m H χ t := by
    unfold eq17FirstScalarTerm
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hterm0]
  unfold eq17FirstScalarTerm
  simp only [chen1973Lemma6PrimitiveLValue, dif_pos hd,
    Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by positivity) hKpos.le)]
  change _ ≤ C * _
  dsimp [C, CP, CS]
  rw [div_eq_mul_inv]
  gcongr

private theorem integrable_eq17SecondScalarTerm
    {x d level B k m H : ℕ} [NeZero d] (χ : PrimitiveCharacter d)
    (hd : 1 < d) (hχ : χ.1 ≠ 1) (hx : 3 ≤ x) :
    Integrable (eq17SecondScalarTerm x d level B k m H χ) := by
  let β := chen1973Lemma6Beta x
  let p : ℝ := 1 - 1 / (2 * Real.log x)
  let CP := eq17PairNormBound x d B k m χ β
  let CS := eq17MobiusNormBound d H χ β
  let C : ℝ := CP * (24 * ((d : ℝ) + 1)) * CS
  have hβ : 0 < β := beta_pos hx
  have hp : p < 1 := by
    dsimp [p]
    have hlog : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < x by omega))
    have : 0 < 1 / (2 * Real.log (x : ℝ)) := by positivity
    linarith
  have hCP : 0 ≤ CP := by dsimp [CP, eq17PairNormBound]; positivity
  have hCS : 0 ≤ CS := by dsimp [CS, eq17MobiusNormBound]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbase := integrable_growth_div_eq17Kernel
    (x := x) (level := level) hx (σ := β) (p := p) hβ hp
  have hmeas : AEStronglyMeasurable
      (eq17SecondScalarTerm x d level B k m H χ) := by
    unfold eq17SecondScalarTerm
    simp only [chen1973PrimitiveLDeriv, dif_pos hd]
    apply Continuous.aestronglyMeasurable
    have hline : Continuous (fun t : ℝ => (β + t * I : ℂ)) := by fun_prop
    have hentire := DirichletCharacter.lFunction_entire_of_ne_one hχ
    have hD : Continuous (fun t : ℝ => deriv χ.1.LFunction (β + t * I)) :=
      hentire.deriv.continuous.comp hline
    have hP := continuous_pairPolynomial_line
      (x := x) (B := B) (k := k) (m := m) χ β
    have hS := continuous_mobiusPartialSum_line (H := H) χ β
    have hK : Continuous (fun t : ℝ =>
        chen1973Lemma6Eq17CorrectedRadialKernel x level (β + t * I)) := by
      unfold chen1973Lemma6Eq17CorrectedRadialKernel chen1973Lemma6Eq17CorrectedKernel
      fun_prop
    have hKne : ∀ t : ℝ,
        chen1973Lemma6Eq17CorrectedRadialKernel x level (β + t * I) ≠ 0 := by
      intro t
      exact (chen1973Lemma6_eq17_correctedRadialKernel_pos
        (x := x) (level := level) (by omega : 1 < x) hβ (v := t)).ne'
    exact ((hP.norm.mul (hD.mul hS).norm).div hK hKne)
  apply Integrable.mono' (hbase.const_mul C) hmeas
  filter_upwards with t
  have hP := norm_pairPolynomial_line_le
    (x := x) (B := B) (k := k) (m := m) χ β t
  have hD := norm_deriv_LFunction_beta_sublinear χ hχ hx t
  have hS := norm_mobiusPartialSum_line_le (H := H) χ β t
  have hKpos := chen1973Lemma6_eq17_correctedRadialKernel_pos
    (x := x) (level := level) (by omega : 1 < x) hβ (v := t)
  have hterm0 : 0 ≤ eq17SecondScalarTerm x d level B k m H χ t := by
    unfold eq17SecondScalarTerm
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hterm0]
  unfold eq17SecondScalarTerm
  simp only [chen1973PrimitiveLDeriv, dif_pos hd,
    Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by positivity) hKpos.le)]
  change _ ≤ C * ((1 + |t|) ^ p / _)
  dsimp [C, CP, CS, p]
  rw [norm_mul, div_eq_mul_inv, div_eq_mul_inv]
  calc
    _ ≤ CP * ((24 * ((d : ℝ) + 1) *
          (1 + |t|) ^ (1 - 1 / (2 * Real.log x))) * CS) *
          (chen1973Lemma6Eq17CorrectedRadialKernel x level
            (chen1973Lemma6Beta x + t * I))⁻¹ := by
      gcongr
      simpa [mul_comm] using hD
    _ = CP * (24 * ((d : ℝ) + 1)) * CS *
          ((1 + |t|) ^ (1 - 1 / (2 * Real.log x)) *
            (chen1973Lemma6Eq17CorrectedRadialKernel x level
              (chen1973Lemma6Beta x + t * I))⁻¹) := by ring

private theorem norm_alphaPrimePairSum_le
    {x d level B k m H : ℕ} [NeZero d] (χ : PrimitiveCharacter d)
    (hd : 1 < d) (hχ : χ.1 ≠ 1) (hx : 3 ≤ x)
    (hAlpha : ∀ t : ℝ,
      ‖chen1973PrimitiveLDeriv d (chen1973Lemma6Alpha x + t * I) χ /
        chen1973Lemma6PrimitiveLValue d
          (chen1973Lemma6Alpha x + t * I) χ‖ ≤ 6 * (Real.log x) ^ 2) :
    ‖chen1973Lemma6AlphaNegLogDerivPrimePairSum x d B k m χ‖ ≤
      6 * (x : ℝ) * (Real.log x) ^ 2 *
          (∫ t : ℝ, eq17FirstScalarTerm x d level B k m H χ t) +
        (x : ℝ) ^ ((1 : ℝ) / 2) *
          (∫ t : ℝ, eq17SecondScalarTerm x d level B k m H χ t) := by
  rw [alphaPrimePairSum_eq_integral (level := level) χ hd hχ hx,
    integral_orig_eq_first_add_secondBeta
      (level := level) (H := H) χ hd hχ hx]
  let f : ℝ → ℂ := fun t =>
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      eq17FirstCharacterIntegrand x d B k m H χ t)
  let g : ℝ → ℂ := fun t =>
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      eq17SecondBetaCharacterIntegrand x d B k m H χ t)
  have hf : Integrable f :=
    (integrable_eq17FirstCharacterIntegrand
      (level := level) χ hd hχ hx).const_mul _
  have hg : Integrable g :=
    (integrable_eq17SecondBetaCharacterIntegrand χ hd hχ hx).const_mul _
  have hF := integrable_eq17FirstScalarTerm
    (level := level) (B := B) (k := k) (m := m) (H := H) χ hd hχ hx
  have hG := integrable_eq17SecondScalarTerm
    (level := level) (B := B) (k := k) (m := m) (H := H) χ hd hχ hx
  change ‖(∫ t : ℝ, f t) + (∫ t : ℝ, g t)‖ ≤ _
  calc
    ‖(∫ t : ℝ, f t) + (∫ t : ℝ, g t)‖ ≤
        ‖∫ t : ℝ, f t‖ + ‖∫ t : ℝ, g t‖ := norm_add_le _ _
    _ ≤ (∫ t : ℝ, ‖f t‖) + ∫ t : ℝ, ‖g t‖ :=
      add_le_add (norm_integral_le_integral_norm _) (norm_integral_le_integral_norm _)
    _ ≤ (∫ t : ℝ, 6 * (x : ℝ) * (Real.log x) ^ 2 *
          eq17FirstScalarTerm x d level B k m H χ t) +
        ∫ t : ℝ, (x : ℝ) ^ ((1 : ℝ) / 2) *
          eq17SecondScalarTerm x d level B k m H χ t := by
      apply add_le_add
      · apply integral_mono hf.norm
          (hF.const_mul (6 * (x : ℝ) * (Real.log x) ^ 2))
        intro t
        exact norm_normalized_first_le χ hd hχ hx t (hAlpha t)
      · apply integral_mono hg.norm
          (hG.const_mul ((x : ℝ) ^ ((1 : ℝ) / 2)))
        intro t
        exact norm_normalized_second_le χ hd hx t
    _ = _ := by
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

private theorem norm_alphaCharacterSum_le
    {x d level B k m H : ℕ} [NeZero d]
    (hd : 1 < d) (hx : 3 ≤ x)
    (hAlpha : ∀ χ : PrimitiveCharacter d, ∀ t : ℝ,
      ‖chen1973PrimitiveLDeriv d (chen1973Lemma6Alpha x + t * I) χ /
        chen1973Lemma6PrimitiveLValue d
          (chen1973Lemma6Alpha x + t * I) χ‖ ≤ 6 * (Real.log x) ^ 2) :
    ‖chen1973Lemma6AlphaNegLogDerivCharacterSum x d B k m‖ ≤
      6 * (x : ℝ) * (Real.log x) ^ 2 *
          (∑ χ : PrimitiveCharacter d,
            ∫ t : ℝ, eq17FirstScalarTerm x d level B k m H χ t) +
        (x : ℝ) ^ ((1 : ℝ) / 2) *
          (∑ χ : PrimitiveCharacter d,
            ∫ t : ℝ, eq17SecondScalarTerm x d level B k m H χ t) := by
  have hχ : ∀ χ : PrimitiveCharacter d, χ.1 ≠ 1 :=
    primitiveCharacter_ne_one_of_one_lt hd
  unfold chen1973Lemma6AlphaNegLogDerivCharacterSum
  calc
    ‖∑ χ : PrimitiveCharacter d,
        star (χ.1 (x : ZMod d)) *
          chen1973Lemma6AlphaNegLogDerivPrimePairSum x d B k m χ‖ ≤
      ∑ χ : PrimitiveCharacter d,
        ‖star (χ.1 (x : ZMod d)) *
          chen1973Lemma6AlphaNegLogDerivPrimePairSum x d B k m χ‖ :=
        norm_sum_le _ _
    _ ≤ ∑ χ : PrimitiveCharacter d,
        (6 * (x : ℝ) * (Real.log x) ^ 2 *
            (∫ t : ℝ, eq17FirstScalarTerm x d level B k m H χ t) +
          (x : ℝ) ^ ((1 : ℝ) / 2) *
            (∫ t : ℝ, eq17SecondScalarTerm x d level B k m H χ t)) := by
      apply Finset.sum_le_sum
      intro χ hχmem
      calc
        ‖star (χ.1 (x : ZMod d)) *
            chen1973Lemma6AlphaNegLogDerivPrimePairSum x d B k m χ‖ =
          ‖χ.1 (x : ZMod d)‖ *
            ‖chen1973Lemma6AlphaNegLogDerivPrimePairSum x d B k m χ‖ := by
              rw [norm_mul, norm_star]
        _ ≤ 1 * ‖chen1973Lemma6AlphaNegLogDerivPrimePairSum x d B k m χ‖ := by
          gcongr
          exact χ.1.norm_le_one _
        _ ≤ _ := by
          simpa using norm_alphaPrimePairSum_le
            (level := level) (H := H) χ hd (hχ χ) hx (hAlpha χ)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

private theorem firstFullIntegral_eq_sum_integrals
    {x L level B k m H : ℕ} (hx : 3 ≤ x) (hlevel : 1 ≤ level) :
    chen1973Lemma6Eq17CorrectedRadialFirstFullIntegral x L level B k m H =
      ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
        |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
          (3 : ℝ) ^ d.primeFactors.card / d *
          ∑ χ : PrimitiveCharacter d,
            ∫ t : ℝ, eq17FirstScalarTerm x d level B k m H χ t := by
  let w : ℕ → ℝ := fun d =>
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
      (3 : ℝ) ^ d.primeFactors.card / d
  have hint : ∀ d ∈ chen1973Lemma6ConductorBlock x L level,
      Integrable (fun t : ℝ =>
        w d * ∑ χ : PrimitiveCharacter d,
          eq17FirstScalarTerm x d level B k m H χ t) := by
    intro d hdmem
    have hd : 1 < d := one_lt_of_mem_conductorBlock hlevel hdmem
    letI : NeZero d := ⟨Nat.ne_zero_of_lt hd⟩
    apply Integrable.const_mul
    apply integrable_finset_sum
    intro χ hχmem
    exact integrable_eq17FirstScalarTerm χ hd
      (primitiveCharacter_ne_one_of_one_lt hd χ) hx
  unfold chen1973Lemma6Eq17CorrectedRadialFirstFullIntegral
  calc
    (∫ t : ℝ, chen1973Lemma6A x L level B k m H
        (chen1973Lemma6Alpha x + t * I) /
          chen1973Lemma6Eq17CorrectedRadialKernel x level
            (chen1973Lemma6Alpha x + t * I)) =
      ∫ t : ℝ, ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
        w d * ∑ χ : PrimitiveCharacter d,
          eq17FirstScalarTerm x d level B k m H χ t := by
      apply integral_congr_ae
      filter_upwards with t
      unfold chen1973Lemma6A eq17FirstScalarTerm
        chen1973Lemma6Eq17PairPolynomial
      dsimp [w]
      simp only [div_eq_mul_inv]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hdmem
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ hχmem
      ring
    _ = ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
        ∫ t : ℝ, w d * ∑ χ : PrimitiveCharacter d,
          eq17FirstScalarTerm x d level B k m H χ t := by
      rw [integral_finsetSum]
      intro d hdmem
      exact hint d hdmem
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hdmem
      rw [MeasureTheory.integral_const_mul, integral_finsetSum]
      have hd : 1 < d := one_lt_of_mem_conductorBlock hlevel hdmem
      letI : NeZero d := ⟨Nat.ne_zero_of_lt hd⟩
      intro χ hχmem
      exact integrable_eq17FirstScalarTerm χ hd
        (primitiveCharacter_ne_one_of_one_lt hd χ) hx

private theorem secondFullIntegral_eq_sum_integrals
    {x L level B k m H : ℕ} (hx : 3 ≤ x) (hlevel : 1 ≤ level) :
    chen1973Lemma6Eq17CorrectedRadialSecondFullIntegral x L level B k m H =
      ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
        |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
          (3 : ℝ) ^ d.primeFactors.card / d *
          ∑ χ : PrimitiveCharacter d,
            ∫ t : ℝ, eq17SecondScalarTerm x d level B k m H χ t := by
  let w : ℕ → ℝ := fun d =>
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
      (3 : ℝ) ^ d.primeFactors.card / d
  have hint : ∀ d ∈ chen1973Lemma6ConductorBlock x L level,
      Integrable (fun t : ℝ =>
        w d * ∑ χ : PrimitiveCharacter d,
          eq17SecondScalarTerm x d level B k m H χ t) := by
    intro d hdmem
    have hd : 1 < d := one_lt_of_mem_conductorBlock hlevel hdmem
    letI : NeZero d := ⟨Nat.ne_zero_of_lt hd⟩
    apply Integrable.const_mul
    apply integrable_finset_sum
    intro χ hχmem
    exact integrable_eq17SecondScalarTerm χ hd
      (primitiveCharacter_ne_one_of_one_lt hd χ) hx
  unfold chen1973Lemma6Eq17CorrectedRadialSecondFullIntegral
  calc
    (∫ t : ℝ, chen1973Lemma6B x L level B k m H
        (chen1973Lemma6Beta x + t * I) /
          chen1973Lemma6Eq17CorrectedRadialKernel x level
            (chen1973Lemma6Beta x + t * I)) =
      ∫ t : ℝ, ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
        w d * ∑ χ : PrimitiveCharacter d,
          eq17SecondScalarTerm x d level B k m H χ t := by
      apply integral_congr_ae
      filter_upwards with t
      unfold chen1973Lemma6B eq17SecondScalarTerm
        chen1973Lemma6Eq17PairPolynomial
      dsimp [w]
      simp only [div_eq_mul_inv]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hdmem
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ hχmem
      ring
    _ = ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
        ∫ t : ℝ, w d * ∑ χ : PrimitiveCharacter d,
          eq17SecondScalarTerm x d level B k m H χ t := by
      rw [integral_finsetSum]
      intro d hdmem
      exact hint d hdmem
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hdmem
      rw [MeasureTheory.integral_const_mul, integral_finsetSum]
      have hd : 1 < d := one_lt_of_mem_conductorBlock hlevel hdmem
      letI : NeZero d := ⟨Nat.ne_zero_of_lt hd⟩
      intro χ hχmem
      exact integrable_eq17SecondScalarTerm χ hd
        (primitiveCharacter_ne_one_of_one_lt hd χ) hx

private theorem chen1973Lemma6_equation17_corrected_radial_main
    {x L level B k m H : ℕ} (hx : 3 ≤ x) (hlevel : 1 ≤ level)
    (hAlpha : Chen1973Equation17AlphaLogDerivativePayment x L level) :
    chen1973Lemma6NmBlockActual x L level B k m ≤
      12 * x * (Real.log x) ^ 2 * chen1973Lemma6Eq17CorrectedRadialFirstIntegral x L level B k m H +
        2 * (x : ℝ) ^ ((1 : ℝ) / 2) * chen1973Lemma6Eq17CorrectedRadialSecondIntegral x L level B k m H := by
  have hx1 : 1 < x := by omega
  rw [chen1973Lemma6NmBlockActual_eq_alphaNegLogDeriv hlevel hx]
  have hfirst := chen1973Lemma6Eq17CorrectedRadialFirstFullIntegral_eq_two_mul_half
    (x := x) (L := L) (level := level) (B := B) (k := k) (m := m) (H := H) hlevel hx1
  have hsecond := chen1973Lemma6Eq17CorrectedRadialSecondFullIntegral_eq_two_mul_half
    (x := x) (L := L) (level := level) (B := B) (k := k) (m := m) (H := H) hlevel hx1
  have hrhs :
      12 * x * (Real.log x) ^ 2 * chen1973Lemma6Eq17CorrectedRadialFirstIntegral x L level B k m H +
        2 * (x : ℝ) ^ ((1 : ℝ) / 2) * chen1973Lemma6Eq17CorrectedRadialSecondIntegral x L level B k m H =
      6 * (x : ℝ) * (Real.log x) ^ 2 * chen1973Lemma6Eq17CorrectedRadialFirstFullIntegral x L level B k m H +
        (x : ℝ) ^ ((1 : ℝ) / 2) * chen1973Lemma6Eq17CorrectedRadialSecondFullIntegral x L level B k m H := by
    rw [hfirst, hsecond]
    ring
  rw [hrhs]
  unfold chen1973Lemma6NmBlockAlphaNegLogDeriv
  let w : ℕ → ℝ := fun d =>
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
      (3 : ℝ) ^ d.primeFactors.card / d
  let X : ℝ := 6 * (x : ℝ) * (Real.log x) ^ 2
  let Y : ℝ := (x : ℝ) ^ ((1 : ℝ) / 2)
  have hw : ∀ d, 0 ≤ w d := by
    intro d
    dsimp [w]
    positivity
  have hfirstSum := firstFullIntegral_eq_sum_integrals
    (x := x) (L := L) (level := level) (B := B) (k := k) (m := m) (H := H)
    hx hlevel
  have hsecondSum := secondFullIntegral_eq_sum_integrals
    (x := x) (L := L) (level := level) (B := B) (k := k) (m := m) (H := H)
    hx hlevel
  change (∑ d ∈ chen1973Lemma6ConductorBlock x L level,
    w d * ‖chen1973Lemma6AlphaNegLogDerivCharacterSum x d B k m‖) ≤ _
  calc
    _ ≤ ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
        w d * (X *
            (∑ χ : PrimitiveCharacter d,
              ∫ t : ℝ, eq17FirstScalarTerm x d level B k m H χ t) +
          Y * (∑ χ : PrimitiveCharacter d,
              ∫ t : ℝ, eq17SecondScalarTerm x d level B k m H χ t)) := by
      apply Finset.sum_le_sum
      intro d hdmem
      have hd : 1 < d := one_lt_of_mem_conductorBlock hlevel hdmem
      letI : NeZero d := ⟨Nat.ne_zero_of_lt hd⟩
      apply mul_le_mul_of_nonneg_left _ (hw d)
      simpa [X, Y] using norm_alphaCharacterSum_le
        (level := level) (H := H) hd hx (hAlpha d hdmem)
    _ = (X * ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
          w d * ∑ χ : PrimitiveCharacter d,
            ∫ t : ℝ, eq17FirstScalarTerm x d level B k m H χ t) +
        Y * ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
          w d * ∑ χ : PrimitiveCharacter d,
            ∫ t : ℝ, eq17SecondScalarTerm x d level B k m H χ t := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      congr 1 <;> simp_rw [Finset.mul_sum] <;>
        simp only [mul_assoc, mul_left_comm]
    _ = 6 * (x : ℝ) * (Real.log x) ^ 2 *
          chen1973Lemma6Eq17CorrectedRadialFirstFullIntegral x L level B k m H +
        (x : ℝ) ^ ((1 : ℝ) / 2) *
          chen1973Lemma6Eq17CorrectedRadialSecondFullIntegral x L level B k m H := by
      rw [hfirstSum, hsecondSum]

theorem chen1973Lemma6_eq17_corrected_radial_contourMajorization
    {x L level B k m H : ℕ} (hx : 3 ≤ x) (hlevel : 1 ≤ level)
    (hAlpha : Chen1973Equation17AlphaLogDerivativePayment x L level) :
    Chen1973Equation17CorrectedRadialContourMajorization x L level B k m H := by
  simpa [Chen1973Equation17CorrectedRadialContourMajorization,
    chen1973Lemma6Equation17CorrectedRadialRHS] using
    (chen1973Lemma6_equation17_corrected_radial_main (x := x) (L := L) (level := level)
      (B := B) (k := k) (m := m) (H := H) hx hlevel hAlpha)

theorem chen1973Lemma6_equation17_corrected_radial
    {x L level B k m H : ℕ} (hx : 3 ≤ x) (hlevel : 1 ≤ level)
    (hAlpha : Chen1973Equation17AlphaLogDerivativePayment x L level) :
    chen1973Lemma6NmBlockActual x L level B k m ≤
      12 * x * (Real.log x) ^ 2 * chen1973Lemma6Eq17CorrectedRadialFirstIntegral x L level B k m H +
        2 * (x : ℝ) ^ ((1 : ℝ) / 2) * chen1973Lemma6Eq17CorrectedRadialSecondIntegral x L level B k m H := by
  exact chen1973Lemma6_equation17_corrected_radial_main hx hlevel hAlpha

/-- The alpha-line payment is unconditional: absolute convergence of the
`-L'/L` von Mangoldt series supplies the explicit coefficient `6`. -/
theorem chen1973Lemma6_equation17_alphaLogDerivativePayment_unconditional
    {x L level : ℕ} (hx : 3 ≤ x) (hlevel : 1 ≤ level) :
    Chen1973Equation17AlphaLogDerivativePayment x L level := by
  intro d hdmem χ t
  have hd : 1 < d := one_lt_of_mem_conductorBlock hlevel hdmem
  letI : NeZero d := ⟨Nat.ne_zero_of_lt hd⟩
  exact chen1973Lemma6_alphaLogDerivative_le_six_mul_log_sq χ hd hx t

/-- Unconditional corrected equation-(17) assembly.  The source `A` remains
unchanged; the absolute alpha-line logarithmic derivative is paid only in the
first displayed coefficient. -/
theorem chen1973Lemma6_equation17_corrected_radial_unconditional
    {x L level B k m H : ℕ} (hx : 3 ≤ x) (hlevel : 1 ≤ level) :
    chen1973Lemma6NmBlockActual x L level B k m ≤
      12 * x * (Real.log x) ^ 2 *
          chen1973Lemma6Eq17CorrectedRadialFirstIntegral x L level B k m H +
        2 * (x : ℝ) ^ ((1 : ℝ) / 2) *
          chen1973Lemma6Eq17CorrectedRadialSecondIntegral x L level B k m H := by
  exact chen1973Lemma6_equation17_corrected_radial hx hlevel
    (chen1973Lemma6_equation17_alphaLogDerivativePayment_unconditional hx hlevel)

end AnalyticNumberTheory.LargeSieve