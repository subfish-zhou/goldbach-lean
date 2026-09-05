import MathlibNt.AnalyticNumberTheory.Siegel.Bombieri1965Theorem4TwoCharacterAsymptotic
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Mellin continuation of the genuine two-character convolution

This modern argument continues the actual four-factor product by the Mellin
transform of its proved summatory error. Only the first character must be
quadratic; neither character must be primitive. This is not a source
transcription of Bombieri's argument.
-/

open Complex Finset Filter MeasureTheory Set Asymptotics
open scoped Topology

namespace AnalyticNumberTheory.LargeSieve.Bombieri1965Theorem4

open DirichletCharacter

variable {q : ℕ} [NeZero q]

/-- The actual complex summatory function. -/
noncomputable def twoCharacterSummatory (χ ψ : DirichletCharacter ℂ q) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, twoCharacterConvolution χ ψ n

/-- The actual summatory error with its actual residue. -/
noncomputable def twoCharacterError (χ ψ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  twoCharacterSummatory χ ψ ⌊t⌋₊ - (t : ℂ) * twoCharacterResidue χ ψ

/-- The Mellin kernel of the summatory error. -/
noncomputable def twoCharacterErrorKernel
    (χ ψ : DirichletCharacter ℂ q) (s : ℂ) (t : ℝ) : ℂ :=
  twoCharacterError χ ψ t * (t : ℂ) ^ (-(s + 1))

/-- The genuine error integral, initially convergent for `Re s > 3/4`. -/
noncomputable def twoCharacterErrorIntegral
    (χ ψ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∫ t in Ioi (1 : ℝ), twoCharacterErrorKernel χ ψ s t

/-- The cutoff needed to use the Mellin transform on the positive half-line. -/
noncomputable def twoCharacterCutoffError (χ ψ : DirichletCharacter ℂ q) : ℝ → ℂ :=
  (Ioi (1 : ℝ)).indicator (twoCharacterError χ ψ)

theorem norm_twoCharacterError_le
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) {t : ℝ} (ht : 1 ≤ t) :
    ‖twoCharacterError χ ψ t‖ ≤ 308 * (q : ℝ) ^ 3 * t ^ (3 / 4 : ℝ) := by
  have hf := Nat.floor_le (show 0 ≤ t by linarith)
  have herror : |(⌊t⌋₊ : ℝ) - t| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [Nat.lt_floor_add_one t]
  have he : ‖((⌊t⌋₊ : ℂ) - (t : ℂ)) * twoCharacterResidue χ ψ‖ ≤
      8 * (q : ℝ) ^ 3 := by
    rw [norm_mul]
    have hc : ‖(⌊t⌋₊ : ℂ) - (t : ℂ)‖ ≤ 1 := by
      simpa only [← ofReal_natCast, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using herror
    exact (mul_le_mul hc
      (norm_twoCharacterResidue_le_eight_mul_modulus_cubed χ ψ hχ hψ hprod)
      (norm_nonneg _) (by norm_num)).trans (by simp)
  have hp : (⌊t⌋₊ : ℝ) ^ (3 / 4 : ℝ) ≤ t ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hf (by norm_num)
  have hp1 : 1 ≤ t ^ (3 / 4 : ℝ) := by
    simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) ht
      (by norm_num : (0 : ℝ) ≤ 3 / 4)
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hqq : (q : ℝ) ^ 2 ≤ (q : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (q : ℝ)) (sub_nonneg.mpr hq)]
  have hn :
      ‖twoCharacterSummatory χ ψ ⌊t⌋₊ - (⌊t⌋₊ : ℂ) * twoCharacterResidue χ ψ‖ ≤
        300 * (q : ℝ) ^ 2 * (⌊t⌋₊ : ℝ) ^ (3 / 4 : ℝ) := by
    have hI : Finset.Icc 1 ⌊t⌋₊ = Finset.Ioc 0 ⌊t⌋₊ := by ext n; simp; omega
    simpa only [twoCharacterSummatory, hI] using
      norm_sum_Ioc_twoCharacterConvolution_sub_residue_main_le χ ψ hχ hχquad hψ hprod ⌊t⌋₊
  calc
    _ = ‖(twoCharacterSummatory χ ψ ⌊t⌋₊ - (⌊t⌋₊ : ℂ) * twoCharacterResidue χ ψ) +
        ((⌊t⌋₊ : ℂ) - (t : ℂ)) * twoCharacterResidue χ ψ‖ := by
      unfold twoCharacterError
      congr 1
      ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ 300 * (q : ℝ) ^ 2 * (⌊t⌋₊ : ℝ) ^ (3 / 4 : ℝ) + 8 * (q : ℝ) ^ 3 :=
      add_le_add hn he
    _ ≤ 300 * (q : ℝ) ^ 3 * t ^ (3 / 4 : ℝ) +
        8 * (q : ℝ) ^ 3 * t ^ (3 / 4 : ℝ) := by
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hqq (by norm_num)) hp
          (by positivity) (by positivity)
      · simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hp1 (show (0 : ℝ) ≤ 8 * (q : ℝ) ^ 3 by positivity)
    _ = _ := by ring

theorem measurable_twoCharacterError (χ ψ : DirichletCharacter ℂ q) :
    Measurable (twoCharacterError χ ψ) :=
  ((StronglyMeasurable.of_discrete (f := twoCharacterSummatory χ ψ)).measurable.comp
    measurable_id.nat_floor).sub (Complex.measurable_ofReal.mul_const _)

theorem measurable_twoCharacterCutoffError (χ ψ : DirichletCharacter ℂ q) :
    Measurable (twoCharacterCutoffError χ ψ) :=
  (measurable_twoCharacterError χ ψ).indicator measurableSet_Ioi

theorem norm_twoCharacterCutoffError_le
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) (t : ℝ) :
    ‖twoCharacterCutoffError χ ψ t‖ ≤ 308 * (q : ℝ) ^ 3 * |t| ^ (3 / 4 : ℝ) := by
  by_cases ht : 1 < t
  · simpa [twoCharacterCutoffError, ht, abs_of_pos (lt_trans zero_lt_one ht)] using
      norm_twoCharacterError_le χ ψ hχ hχquad hψ hprod ht.le
  · simp only [twoCharacterCutoffError, Set.mem_Ioi, ht, not_false_eq_true,
      indicator_of_notMem, norm_zero]
    positivity

theorem locallyIntegrable_twoCharacterCutoffError
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) :
    LocallyIntegrable (twoCharacterCutoffError χ ψ) := by
  have hc : Continuous (fun t : ℝ => 308 * (q : ℝ) ^ 3 * |t| ^ (3 / 4 : ℝ)) :=
    continuous_const.mul (continuous_abs.rpow_const (by norm_num))
  refine hc.locallyIntegrable.mono
    (measurable_twoCharacterCutoffError χ ψ).aestronglyMeasurable ?_
  filter_upwards [] with t
  exact (norm_twoCharacterCutoffError_le χ ψ hχ hχquad hψ hprod t).trans
    (Real.le_norm_self _)

theorem twoCharacterCutoffError_isBigO_atTop
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) :
    twoCharacterCutoffError χ ψ =O[atTop] (fun t : ℝ => t ^ (3 / 4 : ℝ)) := by
  refine isBigO_iff.mpr ⟨308 * (q : ℝ) ^ 3, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simpa [abs_of_nonneg ht, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht _)] using
    norm_twoCharacterCutoffError_le χ ψ hχ hχquad hψ hprod t

theorem twoCharacterCutoffError_isBigO_zero
    (χ ψ : DirichletCharacter ℂ q) (b : ℝ) :
    twoCharacterCutoffError χ ψ =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ b) := by
  refine isBigO_iff.mpr ⟨0, ?_⟩
  filter_upwards [((eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
    nhdsWithin_le_nhds)] with t ht
  simp [twoCharacterCutoffError, not_lt.mpr ht.le]

private theorem cutoff_mellin_kernel (χ ψ : DirichletCharacter ℂ q) (s : ℂ) :
    (fun t : ℝ => (t : ℂ) ^ (-s - 1) • twoCharacterCutoffError χ ψ t) =
      (Ioi (1 : ℝ)).indicator (twoCharacterErrorKernel χ ψ s) := by
  funext t
  by_cases ht : 1 < t
  · simp [twoCharacterCutoffError, twoCharacterErrorKernel, ht,
      smul_eq_mul, sub_eq_add_neg, mul_comm, add_comm]
  · simp [twoCharacterCutoffError, ht]

theorem mellin_twoCharacterCutoffError (χ ψ : DirichletCharacter ℂ q) (s : ℂ) :
    mellin (twoCharacterCutoffError χ ψ) (-s) = twoCharacterErrorIntegral χ ψ s := by
  rw [mellin, cutoff_mellin_kernel, setIntegral_indicator measurableSet_Ioi]
  simp only [Ioi_inter_Ioi, max_eq_right (show (0 : ℝ) ≤ 1 by norm_num)]
  rfl

theorem integrableOn_twoCharacterErrorKernel
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) {s : ℂ} (hs : 3 / 4 < s.re) :
    IntegrableOn (twoCharacterErrorKernel χ ψ s) (Ioi (1 : ℝ)) := by
  have h : MellinConvergent (twoCharacterCutoffError χ ψ) (-s) := by
    apply mellinConvergent_of_isBigO_rpow
      ((locallyIntegrable_twoCharacterCutoffError χ ψ hχ hχquad hψ hprod).locallyIntegrableOn _)
      (a := -(3 / 4)) (b := -s.re - 1)
    · simpa using twoCharacterCutoffError_isBigO_atTop χ ψ hχ hχquad hψ hprod
    · simp only [neg_re]; linarith
    · exact twoCharacterCutoffError_isBigO_zero χ ψ _
    · simp only [neg_re]; linarith
  rw [MellinConvergent, cutoff_mellin_kernel,
    integrableOn_indicator_iff measurableSet_Ioi] at h
  simpa only [Ioi_inter_Ioi, max_eq_left (show (0 : ℝ) ≤ 1 by norm_num)] using h

/-- Holomorphy is proved from the actual `O(t^(3/4))` error. -/
theorem differentiableAt_twoCharacterErrorIntegral
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) {s : ℂ} (hs : 3 / 4 < s.re) :
    DifferentiableAt ℂ (twoCharacterErrorIntegral χ ψ) s := by
  have hm : DifferentiableAt ℂ (mellin (twoCharacterCutoffError χ ψ)) (-s) := by
    apply mellin_differentiableAt_of_isBigO_rpow
      ((locallyIntegrable_twoCharacterCutoffError χ ψ hχ hχquad hψ hprod).locallyIntegrableOn _)
      (a := -(3 / 4)) (b := -s.re - 1)
    · simpa using twoCharacterCutoffError_isBigO_atTop χ ψ hχ hχquad hψ hprod
    · simp only [neg_re]; linarith
    · exact twoCharacterCutoffError_isBigO_zero χ ψ _
    · simp only [neg_re]; linarith
  simpa only [Function.comp_def, mellin_twoCharacterCutoffError] using
    hm.comp s differentiableAt_id.neg

theorem twoCharacterSummatory_isBigO
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) :
    twoCharacterSummatory χ ψ =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
  refine isBigO_iff.mpr ⟨308 * (q : ℝ) ^ 3 + ‖twoCharacterResidue χ ψ‖, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (n : ℝ) ^ (3 / 4 : ℝ) ≤ n := by
    simpa using Real.rpow_le_rpow_of_exponent_le hnR (by norm_num : (3 / 4 : ℝ) ≤ 1)
  have he := norm_twoCharacterError_le χ ψ hχ hχquad hψ hprod hnR
  simp only [twoCharacterError, Nat.floor_natCast, ofReal_natCast] at he
  have ht := norm_add_le
    (twoCharacterSummatory χ ψ n - (n : ℂ) * twoCharacterResidue χ ψ)
    ((n : ℂ) * twoCharacterResidue χ ψ)
  rw [sub_add_cancel, norm_mul, Complex.norm_natCast] at ht
  simp only [Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  nlinarith [mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 308 * (q : ℝ) ^ 3 by positivity)]

private theorem mul_error_cpow (t : ℝ) (ht : 0 < t) (s : ℂ) :
    (t : ℂ) * (t : ℂ) ^ (-(s + 1)) = (t : ℂ) ^ (-s) := by
  calc
    _ = (t : ℂ) ^ (1 : ℂ) * (t : ℂ) ^ (-(s + 1)) := by rw [cpow_one]
    _ = (t : ℂ) ^ ((1 : ℂ) + -(s + 1)) :=
      (cpow_add _ _ (ofReal_ne_zero.mpr ht.ne')).symm
    _ = _ := by congr 1; ring

private theorem summatory_kernel_split
    (χ ψ : DirichletCharacter ℂ q) (s : ℂ) {t : ℝ} (ht : 1 < t) :
    twoCharacterSummatory χ ψ ⌊t⌋₊ * (t : ℂ) ^ (-(s + 1)) =
      twoCharacterErrorKernel χ ψ s t +
        twoCharacterResidue χ ψ * (t : ℂ) ^ (-s) := by
  rw [twoCharacterErrorKernel, twoCharacterError, sub_mul,
    ← mul_error_cpow t (by linarith) s]
  ring

theorem twoCharacter_product_eq_errorIntegral_of_one_lt_re
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ * ψ).LFunction s =
      twoCharacterResidue χ ψ * s / (s - 1) + s * twoCharacterErrorIntegral χ ψ s := by
  have hid := LSeries_eq_mul_integral (twoCharacterConvolution χ ψ)
    (r := 1) (by norm_num) hs (LSeriesSummable_twoCharacterConvolution χ ψ hs)
    (twoCharacterSummatory_isBigO χ ψ hχ hχquad hψ hprod)
  rw [LSeries_twoCharacterConvolution_eq_LFunction_product χ ψ hs] at hid
  change _ = s * ∫ t in Ioi (1 : ℝ),
    twoCharacterSummatory χ ψ ⌊t⌋₊ * (t : ℂ) ^ (-(s + 1)) at hid
  have hsplit :
      (∫ t in Ioi (1 : ℝ), twoCharacterSummatory χ ψ ⌊t⌋₊ * (t : ℂ) ^ (-(s + 1))) =
        twoCharacterErrorIntegral χ ψ s +
          twoCharacterResidue χ ψ * (-(1 : ℂ) / (-s + 1)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => summatory_kernel_split χ ψ s ht)]
    rw [integral_add
      (integrableOn_twoCharacterErrorKernel χ ψ hχ hχquad hψ hprod (by linarith))
      ((integrableOn_Ioi_cpow_of_lt (by simpa using (neg_lt_neg hs))
        (by norm_num : (0 : ℝ) < 1)).const_mul (twoCharacterResidue χ ψ)),
      integral_const_mul, integral_Ioi_cpow_of_lt (by simpa using (neg_lt_neg hs))
        (by norm_num : (0 : ℝ) < 1)]
    simp only [ofReal_one, one_cpow]
    rfl
  rw [hid, hsplit, show -s + 1 = -(s - 1) by ring, div_neg, neg_div, neg_neg]
  ring

/-- Identity-theorem continuation of the pole-cleared actual product. -/
theorem twoCharacter_regularized_product_eq_errorIntegral
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) {s : ℂ} (hs : 3 / 4 < s.re) :
    riemannZeta₁ s * χ.LFunction s * ψ.LFunction s * (χ * ψ).LFunction s =
      twoCharacterResidue χ ψ * s + (s - 1) * s * twoCharacterErrorIntegral χ ψ s := by
  let U : Set ℂ := {z | 3 / 4 < z.re}
  let F : ℂ → ℂ := fun z => twoCharacterResidue χ ψ * z +
    (z - 1) * z * twoCharacterErrorIntegral χ ψ z
  let G : ℂ → ℂ := fun z =>
    riemannZeta₁ z * χ.LFunction z * ψ.LFunction z * (χ * ψ).LFunction z
  have hUopen : IsOpen U := continuous_re.isOpen_preimage _ isOpen_Ioi
  have hFdiff : DifferentiableOn ℂ F U := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    have hE := differentiableAt_twoCharacterErrorIntegral χ ψ hχ hχquad hψ hprod hz
    dsimp [F]
    fun_prop
  have hF : AnalyticOnNhd ℂ F U := hFdiff.analyticOnNhd hUopen
  have hG : AnalyticOnNhd ℂ G U :=
    (((differentiable_riemannZeta₁.mul (χ.differentiable_LFunction hχ)).mul
      (ψ.differentiable_LFunction hψ)).mul
        ((χ * ψ).differentiable_LFunction hprod)).differentiableOn.analyticOnNhd
          isOpen_univ |>.mono (subset_univ U)
  have hpre : IsPreconnected U := (convex_halfSpace_re_gt (3 / 4)).isPreconnected
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
    have hid := twoCharacter_product_eq_errorIntegral_of_one_lt_re χ ψ hχ hχquad hψ hprod hz
    dsimp [F, G]
    rw [hzeta]
    calc
      _ = (z - 1) * (riemannZeta z * χ.LFunction z * ψ.LFunction z *
          (χ * ψ).LFunction z) := by ring
      _ = _ := by rw [hid]; field_simp
  exact hG.eqOn_of_preconnected_of_eventuallyEq hF hpre htwo hevent hs

/-- The continued constant is the actual zeta/three-L-function product. -/
theorem twoCharacter_product_eq_errorIntegral
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχquad : χ ^ 2 = 1)
    (hψ : ψ ≠ 1) (hprod : χ * ψ ≠ 1) {s : ℂ} (hs : 3 / 4 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ * ψ).LFunction s =
      twoCharacterResidue χ ψ * s / (s - 1) + s * twoCharacterErrorIntegral χ ψ s := by
  have h := twoCharacter_regularized_product_eq_errorIntegral χ ψ hχ hχquad hψ hprod hs
  rw [riemannZeta_eq_inv_sub_mul hs1]
  calc
    _ = (s - 1)⁻¹ *
        (riemannZeta₁ s * χ.LFunction s * ψ.LFunction s * (χ * ψ).LFunction s) := by ring
    _ = _ := by rw [h]; field_simp

end AnalyticNumberTheory.LargeSieve.Bombieri1965Theorem4
