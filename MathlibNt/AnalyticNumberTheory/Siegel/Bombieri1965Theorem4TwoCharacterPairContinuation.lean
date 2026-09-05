import MathlibNt.AnalyticNumberTheory.Siegel.Bombieri1965Theorem4TwoCharacterPairSummatory
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Mellin continuation of a nonprincipal character pair

This modern analytic argument identifies the Mellin integral of the actual
convolution of two nonprincipal characters with the product of their
L-functions on `Re s > 1/2`. No primitivity or quadraticity is needed.
In particular the value at one is the actual L-value product, not a
formal or absolutely convergent harmonic series.
-/

open Complex Finset Filter MeasureTheory Set Asymptotics
open scoped Topology

namespace DirichletCharacter

variable {q : ℕ} [NeZero q]

/-- The actual pair summatory function at a real endpoint. -/
noncomputable def characterPairSummatory (ψ η : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊t⌋₊,
    (toArithmeticFunction (ψ ·) * toArithmeticFunction (η ·)) n

/-- The kernel whose integral continues the pair Dirichlet series. -/
noncomputable def characterPairKernel
    (ψ η : DirichletCharacter ℂ q) (s : ℂ) (t : ℝ) : ℂ :=
  characterPairSummatory ψ η t * (t : ℂ) ^ (-(s + 1))

/-- The genuinely convergent integral used for the continuation. -/
noncomputable def characterPairIntegral
    (ψ η : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∫ t in Ioi (1 : ℝ), characterPairKernel ψ η s t

/-- Cutoff of the actual summatory function for the Mellin transform. -/
noncomputable def characterPairCutoff (ψ η : DirichletCharacter ℂ q) : ℝ → ℂ :=
  (Ioi (1 : ℝ)).indicator (characterPairSummatory ψ η)

omit [NeZero q] in
theorem measurable_characterPairSummatory (ψ η : DirichletCharacter ℂ q) :
    Measurable (characterPairSummatory ψ η) :=
  (StronglyMeasurable.of_discrete (f := fun N : ℕ =>
    ∑ n ∈ Finset.Icc 1 N,
      (toArithmeticFunction (ψ ·) * toArithmeticFunction (η ·)) n)).measurable.comp
        measurable_id.nat_floor

omit [NeZero q] in
theorem measurable_characterPairCutoff (ψ η : DirichletCharacter ℂ q) :
    Measurable (characterPairCutoff ψ η) :=
  (measurable_characterPairSummatory ψ η).indicator measurableSet_Ioi

theorem norm_characterPairCutoff_le (ψ η : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) (hη : η ≠ 1) (t : ℝ) :
    ‖characterPairCutoff ψ η t‖ ≤ 3 * q * Real.sqrt t := by
  by_cases ht : 1 < t
  · simpa [characterPairCutoff, characterPairSummatory, ht] using
      norm_sum_Icc_floor_character_pair_convolution_le_three_mul_sqrt ψ η hψ hη
        (show 0 ≤ t by linarith)
  · simp [characterPairCutoff, ht]
    positivity

theorem locallyIntegrable_characterPairCutoff (ψ η : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) (hη : η ≠ 1) :
    LocallyIntegrable (characterPairCutoff ψ η) := by
  refine (show Continuous (fun t : ℝ => 3 * (q : ℝ) * Real.sqrt t) by
    fun_prop).locallyIntegrable.mono
      (measurable_characterPairCutoff ψ η).aestronglyMeasurable ?_
  filter_upwards [] with t
  exact (norm_characterPairCutoff_le ψ η hψ hη t).trans (Real.le_norm_self _)

theorem characterPairCutoff_isBigO_atTop (ψ η : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) (hη : η ≠ 1) :
    characterPairCutoff ψ η =O[atTop] (fun t : ℝ => t ^ (1 / 2 : ℝ)) := by
  refine isBigO_iff.mpr ⟨3 * q, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simpa [Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht _)]
    using norm_characterPairCutoff_le ψ η hψ hη t

omit [NeZero q] in
theorem characterPairCutoff_isBigO_zero (ψ η : DirichletCharacter ℂ q) (b : ℝ) :
    characterPairCutoff ψ η =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ b) := by
  refine isBigO_iff.mpr ⟨0, ?_⟩
  filter_upwards [((eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
    nhdsWithin_le_nhds)] with t ht
  simp [characterPairCutoff, not_lt.mpr ht.le]

omit [NeZero q] in
private theorem characterPair_cutoff_mellin_kernel
    (ψ η : DirichletCharacter ℂ q) (s : ℂ) :
    (fun t : ℝ => (t : ℂ) ^ (-s - 1) • characterPairCutoff ψ η t) =
      (Ioi (1 : ℝ)).indicator (characterPairKernel ψ η s) := by
  funext t
  by_cases ht : 1 < t
  · simp [characterPairCutoff, characterPairKernel, ht,
      smul_eq_mul, sub_eq_add_neg, mul_comm, add_comm]
  · simp [characterPairCutoff, ht]

omit [NeZero q] in
theorem mellin_characterPairCutoff (ψ η : DirichletCharacter ℂ q) (s : ℂ) :
    mellin (characterPairCutoff ψ η) (-s) = characterPairIntegral ψ η s := by
  rw [mellin, characterPair_cutoff_mellin_kernel, setIntegral_indicator measurableSet_Ioi]
  simp only [Ioi_inter_Ioi, max_eq_right (show (0 : ℝ) ≤ 1 by norm_num)]
  rfl

theorem mellinConvergent_characterPairCutoff (ψ η : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) (hη : η ≠ 1) {s : ℂ} (hs : 1 / 2 < s.re) :
    MellinConvergent (characterPairCutoff ψ η) (-s) := by
  apply mellinConvergent_of_isBigO_rpow
    ((locallyIntegrable_characterPairCutoff ψ η hψ hη).locallyIntegrableOn _)
    (a := -(1 / 2)) (b := -s.re - 1)
  · simpa using characterPairCutoff_isBigO_atTop ψ η hψ hη
  · simp only [neg_re]; linarith
  · exact characterPairCutoff_isBigO_zero ψ η _
  · simp only [neg_re]; linarith

/-- Absolute integrability of the summatory kernel, not of the harmonic series. -/
theorem integrableOn_characterPairKernel (ψ η : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) (hη : η ≠ 1) {s : ℂ} (hs : 1 / 2 < s.re) :
    IntegrableOn (characterPairKernel ψ η s) (Ioi (1 : ℝ)) := by
  have h := mellinConvergent_characterPairCutoff ψ η hψ hη hs
  rw [MellinConvergent, characterPair_cutoff_mellin_kernel,
    integrableOn_indicator_iff measurableSet_Ioi] at h
  simpa only [Ioi_inter_Ioi, max_eq_left (show (0 : ℝ) ≤ 1 by norm_num)] using h

theorem differentiableAt_characterPairIntegral (ψ η : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) (hη : η ≠ 1) {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ (characterPairIntegral ψ η) s := by
  have hm : DifferentiableAt ℂ (mellin (characterPairCutoff ψ η)) (-s) := by
    apply mellin_differentiableAt_of_isBigO_rpow
      ((locallyIntegrable_characterPairCutoff ψ η hψ hη).locallyIntegrableOn _)
      (a := -(1 / 2)) (b := -s.re - 1)
    · simpa using characterPairCutoff_isBigO_atTop ψ η hψ hη
    · simp only [neg_re]; linarith
    · exact characterPairCutoff_isBigO_zero ψ η _
    · simp only [neg_re]; linarith
  simpa only [Function.comp_def, mellin_characterPairCutoff] using
    hm.comp s differentiableAt_id.neg

private theorem characterPair_sum_isBigO (ψ η : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) (hη : η ≠ 1) :
    (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N,
      (toArithmeticFunction (ψ ·) * toArithmeticFunction (η ·)) n) =O[atTop]
        (fun N : ℕ => (N : ℝ) ^ (1 / 2 : ℝ)) := by
  refine isBigO_iff.mpr ⟨3 * q, Eventually.of_forall fun N => ?_⟩
  simpa [Real.sqrt_eq_rpow, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)] using
      norm_sum_Icc_character_pair_convolution_le_three_mul_sqrt ψ η hψ hη N

omit [NeZero q] in
private theorem characterPair_factor_summable (ψ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (toArithmeticFunction (ψ ·)) s := by
  apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ hs
  intro n hn
  simpa only [toArithmeticFunction, ArithmeticFunction.coe_mk, hn, ↓reduceIte] using
    norm_le_one ψ n

private theorem characterPair_factor_LSeries (ψ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (toArithmeticFunction (ψ ·)) s = ψ.LFunction s := by
  rw [ψ.LFunction_eq_LSeries hs]
  exact LSeries_congr (fun hn => (ψ.apply_eq_toArithmeticFunction_apply hn).symm) s

set_option maxHeartbeats 800000 in
/-- Identification on the absolute-convergence half-plane. -/
theorem LFunction_mul_eq_characterPairIntegral_of_one_lt_re
    (ψ η : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (hη : η ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    ψ.LFunction s * η.LFunction s = s * characterPairIntegral ψ η s := by
  have hψs := characterPair_factor_summable ψ hs
  have hηs := characterPair_factor_summable η hs
  have hid := LSeries_eq_mul_integral
    (toArithmeticFunction (ψ ·) * toArithmeticFunction (η ·) : ArithmeticFunction ℂ)
    (r := 1 / 2) (by norm_num) (by linarith : 1 / 2 < s.re)
    (ArithmeticFunction.LSeriesSummable_mul hψs hηs)
    (characterPair_sum_isBigO ψ η hψ hη)
  rw [ArithmeticFunction.LSeries_mul' hψs hηs,
    characterPair_factor_LSeries ψ hs, characterPair_factor_LSeries η hs] at hid
  exact hid

/-- The actual product identity throughout `Re s > 1/2`, obtained by analytic
continuation of the convergent Mellin integral. -/
theorem LFunction_mul_eq_characterPairIntegral
    (ψ η : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (hη : η ≠ 1)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    ψ.LFunction s * η.LFunction s = s * characterPairIntegral ψ η s := by
  let U : Set ℂ := {z | 1 / 2 < z.re}
  let F : ℂ → ℂ := fun z => z * characterPairIntegral ψ η z
  let G : ℂ → ℂ := fun z => ψ.LFunction z * η.LFunction z
  have hUopen : IsOpen U := continuous_re.isOpen_preimage _ isOpen_Ioi
  have hFdiff : DifferentiableOn ℂ F U := by
    intro z hz
    exact (differentiableAt_id.mul
      (differentiableAt_characterPairIntegral ψ η hψ hη hz)).differentiableWithinAt
  have hF : AnalyticOnNhd ℂ F U := hFdiff.analyticOnNhd hUopen
  have hG : AnalyticOnNhd ℂ G U :=
    ((ψ.differentiable_LFunction hψ).mul (η.differentiable_LFunction hη)).differentiableOn
      |>.analyticOnNhd isOpen_univ |>.mono (subset_univ U)
  have hpre : IsPreconnected U := (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  have htwo : (2 : ℂ) ∈ U := by norm_num [U]
  have hevent : G =ᶠ[𝓝 (2 : ℂ)] F := by
    filter_upwards [eventually_of_mem
      ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
        (by norm_num : (1 : ℝ) < (2 : ℂ).re)) (fun z hz => hz)] with z hz
    exact LFunction_mul_eq_characterPairIntegral_of_one_lt_re ψ η hψ hη hz
  exact hG.eqOn_of_preconnected_of_eventuallyEq hF hpre htwo hevent hs

/-- At one, the Mellin integral is exactly the genuine product of L-values. -/
theorem LFunction_one_mul_eq_characterPairIntegral
    (ψ η : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (hη : η ≠ 1) :
    ψ.LFunction 1 * η.LFunction 1 = characterPairIntegral ψ η 1 := by
  simpa using LFunction_mul_eq_characterPairIntegral ψ η hψ hη
    (s := 1) (by norm_num)

end DirichletCharacter
