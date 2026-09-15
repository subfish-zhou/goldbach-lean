import FifthHIntegral
import BaseHCross

namespace Wu2008DoubleSieve
open Set Real Filter MeasureTheory
open scoped Classical Topology

/-- Uniform lower endpoint supplied by the already proved original h cross propagation. -/
noncomputable def fifthHSeed : ℝ := (11 / 2 - 5) ^ 3 / 378000

/-- A certified full-triangle minorant, not the value of the complete h integral. -/
noncomputable def fifthHGain : ℝ :=
  4 * fifthHSeed * (truncatedSixthLowerBeta - truncatedSixthLowerAlpha) ^ 2

noncomputable def fifthHOnlyKernel (δ : ℝ) (v : ℝ × ℝ) : ℝ :=
  if v ∈ fifthPairRegion then
    wuImprovementLimit false δ (truncatedSixthLowerS δ v.1 v.2) /
      (v.1 * v.2 * (truncatedSixthLowerC δ - v.1 - v.2)) else 0

/-- The entire actual h contribution, without truncating its support. -/
noncomputable def fifthHOnlyIntegral (δ : ℝ) : ℝ :=
  4 * ∫ v : ℝ × ℝ, fifthHOnlyKernel δ v

theorem fifthHSeed_pos : 0 < fifthHSeed := by norm_num [fifthHSeed]

theorem fifthHGain_pos : 0 < fifthHGain := by
  unfold fifthHGain
  exact mul_pos (mul_pos (by norm_num) fifthHSeed_pos)
    (sq_pos_of_pos (sub_pos.mpr truncatedSixthLower_parameters.2.1))

theorem fifthH_uniform_seed {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000)
    {v : ℝ × ℝ} (hv : v ∈ fifthPairRegion) :
    fifthHSeed ≤ wuImprovementLimit false δ (truncatedSixthLowerS δ v.1 v.2) := by
  have hb := fifthPair_region_bounds hδ.le hδhi hv
  exact (BaseHGain.h_extended hδ hδhi (by norm_num : (4 : ℝ) ≤ 5)
    (by norm_num : (5 : ℝ) ≤ 11 / 2)).trans
    (wuImprovementLimit_lower_antitone hδ (by linarith)
      ⟨hb.2.2.2.1, by linarith [hb.2.2.2.2]⟩ (by norm_num) hb.2.2.2.2)

theorem fifthH_denominator_bounds {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000)
    {v : ℝ × ℝ} (hv : v ∈ fifthPairRegion) :
    0 < v.1 * v.2 * (truncatedSixthLowerC δ - v.1 - v.2) ∧
      v.1 * v.2 * (truncatedSixthLowerC δ - v.1 - v.2) ≤ 1 / 2 := by
  have hb := fifthPair_region_bounds hδ.le hδhi hv
  have hp := truncatedSixthLower_parameters
  have hz : 0 < truncatedSixthLowerC δ - v.1 - v.2 := by linarith [hb.2.2.1]
  have hx1 : v.1 ≤ 1 := by linarith [hv.2.1, hv.2.2, hp.2.2.1, hp.2.2.2.1]
  have hy1 : v.2 ≤ 1 := by linarith [hv.2.2, hp.2.2.1, hp.2.2.2.1]
  have hxy : v.1 * v.2 ≤ 1 := by nlinarith [mul_le_mul hx1 hy1 hb.2.1.le (by norm_num : (0 : ℝ) ≤ 1)]
  have hC : truncatedSixthLowerC δ ≤ 1 / 2 := by
    unfold truncatedSixthLowerC
    linarith
  refine ⟨mul_pos (mul_pos hb.1 hb.2.1) hz, ?_⟩
  have hm := mul_le_mul_of_nonneg_right hxy hz.le
  nlinarith

theorem fifthH_only_kernel_eq_sub {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) :
    fifthHOnlyKernel δ = fun v => fifthHKernel δ v - fifthPairKernel δ v := by
  funext v
  by_cases hv : v ∈ fifthPairRegion
  · rw [fifthH_kernel_original hδ.le hδhi hv, fifthPair_kernel_original hδ.le hδhi hv]
    simp only [fifthHOnlyKernel, if_pos hv]
    ring
  · simp [fifthHOnlyKernel, fifthHKernel, fifthPairKernel, hv]

/-- Genuine integrability is established before any additive splitting. -/
theorem fifthH_only_integrable {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) :
    Integrable (fifthHOnlyKernel δ) := by
  rw [fifthH_only_kernel_eq_sub hδ hδhi]
  exact (fifthH_kernel_integrable hδ hδhi).sub (fifthPair_kernel_integrable hδ.le hδhi)

theorem fifthH_actual_integral_split {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) :
    fifthHFdelta δ = fifthPairFdelta δ + fifthHOnlyIntegral δ := by
  rw [fifthH_literal_integral hδ hδhi, fifthPair_literal_integral hδ.le hδhi]
  unfold fifthHOnlyIntegral
  rw [fifthH_only_kernel_eq_sub hδ hδhi,
    integral_sub (fifthH_kernel_integrable hδ hδhi) (fifthPair_kernel_integrable hδ.le hδhi)]
  ring

/-- Fubini on the original triangle for an actually integrable supported function. -/
theorem fifthH_triangle_integral {f : ℝ × ℝ → ℝ} (hi : Integrable f)
    (hsupp : Function.support f ⊆ fifthPairRegion) :
    (∫ v : ℝ × ℝ, f v) =
      ∫ y in truncatedSixthLowerAlpha..truncatedSixthLowerBeta,
        ∫ x in truncatedSixthLowerAlpha..y, f (x,y) := by
  have hz : ∀ v, v ∉ fifthPairRegion → f v = 0 := by
    intro v hv
    by_contra h
    exact hv (hsupp h)
  have houter : Function.support (fun y => ∫ x, f (x,y)) ⊆
      Icc truncatedSixthLowerAlpha truncatedSixthLowerBeta := by
    intro y hy
    by_contra h
    apply hy
    change (∫ x, f (x,y)) = 0
    have he : (fun x => f (x,y)) = 0 := by
      funext x
      exact hz (x,y) (fun hv => h ⟨hv.1.trans hv.2.1, hv.2.2⟩)
    rw [he]
    simp
  rw [show (∫ v : ℝ × ℝ, f v) = ∫ y, ∫ x, f (x,y) from integral_prod_symm _ hi,
    truncatedSixthMass_integral_eq_interval truncatedSixthLower_parameters.2.1.le houter]
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le truncatedSixthLower_parameters.2.1.le] at hy
  apply truncatedSixthMass_integral_eq_interval hy.1
  intro x hx
  exact ⟨(hsupp hx).1, (hsupp hx).2.1⟩

/-- Literal iterated h integral, retaining all the original s-delta and denominator parameters. -/
theorem fifthH_only_literal_integral {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) :
    fifthHOnlyIntegral δ =
      4 * ∫ y in truncatedSixthLowerAlpha..truncatedSixthLowerBeta,
        ∫ x in truncatedSixthLowerAlpha..y,
          wuImprovementLimit false δ (truncatedSixthLowerS δ x y) /
            (x * y * (truncatedSixthLowerC δ - x - y)) := by
  unfold fifthHOnlyIntegral
  rw [fifthH_triangle_integral (fifthH_only_integrable hδ hδhi)
    (by intro v hv; by_contra hn; exact hv (by simp [fifthHOnlyKernel, hn]))]
  congr 1
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le truncatedSixthLower_parameters.2.1.le] at hy
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le hy.1] at hx
  exact if_pos (show (x,y) ∈ fifthPairRegion from ⟨hx.1, hx.2, hy.2⟩)

/-- Exact triangle area calculation; no numerical integration or new cutoff. -/
theorem fifthH_triangle_constant (c : ℝ) :
    (∫ v : ℝ × ℝ, fifthPairRegion.indicator (fun _ => c) v) =
      c * (truncatedSixthLowerBeta - truncatedSixthLowerAlpha) ^ 2 / 2 := by
  have hi : Integrable (fifthPairRegion.indicator (fun _ : ℝ × ℝ => c)) :=
    (integrableOn_const fifthPair_region_compact.measure_lt_top.ne).integrable_indicator
      fifthPair_region_compact.isClosed.measurableSet
  rw [fifthH_triangle_integral hi (by intro v hv; by_contra hn; exact hv (Set.indicator_of_notMem hn _))]
  have he : (∫ y in truncatedSixthLowerAlpha..truncatedSixthLowerBeta,
      ∫ x in truncatedSixthLowerAlpha..y, fifthPairRegion.indicator (fun _ => c) (x,y)) =
      ∫ y in truncatedSixthLowerAlpha..truncatedSixthLowerBeta,
        (y - truncatedSixthLowerAlpha) * c := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le truncatedSixthLower_parameters.2.1.le] at hy
    have hh : (∫ x in truncatedSixthLowerAlpha..y,
        fifthPairRegion.indicator (fun _ => c) (x,y)) = ∫ x in truncatedSixthLowerAlpha..y, c := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hy.1] at hx
      exact Set.indicator_of_mem (show (x,y) ∈ fifthPairRegion from ⟨hx.1, hx.2, hy.2⟩) _
    dsimp only
    rw [hh, intervalIntegral.integral_const, smul_eq_mul]
  have hsub : (∫ x in truncatedSixthLowerAlpha..truncatedSixthLowerBeta,
      x - truncatedSixthLowerAlpha) =
      (∫ x in truncatedSixthLowerAlpha..truncatedSixthLowerBeta, x) -
        ∫ _x in truncatedSixthLowerAlpha..truncatedSixthLowerBeta, truncatedSixthLowerAlpha :=
    intervalIntegral.integral_sub (continuous_id.intervalIntegrable _ _) intervalIntegrable_const
  rw [he, intervalIntegral.integral_mul_const, hsub,
    integral_id, intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem fifthH_only_uniform_gain {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) :
    fifthHGain ≤ fifthHOnlyIntegral δ := by
  have hi : Integrable (fifthPairRegion.indicator (fun _ : ℝ × ℝ => 2 * fifthHSeed)) :=
    (integrableOn_const fifthPair_region_compact.measure_lt_top.ne).integrable_indicator
      fifthPair_region_compact.isClosed.measurableSet
  have hm := integral_mono hi (fifthH_only_integrable hδ hδhi) (fun v => by
    by_cases hv : v ∈ fifthPairRegion
    · rw [Set.indicator_of_mem hv]
      simp only [fifthHOnlyKernel, if_pos hv]
      have hb := fifthH_denominator_bounds hδ hδhi hv
      apply (le_div_iff₀ hb.1).mpr
      have hh := fifthH_uniform_seed hδ hδhi hv
      have hmul := mul_le_mul_of_nonneg_left hb.2
        (show 0 ≤ 2 * fifthHSeed from mul_nonneg (by norm_num) fifthHSeed_pos.le)
      nlinarith
    · simp [fifthHOnlyKernel, hv])
  rw [fifthH_triangle_constant] at hm
  unfold fifthHGain fifthHOnlyIntegral
  linarith

theorem fifthH_Fdelta_uniform_gain {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) :
    fifthPairFdelta δ + fifthHGain ≤ fifthHFdelta δ := by
  rw [fifthH_actual_integral_split hδ hδhi]
  exact add_le_add_right (fifthH_only_uniform_gain hδ hδhi) _

theorem fifthH_Fdelta_strict {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) :
    fifthPairFdelta δ < fifthHFdelta δ :=
  (lt_add_of_pos_right _ fifthHGain_pos).trans_le (fifthH_Fdelta_uniform_gain hδ hδhi)

end Wu2008DoubleSieve
