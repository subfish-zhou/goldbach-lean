import MathlibNt.Wu2008DoubleSieve.TruncatedSixthMassRectangle
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrability of the literal classical and admissible-gain kernels

Clipping is used only to establish measurability off the support. On
the actual polygon the clipping is the identity. The improvement is
handled as a bounded monotone effective coefficient minus the
continuous classical coefficient, not as a continuous function.
-/

namespace Wu2008DoubleSieve

open Set Real Filter MeasureTheory
open scoped Classical Topology
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

noncomputable def truncatedSixthMassClip (s : ℝ) : ℝ := max 2 (min 5 s)

noncomputable def truncatedSixthMassEffective (δ s : ℝ) : ℝ :=
  wuLowerCoefficient (truncatedSixthMassClip s) +
    wuImprovementLimit false δ (truncatedSixthMassClip s)

noncomputable def truncatedSixthMassAKernel (δ : ℝ) (v : ℝ × ℝ) : ℝ :=
  if truncatedSixthLowerRegion δ v.1 v.2 then
    wuLowerCoefficient (truncatedSixthLowerS δ v.1 v.2) /
      (v.1 * v.2 * (truncatedSixthLowerC δ - v.1 - v.2)) else 0

noncomputable def truncatedSixthMassHKernel (δ : ℝ) (v : ℝ × ℝ) : ℝ :=
  if truncatedSixthLowerAdmissibleRegion δ v.1 v.2 then
    wuImprovementLimit false δ (truncatedSixthLowerS δ v.1 v.2) /
      (v.1 * v.2 * (truncatedSixthLowerC δ - v.1 - v.2)) else 0

noncomputable def truncatedSixthMassKernelBound : ℝ :=
  10 / (truncatedSixthLowerAlpha * truncatedSixthLowerBeta * (2 * truncatedSixthLowerAlpha))

theorem truncatedSixthMass_clip_bounds (s : ℝ) :
    truncatedSixthMassClip s ∈ Icc 2 5 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem truncatedSixthMass_clip_eq {s : ℝ} (hs : s ∈ Icc 2 5) :
    truncatedSixthMassClip s = s := by
  simp only [truncatedSixthMassClip, min_eq_right hs.2, max_eq_right hs.1]

theorem truncatedSixthMass_effective_monotone {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) :
    Monotone (truncatedSixthMassEffective δ) := by
  intro s t hst
  exact truncatedSixthLower_effective_monotone hδ hδhi
    (truncatedSixthMass_clip_bounds s) (truncatedSixthMass_clip_bounds t)
    (max_le_max_left 2 (min_le_min_left 5 hst))

theorem truncatedSixthMass_clipped_classical_continuous :
    Continuous (fun s => wuLowerCoefficient (truncatedSixthMassClip s)) := by
  apply continuousOn_wuLowerCoefficient.comp_continuous
    (show Continuous truncatedSixthMassClip by unfold truncatedSixthMassClip; fun_prop)
  intro s
  have h := (truncatedSixthMass_clip_bounds s).1
  exact (by linarith : 0 < truncatedSixthMassClip s)

theorem truncatedSixthMass_regions_measurable (δ : ℝ) :
    MeasurableSet {v : ℝ × ℝ | truncatedSixthLowerRegion δ v.1 v.2} ∧
      MeasurableSet {v : ℝ × ℝ | truncatedSixthLowerAdmissibleRegion δ v.1 v.2} := by
  have hR : MeasurableSet {v : ℝ × ℝ | truncatedSixthLowerRegion δ v.1 v.2} := by
    unfold truncatedSixthLowerRegion
    exact (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_le measurable_fst measurable_const).inter
      ((measurableSet_le measurable_const measurable_snd).inter
      ((measurableSet_le measurable_snd measurable_const).inter
        (measurableSet_le (measurable_fst.add measurable_snd) measurable_const))))
  exact ⟨hR, hR.inter (measurableSet_le measurable_snd measurable_const)⟩

theorem truncatedSixthMass_kernels_measurable {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) :
    Measurable (truncatedSixthMassAKernel δ) ∧ Measurable (truncatedSixthMassHKernel δ) := by
  classical
  have hs : Measurable (fun v : ℝ × ℝ => truncatedSixthLowerS δ v.1 v.2) := by
    unfold truncatedSixthLowerS
    fun_prop
  have hd : Measurable (fun v : ℝ × ℝ =>
      v.1 * v.2 * (truncatedSixthLowerC δ - v.1 - v.2)) := by fun_prop
  have ha := truncatedSixthMass_clipped_classical_continuous.measurable.comp hs
  have he := (truncatedSixthMass_effective_monotone hδ hδhi).measurable.comp hs
  have hma : Measurable (fun v : ℝ × ℝ =>
      if truncatedSixthLowerRegion δ v.1 v.2 then
        wuLowerCoefficient (truncatedSixthMassClip (truncatedSixthLowerS δ v.1 v.2)) /
          (v.1 * v.2 * (truncatedSixthLowerC δ - v.1 - v.2)) else 0) :=
    (ha.div hd).ite (truncatedSixthMass_regions_measurable δ).1 measurable_const
  have hmh : Measurable (fun v : ℝ × ℝ =>
      if truncatedSixthLowerAdmissibleRegion δ v.1 v.2 then
        (truncatedSixthMassEffective δ (truncatedSixthLowerS δ v.1 v.2) -
          wuLowerCoefficient (truncatedSixthMassClip (truncatedSixthLowerS δ v.1 v.2))) /
          (v.1 * v.2 * (truncatedSixthLowerC δ - v.1 - v.2)) else 0) :=
    ((he.sub ha).div hd).ite (truncatedSixthMass_regions_measurable δ).2 measurable_const
  constructor
  · convert hma using 1
    funext v
    dsimp [truncatedSixthMassAKernel]
    split_ifs with hv
    · rw [truncatedSixthMass_clip_eq
        (truncatedSixthLower_region_bounds hδ.le hv).2.2.2]
    · rfl
  · convert hmh using 1
    funext v
    dsimp [truncatedSixthMassHKernel, truncatedSixthMassEffective]
    split_ifs with hv
    · rw [truncatedSixthMass_clip_eq
        (truncatedSixthLower_region_bounds hδ.le hv.1).2.2.2]
      ring
    · rfl

theorem truncatedSixthMass_kernels_bounds {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) (v : ℝ × ℝ) :
    (0 ≤ truncatedSixthMassAKernel δ v ∧
      truncatedSixthMassAKernel δ v ≤ truncatedSixthMassKernelBound) ∧
    (0 ≤ truncatedSixthMassHKernel δ v ∧
      truncatedSixthMassHKernel δ v ≤ truncatedSixthMassKernelBound) := by
  have hα := truncatedSixthLower_parameters.1
  have hβ := hα.trans truncatedSixthLower_parameters.2.1
  have hK : 0 ≤ truncatedSixthMassKernelBound := by
    unfold truncatedSixthMassKernelBound
    positivity
  have hpoint (hr : truncatedSixthLowerRegion δ v.1 v.2) :
      0 ≤ wuLowerCoefficient (truncatedSixthLowerS δ v.1 v.2) ∧
      wuLowerCoefficient (truncatedSixthLowerS δ v.1 v.2) ≤ 10 ∧
      0 ≤ wuImprovementLimit false δ (truncatedSixthLowerS δ v.1 v.2) ∧
      wuImprovementLimit false δ (truncatedSixthLowerS δ v.1 v.2) ≤ 10 ∧
      0 < v.1 * v.2 * (truncatedSixthLowerC δ - v.1 - v.2) ∧
      truncatedSixthLowerAlpha * truncatedSixthLowerBeta * (2 * truncatedSixthLowerAlpha) ≤
        v.1 * v.2 * (truncatedSixthLowerC δ - v.1 - v.2) := by
    have hb := truncatedSixthLower_region_bounds hδ.le hr
    have hs0 : 0 ≤ truncatedSixthLowerS δ v.1 v.2 := by linarith [hb.2.2.2.1]
    have hf := jr1965f_nonneg (show 0 < truncatedSixthLowerS δ v.1 v.2 by linarith [hb.2.2.2.1])
    have ha0 : 0 ≤ wuLowerCoefficient (truncatedSixthLowerS δ v.1 v.2) := by
      unfold wuLowerCoefficient
      positivity
    have hh := wuImprovementLimit_nonneg false (s := truncatedSixthLowerS δ v.1 v.2) hδ (by linarith)
      (by linarith [hb.2.2.2.1]) (by linarith [hb.2.2.2.2])
    have he := (truncatedSixthLower_effective_bounds hδ hδhi hb.2.2.2).2
    refine ⟨ha0, by linarith, hh, by linarith, ?_, ?_⟩
    · exact mul_pos (mul_pos hb.1 hb.2.1) ((by positivity : 0 < 2 * truncatedSixthLowerAlpha).trans_le hb.2.2.1)
    · exact mul_le_mul (mul_le_mul hr.1 hr.2.2.1 hβ.le hb.1.le)
        hb.2.2.1 (by positivity) (mul_nonneg hb.1.le hb.2.1.le)
  constructor
  · unfold truncatedSixthMassAKernel
    split_ifs with hv
    · obtain ⟨ha0, ha10, _, _, hd0, hd⟩ := hpoint hv
      refine ⟨div_nonneg ha0 hd0.le, ?_⟩
      exact div_le_div₀ (by norm_num) ha10 (by positivity) hd
    · exact ⟨le_rfl, hK⟩
  · unfold truncatedSixthMassHKernel
    split_ifs with hv
    · obtain ⟨_, _, hh0, hh10, hd0, hd⟩ := hpoint hv.1
      refine ⟨div_nonneg hh0 hd0.le, ?_⟩
      exact div_le_div₀ (by norm_num) hh10 (by positivity) hd
    · exact ⟨le_rfl, hK⟩

theorem truncatedSixthMass_kernels_integrable {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) :
    Integrable (truncatedSixthMassAKernel δ) ∧ Integrable (truncatedSixthMassHKernel δ) := by
  let R : Set (ℝ × ℝ) := Icc truncatedSixthLowerAlpha truncatedSixthLowerBeta ×ˢ
    Icc truncatedSixthLowerBeta truncatedSixthLowerSigma
  have hfin : volume R ≠ ⊤ := (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  have hsubA : Function.support (truncatedSixthMassAKernel δ) ⊆ R := by
    intro v hv
    by_cases h : truncatedSixthLowerRegion δ v.1 v.2
    · exact ⟨⟨h.1, h.2.1⟩, ⟨h.2.2.1, h.2.2.2.1⟩⟩
    · exact False.elim (hv (by simp [truncatedSixthMassAKernel, h]))
  have hsubH : Function.support (truncatedSixthMassHKernel δ) ⊆ R := by
    intro v hv
    by_cases h : truncatedSixthLowerAdmissibleRegion δ v.1 v.2
    · exact ⟨⟨h.1.1, h.1.2.1⟩, ⟨h.1.2.2.1, h.1.2.2.2.1⟩⟩
    · exact False.elim (hv (by simp [truncatedSixthMassHKernel, h]))
  have hm := truncatedSixthMass_kernels_measurable hδ hδhi
  constructor
  · apply (integrableOn_iff_integrable_of_support_subset hsubA).mp
    apply Measure.integrableOn_of_bounded hfin hm.1.aestronglyMeasurable
    filter_upwards [] with v
    simpa only [Real.norm_eq_abs, abs_of_nonneg (truncatedSixthMass_kernels_bounds hδ hδhi v).1.1]
      using (truncatedSixthMass_kernels_bounds hδ hδhi v).1.2
  · apply (integrableOn_iff_integrable_of_support_subset hsubH).mp
    apply Measure.integrableOn_of_bounded hfin hm.2.aestronglyMeasurable
    filter_upwards [] with v
    simpa only [Real.norm_eq_abs, abs_of_nonneg (truncatedSixthMass_kernels_bounds hδ hδhi v).2.1]
      using (truncatedSixthMass_kernels_bounds hδ hδhi v).2.2

theorem truncatedSixthMass_slices_integrable {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) (x : ℝ) :
    Integrable (fun y => truncatedSixthMassAKernel δ (x, y)) ∧
      Integrable (fun y => truncatedSixthMassHKernel δ (x, y)) := by
  have hm := truncatedSixthMass_kernels_measurable hδ hδhi
  have hcomp : Measurable (fun y : ℝ => (x, y)) := measurable_const.prodMk measurable_id
  have hfin : volume (Icc truncatedSixthLowerBeta truncatedSixthLowerSigma) ≠ ⊤ :=
    measure_Icc_lt_top.ne
  have hsuppA : Function.support (fun y => truncatedSixthMassAKernel δ (x, y)) ⊆
      Icc truncatedSixthLowerBeta truncatedSixthLowerSigma := by
    intro y hy
    by_cases h : truncatedSixthLowerRegion δ x y
    · exact ⟨h.2.2.1, h.2.2.2.1⟩
    · exact False.elim (hy (by simp [truncatedSixthMassAKernel, h]))
  have hsuppH : Function.support (fun y => truncatedSixthMassHKernel δ (x, y)) ⊆
      Icc truncatedSixthLowerBeta truncatedSixthLowerSigma := by
    intro y hy
    by_cases h : truncatedSixthLowerAdmissibleRegion δ x y
    · exact ⟨h.1.2.2.1, h.1.2.2.2.1⟩
    · exact False.elim (hy (by simp [truncatedSixthMassHKernel, h]))
  constructor
  · apply (integrableOn_iff_integrable_of_support_subset hsuppA).mp
    apply Measure.integrableOn_of_bounded (M := truncatedSixthMassKernelBound)
      hfin (hm.1.comp hcomp).aestronglyMeasurable
    filter_upwards [] with y
    simpa only [Function.comp_def, Real.norm_eq_abs, abs_of_nonneg (truncatedSixthMass_kernels_bounds hδ hδhi (x, y)).1.1]
      using (truncatedSixthMass_kernels_bounds hδ hδhi (x, y)).1.2
  · apply (integrableOn_iff_integrable_of_support_subset hsuppH).mp
    apply Measure.integrableOn_of_bounded (M := truncatedSixthMassKernelBound)
      hfin (hm.2.comp hcomp).aestronglyMeasurable
    filter_upwards [] with y
    simpa only [Function.comp_def, Real.norm_eq_abs, abs_of_nonneg (truncatedSixthMass_kernels_bounds hδ hδhi (x, y)).2.1]
      using (truncatedSixthMass_kernels_bounds hδ hδhi (x, y)).2.2

end Wu2008DoubleSieve
