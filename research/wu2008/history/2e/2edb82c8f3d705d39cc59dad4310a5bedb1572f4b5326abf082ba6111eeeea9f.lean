import MathlibNt.Wu2008DoubleSieve.Gamma5MassIntegrability
import MathlibNt.Wu2008DoubleSieve.ImprovementMonotonicity
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Convex.Measure

/-!
# The literal legal-domain improvement kernel

The coefficient is the existing final upper improvement, at fixed delta.
Clipping only extends it measurably off the actual source triangle.
-/

namespace Wu2008DoubleSieve

open Set Real Filter MeasureTheory
open scoped Classical Topology Interval
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

noncomputable def gamma5GainV (t u : ℝ) : ℝ := gamma5ClassicalS * (1 - t - u)

def gamma5GainLegal (t u : ℝ) : Prop := 2 * u ≤ 1 ∧ u + 2 * t ≤ 1

def gamma5GainTriangle (v : ℝ × ℝ) : Prop :=
  gamma5MassA ≤ v.1 ∧ v.1 ≤ v.2 ∧ v.2 ≤ gamma5ClassicalB

def gamma5GainRegion : Set (ℝ × ℝ) :=
  {v | gamma5GainTriangle v ∧ gamma5GainLegal v.1 v.2}

noncomputable def gamma5GainClip (s : ℝ) : ℝ := max 1 (min 3 s)

noncomputable def gamma5GainH (δ s : ℝ) : ℝ :=
  wuImprovementLimit true δ (gamma5GainClip s)

noncomputable def gamma5GainLiteral (δ t u : ℝ) : ℝ :=
  if gamma5GainLegal t u then
    wuImprovementLimit true δ (gamma5GainV t u) / (t * u * (1 - t - u)) else 0

noncomputable def gamma5GainIntegral (δ : ℝ) : ℝ :=
  ∫ t in gamma5MassA..gamma5ClassicalB,
    ∫ u in t..gamma5ClassicalB, gamma5GainLiteral δ t u

noncomputable def gamma5GainKernel (δ : ℝ) (v : ℝ × ℝ) : ℝ :=
  if v ∈ gamma5GainRegion then
    gamma5GainH δ (gamma5GainV v.1 v.2) / (v.1 * v.2 * (1 - v.1 - v.2)) else 0

theorem gamma5Gain_triangle_bounds {v : ℝ × ℝ} (hv : gamma5GainTriangle v) :
    v.1 ∈ Icc gamma5MassA gamma5ClassicalB ∧
    v.2 ∈ Icc gamma5MassA gamma5ClassicalB ∧
    1 < gamma5GainV v.1 v.2 ∧ gamma5GainV v.1 v.2 < 3 ∧
    0 < v.1 * v.2 * (1 - v.1 - v.2) := by
  have hx : v.1 ≤ gamma5ClassicalB := hv.2.1.trans hv.2.2
  have hy : gamma5MassA ≤ v.2 := hv.1.trans hv.2.1
  have ha : (0 : ℝ) < gamma5MassA := by norm_num [gamma5MassA, gamma5ClassicalS]
  have hb : 2 * gamma5ClassicalB < 1 := by norm_num [gamma5ClassicalB]
  refine ⟨⟨hv.1, hx⟩, ⟨hy, hv.2.2⟩, ?_, ?_, ?_⟩
  · dsimp [gamma5GainV, gamma5ClassicalS]
    norm_num [gamma5MassA, gamma5ClassicalS, gamma5ClassicalB] at hv hx hy
    linarith [hv.2.2]
  · dsimp [gamma5GainV, gamma5ClassicalS]
    norm_num [gamma5MassA, gamma5ClassicalS] at hv hy
    linarith [hv.1]
  · exact mul_pos (mul_pos (ha.trans_le hv.1) (ha.trans_le hy)) (by linarith [hv.2.2])

theorem gamma5Gain_clip_bounds (s : ℝ) : gamma5GainClip s ∈ Icc 1 3 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem gamma5Gain_clip_eq {s : ℝ} (hs : s ∈ Icc 1 3) : gamma5GainClip s = s := by
  simp only [gamma5GainClip, min_eq_right hs.2, max_eq_right hs.1]

theorem gamma5Gain_H_bounds {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) (s : ℝ) :
    0 ≤ gamma5GainH δ s ∧ gamma5GainH δ s ≤ 1 := by
  have hs := gamma5Gain_clip_bounds s
  have h := wuImprovementLimit_bounds hδ hδhi hs.1 (by linarith [hs.2])
  have he : wuUpperCoefficient (gamma5GainClip s) = 1 :=
    jr1965F_normalized_initial (by linarith [hs.1]) hs.2
  exact ⟨h.1, h.2.1.trans_eq he⟩

theorem gamma5Gain_H_antitone {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    Antitone (gamma5GainH δ) := by
  intro s t hst
  exact wuImprovementLimit_upper_antitone_initial hδ hδhi
    (gamma5Gain_clip_bounds s) (gamma5Gain_clip_bounds t)
    (max_le_max_left _ (min_le_min_left _ hst))

theorem gamma5Gain_region_measurable : MeasurableSet gamma5GainRegion := by
  unfold gamma5GainRegion gamma5GainTriangle gamma5GainLegal
  exact ((measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_le measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const))).inter
    ((measurableSet_le (measurable_const.mul measurable_snd) measurable_const).inter
      (measurableSet_le (measurable_snd.add (measurable_const.mul measurable_fst)) measurable_const))

theorem gamma5Gain_kernel_measurable {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    Measurable (gamma5GainKernel δ) := by
  have hv : Measurable (fun v : ℝ × ℝ => gamma5GainV v.1 v.2) := by
    unfold gamma5GainV
    fun_prop
  exact (((gamma5Gain_H_antitone hδ hδhi).measurable.comp hv).div
    (by fun_prop)).ite gamma5Gain_region_measurable measurable_const

theorem gamma5Gain_kernel_bounds {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (v : ℝ × ℝ) :
    0 ≤ gamma5GainKernel δ v ∧ gamma5GainKernel δ v ≤ 400 := by
  unfold gamma5GainKernel
  split_ifs with hv
  · have hb := gamma5Gain_triangle_bounds hv.1
    have hw := gamma5Gain_H_bounds hδ hδhi (gamma5GainV v.1 v.2)
    have ha : (1 / 10 : ℝ) ≤ v.1 := gamma5Mass_constants.1.trans hb.1.1
    have hc : (1 / 10 : ℝ) ≤ v.2 := gamma5Mass_constants.1.trans hb.2.1.1
    have hgap : (1 / 4 : ℝ) ≤ 1 - v.1 - v.2 := by
      have := gamma5Mass_constants.2.2.2
      linarith [hb.1.2, hb.2.1.2]
    have hd : (1 / 10 : ℝ) * (1 / 10) * (1 / 4) ≤ v.1 * v.2 * (1 - v.1 - v.2) :=
      mul_le_mul (mul_le_mul ha hc (by norm_num) (by linarith)) hgap (by norm_num)
        (mul_nonneg (by linarith) (by linarith))
    exact ⟨div_nonneg hw.1 hb.2.2.2.2.le,
      (div_le_div₀ (by norm_num) hw.2 (by norm_num) hd).trans_eq (by norm_num)⟩
  · exact ⟨le_rfl, by norm_num⟩

theorem gamma5Gain_kernel_support (δ : ℝ) :
    Function.support (gamma5GainKernel δ) ⊆
      Icc gamma5MassA gamma5ClassicalB ×ˢ Icc gamma5MassA gamma5ClassicalB := by
  intro v hv
  by_cases h : v ∈ gamma5GainRegion
  · exact ⟨(gamma5Gain_triangle_bounds h.1).1, (gamma5Gain_triangle_bounds h.1).2.1⟩
  · exact False.elim (hv (by simp [gamma5GainKernel, h]))

theorem gamma5Gain_kernel_integrable {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    Integrable (gamma5GainKernel δ) := by
  apply (integrableOn_iff_integrable_of_support_subset (gamma5Gain_kernel_support δ)).mp
  apply Measure.integrableOn_of_bounded
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
    (gamma5Gain_kernel_measurable hδ hδhi).aestronglyMeasurable
  exact Eventually.of_forall (fun v => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (gamma5Gain_kernel_bounds hδ hδhi v).1]
      using (gamma5Gain_kernel_bounds hδ hδhi v).2)

theorem gamma5Gain_slice_integrable {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) (t : ℝ) :
    Integrable (fun u => gamma5GainKernel δ (t, u)) := by
  have hs : Function.support (fun u => gamma5GainKernel δ (t, u)) ⊆
      Icc gamma5MassA gamma5ClassicalB :=
    fun _ hu => (gamma5Gain_kernel_support δ hu).2
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  apply Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
    ((gamma5Gain_kernel_measurable hδ hδhi).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact Eventually.of_forall (fun u => by
    simpa only [Function.comp_def, Real.norm_eq_abs,
      abs_of_nonneg (gamma5Gain_kernel_bounds hδ hδhi (t, u)).1]
      using (gamma5Gain_kernel_bounds hδ hδhi (t, u)).2)

theorem gamma5Gain_kernel_eq_literal {δ t u : ℝ} (ht : gamma5MassA ≤ t)
    (htu : t ≤ u) (hu : u ≤ gamma5ClassicalB) :
    gamma5GainKernel δ (t, u) = gamma5GainLiteral δ t u := by
  have hb := gamma5Gain_triangle_bounds (v := (t, u)) ⟨ht, htu, hu⟩
  simp only [gamma5GainKernel, gamma5GainRegion, mem_setOf_eq, gamma5GainTriangle,
    ht, htu, hu, and_self, true_and, gamma5GainLiteral, gamma5GainH,
    gamma5Gain_clip_eq ⟨hb.2.2.1.le, hb.2.2.2.1.le⟩]

end Wu2008DoubleSieve
