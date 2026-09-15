import Wu18938Campaign.M3.FullMassFamily
import MathlibNt.Wu2008DoubleSieve.MotherPairGainRegularity
import MathlibNt.Wu2008DoubleSieve.TruncatedSixthClosureGrid
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

namespace Wu18938Campaign.M3

open Finset Set Real Filter MeasureTheory Wu2008DoubleSieve
open Wu2008DoubleSieve.MotherPair WuPaper.R2Gamma5
open scoped Classical Topology Interval

def fullDomain (p : SecondFunctionalParameters) : Set (ℝ × ℝ) :=
  {v | 1 / p.S ≤ v.1 ∧ v.1 ≤ v.2 ∧ v.2 ≤ 1 / p.kappa2}

def fullKernel (p : SecondFunctionalParameters) (δ : ℝ) : ℝ × ℝ → ℝ :=
  (fullDomain p).indicator
    (fun v => gamma5GainH δ (p.S * (1 - v.1 - v.2)) * gainSmooth p v)

def fullIntegral (p : SecondFunctionalParameters) (δ : ℝ) : ℝ :=
  ∫ v : ℝ × ℝ, fullKernel p δ v

theorem full_kernel_value {p : SecondFunctionalParameters} (hp : FullParameters p)
    (δ : ℝ) {v : ℝ × ℝ} (hv : v ∈ fullDomain p) :
    fullKernel p δ v =
      wuImprovementLimit true δ (p.S * (1 - v.1 - v.2)) /
        (v.1 * v.2 * (1 - v.1 - v.2)) := by
  have h1 : v.1 ∈ Icc (1 / p.S) (1 / p.kappa2) := ⟨hv.1, hv.2.1.trans hv.2.2⟩
  have h2 : v.2 ∈ Icc (1 / p.S) (1 / p.kappa2) := ⟨hv.1.trans hv.2.1, hv.2.2⟩
  have hk := (parameter_order hp.toAnalyticParameters).2.2.2.1.le
  rw [fullKernel, indicator_of_mem hv, gamma5GainH,
    gamma5Gain_clip_eq (full_ratio_mem hp h1 h2),
    gain_smooth_eq ⟨h1.1, h1.2.trans hk⟩ ⟨h2.1, h2.2.trans hk⟩]
  exact (div_eq_mul_one_div _ _).symm

private def inner (p : SecondFunctionalParameters) (n : ℕ) : Finset (ℕ × ℕ) :=
  (truncatedSixthClosureCells n).filter (fun j =>
    1 / p.S < truncatedSixthClosureLo n j.1 ∧
    truncatedSixthClosureHi n j.1 < truncatedSixthClosureLo n j.2 ∧
    truncatedSixthClosureHi n j.2 < 1 / p.kappa2)

private def cell (p : SecondFunctionalParameters) (n : ℕ)
    (j : {j // j ∈ inner p n}) : FullCell p where
  A := truncatedSixthClosureLo n j.val.1
  B := truncatedSixthClosureHi n j.val.1
  C := truncatedSixthClosureLo n j.val.2
  D := truncatedSixthClosureHi n j.val.2
  bounds := by
    obtain ⟨ha, hbc, hd⟩ := (mem_filter.mp j.property).2
    have hab := truncatedSixthClosure_lo_lt_hi n j.val.1
    have hcd := truncatedSixthClosure_lo_lt_hi n j.val.2
    exact ⟨ha.le, hab.le, (hbc.trans (hcd.trans hd)).le,
      (ha.trans (hab.trans hbc)).le, hcd.le, hd.le⟩
  separated := (mem_filter.mp j.property).2.2.1.le

private def family (p : SecondFunctionalParameters) (n : ℕ) : Finset (FullCell p) :=
  univ.image (cell p n)

private theorem cell_subset {p : SecondFunctionalParameters} {n : ℕ} {j : ℕ × ℕ}
    (hj : j ∈ inner p n) : truncatedSixthClosureCell n j ⊆ fullDomain p := by
  intro v hv
  obtain ⟨ha, hbc, hd⟩ := (mem_filter.mp hj).2
  exact ⟨ha.le.trans hv.1.1, hv.1.2.le.trans (hbc.le.trans hv.2.1),
    hv.2.2.le.trans hd.le⟩

private theorem family_disjoint (p : SecondFunctionalParameters) (n : ℕ) :
    (family p n : Set (FullCell p)).Pairwise (fun r s => Disjoint r.region s.region) := by
  intro r hr s hs hrs
  obtain ⟨i, _, rfl⟩ := mem_image.mp hr
  obtain ⟨j, _, rfl⟩ := mem_image.mp hs
  apply Set.disjoint_left.mpr
  intro v hv hw
  have he : i.val = j.val := truncatedSixthClosure_cell_unique hv hw
  exact hrs (congrArg (cell p n) (Subtype.ext he))

private def approx (p : SecondFunctionalParameters) (δ : ℝ) (n : ℕ)
    (v : ℝ × ℝ) : ℝ :=
  ∑ j ∈ inner p n, (truncatedSixthClosureCell n j).indicator
    (fun v => gamma5GainH δ
      (p.S * (1 - truncatedSixthClosureLo n j.1 - truncatedSixthClosureLo n j.2)) *
        gainSmooth p v) v

private theorem approx_at {p : SecondFunctionalParameters} {δ : ℝ} {n : ℕ}
    {j : ℕ × ℕ} {v : ℝ × ℝ} (hj : j ∈ inner p n)
    (hv : v ∈ truncatedSixthClosureCell n j) :
    approx p δ n v = gamma5GainH δ
      (p.S * (1 - truncatedSixthClosureLo n j.1 - truncatedSixthClosureLo n j.2)) *
        gainSmooth p v := by
  unfold approx
  rw [sum_eq_single j]
  · exact indicator_of_mem hv _
  · intro l _ hlj
    exact indicator_of_notMem (fun hl => hlj (truncatedSixthClosure_cell_unique hl hv)) _
  · exact fun hn => False.elim (hn hj)

private theorem approx_zero {p : SecondFunctionalParameters} {δ : ℝ} {n : ℕ}
    {v : ℝ × ℝ} (h : ∀ j ∈ inner p n, v ∉ truncatedSixthClosureCell n j) :
    approx p δ n v = 0 :=
  sum_eq_zero (fun j hj => indicator_of_notMem (h j hj) _)

private theorem approx_measurable {p : SecondFunctionalParameters} (hp : FullParameters p)
    (δ : ℝ) (n : ℕ) : Measurable (approx p δ n) := by
  apply Finset.measurable_sum
  intro j _
  exact (measurable_const.mul
    (gain_smooth_continuous hp.toAnalyticParameters).measurable).indicator
      (truncatedSixthClosure_cell_measurable n j)

private theorem approx_bound {p : SecondFunctionalParameters} (hp : FullParameters p)
    {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) (n : ℕ) (v : ℝ × ℝ) :
    ‖approx p δ n v‖ ≤ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1).indicator
      (fun _ => 25 / (1 - 2 * (1 / p.kappa3))) v := by
  by_cases hex : ∃ j ∈ inner p n, v ∈ truncatedSixthClosureCell n j
  · obtain ⟨j, hj, hv⟩ := hex
    have hu := truncatedSixthClosure_cell_mem (mem_filter.mp hj).1 hv
    rw [approx_at hj hv, indicator_of_mem
      (show v ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 from
        ⟨⟨hu.1.1, hu.1.2.le⟩, ⟨hu.2.1, hu.2.2.le⟩⟩)]
    have hh := gamma5Gain_H_bounds hδ hδhi
      (p.S * (1 - truncatedSixthClosureLo n j.1 - truncatedSixthClosureLo n j.2))
    have hk := gain_smooth_bounds hp.toAnalyticParameters v
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hh.1 hk.1)]
    exact (mul_le_of_le_one_left hk.1 hh.2).trans hk.2
  · rw [approx_zero (by simpa only [not_exists, not_and] using hex), norm_zero]
    exact indicator_nonneg (fun _ _ =>
      (gain_smooth_bounds hp.toAnalyticParameters v).1.trans
        (gain_smooth_bounds hp.toAnalyticParameters v).2) _

private theorem approx_tendsto {p : SecondFunctionalParameters} (hp : FullParameters p)
    {δ : ℝ} {v : ℝ × ℝ}
    (hs : v ∈ fullDomain p → 1 / p.S < v.1 ∧ v.1 < v.2 ∧ v.2 < 1 / p.kappa2)
    (hc : ContinuousAt (gamma5GainH δ) (p.S * (1 - v.1 - v.2))) :
    Tendsto (fun n => approx p δ n v) atTop (𝓝 (fullKernel p δ v)) := by
  by_cases hv : v ∈ fullDomain p
  · obtain ⟨ha, hxy, hb⟩ := hs hv
    have he := parameter_order hp.toAnalyticParameters
    have hx0 : 0 ≤ v.1 := by linarith [he.1, hv.1]
    have hy0 : 0 ≤ v.2 := hx0.trans hv.2.1
    have hb1 : 1 / p.kappa2 < 1 := by
      linarith [he.2.2.2.1, he.2.2.2.2.1, he.2.2.2.2.2]
    have hx := truncatedSixthClosure_corner_tendsto hx0
    have hy := truncatedSixthClosure_corner_tendsto hy0
    have hsample : Tendsto (fun n => p.S *
        (1 - truncatedSixthClosureLo n (truncatedSixthClosureIndex n v.1) -
          truncatedSixthClosureLo n (truncatedSixthClosureIndex n v.2)))
        atTop (𝓝 (p.S * (1 - v.1 - v.2))) :=
      ((tendsto_const_nhds.sub hx.1).sub hy.1).const_mul p.S
    rw [fullKernel, indicator_of_mem hv]
    apply ((hc.tendsto.comp hsample).mul_const (gainSmooth p v)).congr'
    filter_upwards [hx.1.eventually (lt_mem_nhds ha),
      Filter.Tendsto.eventually_lt hx.2 hy.1 hxy,
      hy.2.eventually (gt_mem_nhds hb)] with n hn1 hn2 hn3
    have hi : (truncatedSixthClosureIndex n v.1, truncatedSixthClosureIndex n v.2) ∈
        inner p n := by
      exact mem_filter.mpr ⟨mem_product.mpr
        ⟨mem_range.mpr (truncatedSixthClosure_index_lt n hx0
            (hv.2.1.trans_lt (hb.trans hb1))),
          mem_range.mpr (truncatedSixthClosure_index_lt n hy0 (hb.trans hb1))⟩,
        hn1, hn2, hn3⟩
    exact (approx_at hi
      ⟨truncatedSixthClosure_index_bounds n hx0,
        truncatedSixthClosure_index_bounds n hy0⟩).symm
  · have hz (n : ℕ) : approx p δ n v = 0 :=
      approx_zero (fun j hj hjv => hv (cell_subset hj hjv))
    simp only [hz, fullKernel, indicator_of_notMem hv]
    exact tendsto_const_nhds

private theorem integral_tendsto {p : SecondFunctionalParameters} (hp : FullParameters p)
    {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    Tendsto (fun n => ∫ v : ℝ × ℝ, approx p δ n v) atTop
      (𝓝 (fullIntegral p δ)) := by
  apply tendsto_integral_of_dominated_convergence
    ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1).indicator
      (fun _ => 25 / (1 - 2 * (1 / p.kappa3))))
  · exact fun n => (approx_measurable hp δ n).aestronglyMeasurable
  · exact (integrableOn_const
      (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne).integrable_indicator
        (measurableSet_Icc.prod measurableSet_Icc)
  · exact fun n => Eventually.of_forall (approx_bound hp hδ hδhi n)
  · filter_upwards [gamma5Gain_vertical_ne_ae (1 / p.S),
      gamma5Gain_affine_ne_ae 1 (-1) 0 (by norm_num),
      gamma5Gain_affine_ne_ae 0 1 (1 / p.kappa2) (by norm_num),
      gain_H_pullback_ae hp.toAnalyticParameters .gammaFive hδ hδhi]
        with v ha he hb hc
    apply approx_tendsto hp _ hc
    intro hv
    simp only [zero_mul, one_mul, zero_add] at hb
    refine ⟨lt_of_le_of_ne hv.1 ha.symm, ?_, lt_of_le_of_ne hv.2.2 hb⟩
    apply lt_of_le_of_ne hv.2.1
    intro h
    apply he
    rw [h]
    ring

private theorem smooth_cell_integral {p : SecondFunctionalParameters} (hp : FullParameters p)
    (r : FullCell p) :
    (∫ v : ℝ × ℝ, r.region.indicator (gainSmooth p) v) =
      rectIntegral r.A r.B r.C r.D := by
  have hi : IntegrableOn (gainSmooth p) r.region :=
    ((gain_smooth_continuous hp.toAnalyticParameters).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set
        (Set.prod_mono Ico_subset_Icc_self Ico_subset_Icc_self)
  rw [FullCell.region, integral_indicator (measurableSet_Ico.prod measurableSet_Ico)]
  rw [show (∫ v in Ico r.A r.B ×ˢ Ico r.C r.D, gainSmooth p v) =
    ∫ t in Ico r.A r.B, ∫ u in Ico r.C r.D, gainSmooth p (t, u) from
      setIntegral_prod _ hi]
  simp_rw [integral_Ico_eq_integral_Ioc]
  simp_rw [← intervalIntegral.integral_of_le r.bounds.2.2.2.2.1]
  rw [← intervalIntegral.integral_of_le r.bounds.2.1]
  unfold rectIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc r.A r.B := by
    simpa only [uIcc_of_le r.bounds.2.1] using ht
  rw [max_eq_left (ht'.2.trans r.separated), min_eq_right r.bounds.2.2.2.2.1]
  apply intervalIntegral.integral_congr
  intro u hu
  have hu' : u ∈ Icc r.C r.D := by
    simpa only [uIcc_of_le r.bounds.2.2.2.2.1] using hu
  have hk := (parameter_order hp.toAnalyticParameters).2.2.2.1.le
  exact gain_smooth_eq
    ⟨r.bounds.1.trans ht'.1, ht'.2.trans (r.bounds.2.2.1.trans hk)⟩
    ⟨r.bounds.2.2.2.1.trans hu'.1, hu'.2.trans (r.bounds.2.2.2.2.2.trans hk)⟩

private theorem integral_sum {p : SecondFunctionalParameters} (hp : FullParameters p)
    (δ : ℝ) (n : ℕ) :
    (∫ v : ℝ × ℝ, approx p δ n v) =
      ∑ r ∈ family p n, wuImprovementLimit true δ r.sample *
        rectIntegral r.A r.B r.C r.D := by
  have hinj : Function.Injective (cell p n) := by
    intro i j he
    apply Subtype.ext
    have hA := congrArg FullCell.A he
    have hC := congrArg FullCell.C he
    change truncatedSixthClosureLo n i.val.1 = truncatedSixthClosureLo n j.val.1 at hA
    change truncatedSixthClosureLo n i.val.2 = truncatedSixthClosureLo n j.val.2 at hC
    apply Prod.ext
    · exact_mod_cast (div_left_inj' (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0)).mp hA
    · exact_mod_cast (div_left_inj' (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0)).mp hC
  unfold family approx
  rw [sum_image hinj.injOn]
  rw [integral_finsetSum _ (fun j _ => ?_)]
  · rw [← Finset.sum_attach]
    change (∑ j : {j // j ∈ inner p n}, _) = _
    apply sum_congr rfl
    intro j _
    let r := cell p n j
    have hEq : (truncatedSixthClosureCell n j.val).indicator
        (fun v => gamma5GainH δ r.sample * gainSmooth p v) =
        fun v => gamma5GainH δ r.sample * r.region.indicator (gainSmooth p) v := by
      funext v
      change r.region.indicator (fun v => gamma5GainH δ r.sample * gainSmooth p v) v =
        gamma5GainH δ r.sample * r.region.indicator (gainSmooth p) v
      by_cases hv : v ∈ r.region
      · simp only [indicator_of_mem hv]
      · simp only [indicator_of_notMem hv, mul_zero]
    change (∫ v : ℝ × ℝ, (truncatedSixthClosureCell n j.val).indicator
      (fun v => gamma5GainH δ r.sample * gainSmooth p v) v) =
        wuImprovementLimit true δ r.sample * rectIntegral r.A r.B r.C r.D
    rw [hEq, integral_const_mul, smooth_cell_integral hp r, gamma5GainH, FullCell.sample,
      gamma5Gain_clip_eq (full_ratio_mem hp
        ⟨r.bounds.1, r.bounds.2.1.trans r.bounds.2.2.1⟩
        ⟨r.bounds.2.2.2.1, r.bounds.2.2.2.2.1.trans r.bounds.2.2.2.2.2⟩)]
  · apply IntegrableOn.integrable_indicator _ (truncatedSixthClosure_cell_measurable n _)
    exact (((continuous_const.mul
      (gain_smooth_continuous hp.toAnalyticParameters)).continuousOn.integrableOn_compact
        (isCompact_Icc.prod isCompact_Icc)).mono_set
          (Set.prod_mono Ico_subset_Icc_self Ico_subset_Icc_self))

theorem full_integral_sufficient_family {p : SecondFunctionalParameters} (hp : FullParameters p)
    {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ F : Finset (FullCell p),
      (F : Set (FullCell p)).Pairwise (fun r s => Disjoint r.region s.region) ∧
      fullIntegral p δ - ε < ∑ r ∈ F,
        wuImprovementLimit true δ r.sample * rectIntegral r.A r.B r.C r.D := by
  obtain ⟨n, hn⟩ := ((integral_tendsto hp hδ hδhi).eventually
    (lt_mem_nhds (sub_lt_self _ hε))).exists
  exact ⟨family p n, family_disjoint p n, by rwa [integral_sum hp δ n] at hn⟩

theorem fullHMass_integral_lower {p : SecondFunctionalParameters} (hp : FullParameters p)
    (k : ℕ) {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        (fullIntegral p δ - ε) *
            boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
          fullHMass p N δ (convolutionWuWindows N Δ V)
            (termLabels p .gammaFive N δ (convolutionWuWindows N Δ V)) := by
  obtain ⟨F, hF, hgain⟩ := full_integral_sufficient_family hp hδ
    (by linarith : δ < 1 / 2) (half_pos hε)
  obtain ⟨T, hT4, hT⟩ := fullHMass_family_lower hp F hF k hδ hδhi (half_pos hε)
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb
  have hθ := gamma5Mass_theta_nonneg (by omega : 2 ≤ N) hδ (by linarith) hb
  exact (mul_le_mul_of_nonneg_right (by linarith : fullIntegral p δ - ε ≤
    (∑ r ∈ F, wuImprovementLimit true δ r.sample * rectIntegral r.A r.B r.C r.D) -
      ε / 2) hθ).trans (hT N hN i Δ V hb)

end Wu18938Campaign.M3
