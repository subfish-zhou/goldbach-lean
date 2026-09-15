import MathlibNt.Wu2008DoubleSieve.MotherPairGainData

namespace Wu2008DoubleSieve.MotherPair
open Set Real Filter MeasureTheory
open scoped Classical Topology Interval

theorem gain_endpoint_order {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) :
    (1/5:ℝ) ≤ 1/p.S ∧ 1/p.S ≤ upperP p j ∧ upperP p j ≤ 1/p.kappa3 ∧
    1/p.S ≤ lowerQ p j ∧ lowerQ p j ≤ upperQ p j ∧
    upperQ p j ≤ 1/p.kappa3 ∧ 1/p.kappa3 < 1/2 := by
  obtain ⟨ha, hab, hbc, hce, hef, hf⟩ := parameter_order h
  have he := hef.trans_lt hf
  cases j <;> simp only [upperP, lowerQ, upperQ] <;>
    exact ⟨ha, by linarith, by linarith, by linarith, by linarith, by linarith, he⟩

theorem pairRegion_bounds {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {t u : ℝ} (hv : PairRegion p j t u) :
    1/p.S ≤ t ∧ t ≤ 1/p.kappa3 ∧ t ≤ u ∧ u ≤ 1/p.kappa3 := by
  obtain ⟨_, _, hbc, hce, _, _⟩ := parameter_order h
  cases j <;> simp only [PairRegion] at hv <;>
    exact ⟨hv.1, by linarith [hv.2.1], by linarith [hv.2.1, hv.2.2.1],
      by linarith [hv.2.2.2]⟩

theorem gain_ratio_mem {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {t u : ℝ} (hv : (t,u) ∈ gainRegion p j) :
    Hratio p j t u ∈ Icc 1 3 := by
  have hb := pairRegion_bounds h j hv.1
  have hd := legal_domain h.three_le_S h.S_le_five hb.1 hb.2.2.1 hv.2.1 hv.2.2
  cases j <;> simp only [Hratio] <;> first | exact hd.2.2.2.1 | exact hd.2.2.2.2

theorem gain_clip_eq {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {t u δ : ℝ} (hv : (t,u) ∈ gainRegion p j) :
    gamma5GainH δ (Hratio p j t u) = wuImprovementLimit true δ (Hratio p j t u) := by
  exact congrArg (wuImprovementLimit true δ) (gamma5Gain_clip_eq (gain_ratio_mem h j hv))

theorem gain_region_measurable (p : SecondFunctionalParameters) (j : Term) :
    MeasurableSet (gainRegion p j) := by
  have hpair : MeasurableSet {v : ℝ × ℝ | PairRegion p j v.1 v.2} := by
    cases j <;> unfold PairRegion <;>
      apply (measurableSet_le measurable_const measurable_fst).inter <;>
      apply (measurableSet_le measurable_fst measurable_const).inter <;>
      apply MeasurableSet.inter
    all_goals first
      | exact measurableSet_le measurable_fst measurable_snd
      | exact measurableSet_le measurable_const measurable_snd
      | exact measurableSet_le measurable_snd measurable_const
  exact hpair.inter ((measurableSet_le (measurable_const.mul measurable_snd)
    measurable_const).inter (measurableSet_le
      (measurable_snd.add (measurable_const.mul measurable_fst)) measurable_const))

theorem gain_ratio_measurable (p : SecondFunctionalParameters) (j : Term) :
    Measurable (fun v : ℝ × ℝ => Hratio p j v.1 v.2) := by
  cases j <;> unfold Hratio <;> fun_prop

theorem gain_kernel_measurable (p : SecondFunctionalParameters) (j : Term)
    {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) : Measurable (gainKernel p j δ) := by
  exact (((gamma5Gain_H_antitone hδ hδhi).measurable.comp (gain_ratio_measurable p j)).div
    (by fun_prop)).ite (gain_region_measurable p j) measurable_const

theorem pair_denominator_bound {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {t u : ℝ} (hv : PairRegion p j t u) :
    0 < t*u*(1-t-u) ∧ (1/25:ℝ)*(1-2*(1/p.kappa3)) ≤ t*u*(1-t-u) := by
  obtain ⟨ha, _, _, _, _, _, hU⟩ := gain_endpoint_order h j
  obtain ⟨ht, htU, htu, huU⟩ := pairRegion_bounds h j hv
  have ht5 : (1/5:ℝ) ≤ t := ha.trans ht
  have hu5 : (1/5:ℝ) ≤ u := ht5.trans htu
  have hg : 0 < 1-2*(1/p.kappa3) := by linarith
  have hd : 1-2*(1/p.kappa3) ≤ 1-t-u := by linarith
  have hprod : (1/25:ℝ) ≤ t*u := by nlinarith [mul_le_mul ht5 hu5 (by norm_num) (by linarith)]
  exact ⟨mul_pos (by nlinarith) (hg.trans_le hd),
    mul_le_mul hprod hd hg.le (by nlinarith)⟩

theorem gain_kernel_bounds {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) (v : ℝ × ℝ) :
    0 ≤ gainKernel p j δ v ∧ gainKernel p j δ v ≤ 25/(1-2*(1/p.kappa3)) := by
  have hg : 0 < 1-2*(1/p.kappa3) := by
    have := (gain_endpoint_order h j).2.2.2.2.2.2
    linarith
  unfold gainKernel
  split_ifs with hv
  · have hd := pair_denominator_bound h j hv.1
    have hh := gamma5Gain_H_bounds hδ hδhi (Hratio p j v.1 v.2)
    refine ⟨div_nonneg hh.1 hd.1.le, ?_⟩
    exact (div_le_div₀ (by norm_num) hh.2 (mul_pos (by norm_num) hg) hd.2).trans_eq
      (by field_simp)
  · exact ⟨le_rfl, by positivity⟩

theorem gain_kernel_support {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) (δ : ℝ) : Function.support (gainKernel p j δ) ⊆
    Icc (1/p.S) (1/p.kappa3) ×ˢ Icc (1/p.S) (1/p.kappa3) := by
  intro v hv
  by_cases hr : v ∈ gainRegion p j
  · obtain ⟨ht, htU, htu, huU⟩ := pairRegion_bounds h j hr.1
    exact ⟨⟨ht,htU⟩,⟨ht.trans htu,huU⟩⟩
  · exact False.elim (hv (by simp [gainKernel, hr]))

theorem gain_kernel_integrable {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    Integrable (gainKernel p j δ) := by
  apply (integrableOn_iff_integrable_of_support_subset (gain_kernel_support h j δ)).mp
  apply Measure.integrableOn_of_bounded
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
    (gain_kernel_measurable p j hδ hδhi).aestronglyMeasurable
  exact Eventually.of_forall (fun v => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (gain_kernel_bounds h j hδ hδhi v).1]
      using (gain_kernel_bounds h j hδ hδhi v).2)

theorem gain_slice_integrable {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) (t : ℝ) :
    Integrable (fun u => gainKernel p j δ (t,u)) := by
  have hs : Function.support (fun u => gainKernel p j δ (t,u)) ⊆
      Icc (1/p.S) (1/p.kappa3) := fun _ hu => (gain_kernel_support h j δ hu).2
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  apply Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
    ((gain_kernel_measurable p j hδ hδhi).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact Eventually.of_forall (fun u => by
    simpa only [Function.comp_def, id_eq, Real.norm_eq_abs,
      abs_of_nonneg (gain_kernel_bounds h j hδ hδhi (t,u)).1]
      using (gain_kernel_bounds h j hδ hδhi (t,u)).2)

theorem gain_kernel_eq_literal {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {δ t u : ℝ} (hv : PairRegion p j t u) :
    gainKernel p j δ (t,u) = gainLiteral p j δ t u := by
  by_cases hl : gamma5GainLegal t u
  · have hh := gain_clip_eq h j (δ := δ) ⟨hv,hl⟩
    simp only [gainKernel, gainRegion, mem_ofPred_eq, hv, hl, and_self, if_true,
      gainLiteral, hh]
  · simp [gainKernel, gainRegion, gainLiteral, hl]

end Wu2008DoubleSieve.MotherPair
