import MathlibNt.Wu2008DoubleSieve.Omega2EffectiveIntegral

/-!
# The first functional gain: the actual weighted integral and ordered limits

Wu04, original TeX lines 2004–2020 and 2260–2286 (Lemma 5.1), uses the
kernel `h(t*u)/(u*(1-u))`. Here `h` is the existing finite-threshold,
fixed-depth, or final lower improvement, never a new model. Effective
coefficient monotonicity, not continuity of the gains, supplies integrability.
The threshold limit is taken at fixed positive depth, and only then is the
depth limit taken along `k + 1`. Delta remains fixed throughout.

These are analytic transport statements only: they do not assert the
functional inequality, remove its delta penalty, or assert positive gain.
-/

namespace Wu2008DoubleSieve

open Set Real MeasureTheory Filter
open scoped Interval Topology

/-- The existing `/x` gain bound transports to Wu's first weighted kernel. -/
theorem firstFunctionalGain_kernel_norm_le {s t u q : ℝ}
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hu : u ∈ uIcc (1 - 1 / s) (1 - 1 / t))
    (hq : ‖q / (t * u)‖ ≤ 10) :
    ‖q / (u * (1 - u))‖ ≤ 250 := by
  obtain ⟨hu2, hu5, _⟩ := omega2_integral_domain hs hst ht ht5 hu
  have hu0 : 0 < u := by linarith
  have ht0 : 0 < t := by linarith
  have hv0 : 0 < 1 - u := by linarith
  rw [norm_div, Real.norm_eq_abs (t * u),
    abs_of_pos (mul_pos ht0 hu0)] at hq
  have hq' : ‖q‖ ≤ 10 * (t * u) := (div_le_iff₀ (mul_pos ht0 hu0)).mp hq
  rw [norm_div, Real.norm_eq_abs (u * (1 - u)),
    abs_of_pos (mul_pos hu0 hv0)]
  apply (div_le_iff₀ (mul_pos hu0 hv0)).2
  have hweight : 10 * t ≤ 250 * (1 - u) := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hweight hu0.le]

/-- The continuous lower coefficient with the same kernel as the raw gain. -/
theorem firstFunctionalGain_coefficient_intervalIntegrable {s t : ℝ}
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : 3 ≤ t) (ht5 : t ≤ 5) :
    IntervalIntegrable (fun u => wuLowerCoefficient (t * u) / (u * (1 - u)))
      volume (1 - 1 / s) (1 - 1 / t) := by
  have hc : ContinuousOn (fun u => wuLowerCoefficient (t * u))
      (uIcc (1 - 1 / s) (1 - 1 / t)) := by
    apply continuousOn_wuLowerCoefficient.comp (continuous_const.mul continuous_id).continuousOn
    intro u hu
    have h := omega2_integral_domain hs hst ht ht5 hu
    change 0 < t * u
    linarith [h.2.2.1]
  apply (hc.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id)) ?_).intervalIntegrable
  intro u hu
  have h := omega2_integral_domain hs hst ht ht5 hu
  exact mul_ne_zero (by change u ≠ 0; linarith [h.1])
    (by change 1 - u ≠ 0; linarith [h.2.1])

/-- A common threshold in the source parameter supplies the weighted raw
gain integral; no continuity of the finite-threshold gain is used. -/
theorem firstFunctionalGain_eventually_intervalIntegrable (k : ℕ) (hk : 1 ≤ k)
    {δ s t : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : 3 ≤ t) (ht5 : t ≤ 5) :
    ∀ᶠ N0 : ℕ in atTop,
      IntervalIntegrable (fun u =>
        wuImprovementAt false k δ (t * u) N0 / (u * (1 - u)))
        volume (1 - 1 / s) (1 - 1 / t) := by
  filter_upwards [wu_effective_threshold_uniform_monotone false k hk hδ hδhi] with N0 hN0
  have hm : MonotoneOn
      (fun x => wuLowerCoefficient x + wuImprovementAt false k δ x N0) (Icc 1 10) := by
    simpa only [Bool.false_eq_true, if_false] using hN0
  have hi := omega2_integral_intervalIntegrable hm hs hst ht ht5
  have hc := firstFunctionalGain_coefficient_intervalIntegrable hs hst ht ht5
  convert hi.sub hc using 1
  ext u
  ring

/-- Fixed-depth gain integrability follows by subtracting the continuous
coefficient from the transported monotone effective coefficient. -/
theorem firstFunctionalGain_fixedDepth_intervalIntegrable (k : ℕ) (hk : 1 ≤ k)
    {δ s t : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : 3 ≤ t) (ht5 : t ≤ 5) :
    IntervalIntegrable (fun u =>
      wuImprovementAtInfinity false k δ (t * u) / (u * (1 - u)))
      volume (1 - 1 / s) (1 - 1 / t) := by
  have hm : MonotoneOn
      (fun x => wuLowerCoefficient x + wuImprovementAtInfinity false k δ x) (Icc 1 10) := by
    intro x hx y hy hxy
    exact wu_effective_lower_fixed_depth_mono k hk hδ hδhi hx.1 hxy hy.2
  have hi := omega2_integral_intervalIntegrable hm hs hst ht ht5
  have hc := firstFunctionalGain_coefficient_intervalIntegrable hs hst ht ht5
  convert hi.sub hc using 1
  ext u
  ring

/-- Integrability of the final actual gain, at fixed delta. -/
theorem firstFunctionalGain_limit_intervalIntegrable
    {δ s t : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : 3 ≤ t) (ht5 : t ≤ 5) :
    IntervalIntegrable (fun u =>
      wuImprovementLimit false δ (t * u) / (u * (1 - u)))
      volume (1 - 1 / s) (1 - 1 / t) := by
  have hm : MonotoneOn
      (fun x => wuLowerCoefficient x + wuImprovementLimit false δ x) (Icc 1 10) := by
    intro x hx y hy hxy
    exact wu_effective_lower_limit_mono hδ hδhi hx.1 hxy hy.2
  have hi := omega2_integral_intervalIntegrable hm hs hst ht ht5
  have hc := firstFunctionalGain_coefficient_intervalIntegrable hs hst ht ht5
  convert hi.sub hc using 1
  ext u
  ring

/-- The source condition keeps the logarithm away from its singularity,
including when the two integration endpoints coincide. -/
theorem firstFunctionalGain_log_intervalIntegrable {s t : ℝ}
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hratio : 2 ≤ t - t / s) :
    IntervalIntegrable (fun u => log (t * u - 1) / (u * (1 - u)))
      volume (1 - 1 / s) (1 - 1 / t) := by
  have hab : 1 - 1 / s ≤ 1 - 1 / t :=
    sub_le_sub_left (one_div_le_one_div_of_le (by linarith) hst) 1
  have hc : ContinuousOn (fun u => log (t * u - 1))
      (uIcc (1 - 1 / s) (1 - 1 / t)) := by
    apply ((continuousOn_const.mul continuousOn_id).sub continuousOn_const).log
    intro u hu
    rw [uIcc_of_le hab] at hu
    have hmul := mul_le_mul_of_nonneg_left hu.1 (show 0 ≤ t by linarith)
    have heq : t * (1 - 1 / s) = t - t / s := by ring
    rw [heq] at hmul
    change t * u - 1 ≠ 0
    linarith
  apply (hc.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id)) ?_).intervalIntegrable
  intro u hu
  have h := omega2_integral_domain hs hst ht ht5 hu
  exact mul_ne_zero (by change u ≠ 0; linarith [h.1])
    (by change 1 - u ≠ 0; linarith [h.2.1])

/-- At fixed positive depth, the actual finite-threshold log-plus-gain
integral eventually splits into its two integrable summands. -/
theorem firstFunctionalGain_integral_eventually_split (k : ℕ) (hk : 1 ≤ k)
    {δ s t : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hs : 2 ≤ s) (hs3 : s ≤ 3) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hratio : 2 ≤ t - t / s) :
    ∀ᶠ N0 : ℕ in atTop,
      (∫ u in (1 - 1 / s)..(1 - 1 / t),
        (log (t * u - 1) + wuImprovementAt false k δ (t * u) N0) / (u * (1 - u))) =
      (∫ u in (1 - 1 / s)..(1 - 1 / t), log (t * u - 1) / (u * (1 - u))) +
      (∫ u in (1 - 1 / s)..(1 - 1 / t),
        wuImprovementAt false k δ (t * u) N0 / (u * (1 - u))) := by
  filter_upwards [firstFunctionalGain_eventually_intervalIntegrable k hk hδ hδhi
    hs (hs3.trans ht) ht ht5] with N0 hN0
  simpa only [add_div] using intervalIntegral.integral_add
    (firstFunctionalGain_log_intervalIntegrable hs (hs3.trans ht) ht ht5 hratio) hN0

/-- Inner limit: the threshold tends to infinity at a fixed depth `k ≥ 1`.
The majorant is eventual uniformly over the whole integration interval. -/
theorem firstFunctionalGain_integral_threshold_limit (k : ℕ) (hk : 1 ≤ k)
    {δ s t : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : 3 ≤ t) (ht5 : t ≤ 5) :
    Tendsto (fun N0 : ℕ => ∫ u in (1 - 1 / s)..(1 - 1 / t),
      wuImprovementAt false k δ (t * u) N0 / (u * (1 - u)))
      atTop (𝓝 (∫ u in (1 - 1 / s)..(1 - 1 / t),
        wuImprovementAtInfinity false k δ (t * u) / (u * (1 - u)))) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 250)
  · filter_upwards [firstFunctionalGain_eventually_intervalIntegrable k hk hδ hδhi
      hs hst ht ht5] with N0 hN0
    exact hN0.def'.aestronglyMeasurable
  · filter_upwards [wuImprovementAt_uniform_div_norm_bound false k hk hδ hδhi] with N0 hN0
    apply ae_of_all
    intro u hu
    have hu' := uIoc_subset_uIcc hu
    have hdomain := (omega2_integral_domain hs hst ht ht5 hu').2.2
    exact firstFunctionalGain_kernel_norm_le hs hst ht ht5 hu'
      (hN0 (t * u) hdomain.1 hdomain.2)
  · exact intervalIntegrable_const
  · apply ae_of_all
    intro u hu
    have hdomain := (omega2_integral_domain hs hst ht ht5 (uIoc_subset_uIcc hu)).2.2
    exact (wuImprovementAt_tendsto false k hk hδ hδhi
      hdomain.1 hdomain.2).div_const (u * (1 - u))

/-- Outer limit: after the threshold limit, depths follow exactly the
existing `k + 1` convention. Delta is not taken to a limit. -/
theorem firstFunctionalGain_integral_depth_limit
    {δ s t : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : 3 ≤ t) (ht5 : t ≤ 5) :
    Tendsto (fun k : ℕ => ∫ u in (1 - 1 / s)..(1 - 1 / t),
      wuImprovementAtInfinity false (k + 1) δ (t * u) / (u * (1 - u)))
      atTop (𝓝 (∫ u in (1 - 1 / s)..(1 - 1 / t),
        wuImprovementLimit false δ (t * u) / (u * (1 - u)))) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 250)
  · exact Eventually.of_forall (fun k =>
      (firstFunctionalGain_fixedDepth_intervalIntegrable (k + 1) (by omega)
        hδ hδhi hs hst ht ht5).def'.aestronglyMeasurable)
  · apply Eventually.of_forall
    intro k
    apply ae_of_all
    intro u hu
    have hu' := uIoc_subset_uIcc hu
    have hdomain := (omega2_integral_domain hs hst ht ht5 hu').2.2
    exact firstFunctionalGain_kernel_norm_le hs hst ht ht5 hu'
      (wuImprovementAtInfinity_div_norm_le_ten false (k + 1) (by omega)
        hδ hδhi hdomain.1 hdomain.2)
  · exact intervalIntegrable_const
  · apply ae_of_all
    intro u hu
    have hdomain := (omega2_integral_domain hs hst ht ht5 (uIoc_subset_uIcc hu)).2.2
    exact (wuImprovementAtInfinity_tendsto false hδ hδhi
      hdomain.1 hdomain.2).div_const (u * (1 - u))

/-- The oriented final gain integral is nonnegative because its endpoints
are ordered and its actual gain and kernel are nonnegative on the interval. -/
theorem firstFunctionalGain_integral_nonneg
    {δ s t : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : 3 ≤ t) (ht5 : t ≤ 5) :
    0 ≤ ∫ u in (1 - 1 / s)..(1 - 1 / t),
      wuImprovementLimit false δ (t * u) / (u * (1 - u)) := by
  have hab : 1 - 1 / s ≤ 1 - 1 / t :=
    sub_le_sub_left (one_div_le_one_div_of_le (by linarith) hst) 1
  apply intervalIntegral.integral_nonneg hab
  intro u hu
  have hu' : u ∈ uIcc (1 - 1 / s) (1 - 1 / t) := by
    rwa [uIcc_of_le hab]
  have h := omega2_integral_domain hs hst ht ht5 hu'
  exact div_nonneg (wuImprovementLimit_nonneg false hδ hδhi h.2.2.1 h.2.2.2)
    (mul_nonneg (by linarith [h.1]) (by linarith [h.2.1]))

end Wu2008DoubleSieve
