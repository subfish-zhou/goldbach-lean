import NodeActual

noncomputable section
namespace WuPaper.RMapMSigma
open Real Set MeasureTheory NodeExtension Wu2008DoubleSieve
open scoped Interval BigOperators

theorem sigma_definition (a b c : ℝ) :
    sigma a b c = ∫ v in a..b, log (c / (v - 1)) / v := rfl

theorem sigma0_definition (t : ℝ) :
    sigma0 t = sigma 3 (t + 2) (t + 1) / (1 - sigma 3 5 4) := rfl

theorem sigma_denominator_pos : 0 < 1 - sigma 3 5 4 :=
  sub_pos.mpr D0_lt_one

private theorem log_div_continuous :
    ContinuousOn (fun v : ℝ => log (v - 1) / v) (Icc 3 5) := by
  apply ContinuousOn.div
  · exact (continuousOn_id.sub continuousOn_const).log
      (fun v hv => by dsimp; linarith [hv.1])
  · exact continuousOn_id
  · intro v hv
    dsimp
    linarith [hv.1]

theorem sigma_numerator_identity {t : ℝ} (ht : t ∈ Icc 1 3) :
    sigma 3 (t + 2) (t + 1) =
      log (t + 1) * log ((t + 2) / 3) -
        ∫ v in (3 : ℝ)..(t + 2), log (v - 1) / v := by
  have hab : (3 : ℝ) ≤ t + 2 := by linarith [ht.1]
  have hrec := (reciprocal_continuous (by norm_num : (0 : ℝ) < 3) hab).intervalIntegrable
    (μ := volume)
  have hlog : IntervalIntegrable (fun v : ℝ => log (v - 1) / v) volume 3 (t + 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact log_div_continuous.mono (Icc_subset_Icc le_rfl (by linarith [ht.2]))
  unfold sigma
  calc
    _ = ∫ v in (3 : ℝ)..(t + 2),
        log (t + 1) * (1 / v) - log (v - 1) / v := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [uIcc_of_le hab] at hv
      rw [log_div (by linarith [ht.1] : t + 1 ≠ 0)
        (by linarith [hv.1] : v - 1 ≠ 0)]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_sub (hrec.const_mul _) hlog,
        intervalIntegral.integral_const_mul,
        integral_one_div_of_pos (by norm_num : (0 : ℝ) < 3)
          (by linarith [ht.1])]

theorem sigma0_continuous : ContinuousOn sigma0 (Icc 1 3) := by
  have hi : IntegrableOn (fun v : ℝ => log (v - 1) / v) (uIcc 3 5) := by
    rw [uIcc_of_le (by norm_num : (3 : ℝ) ≤ 5)]
    exact log_div_continuous.integrableOn_Icc
  have hp := intervalIntegral.continuousOn_primitive_interval hi
  have hc : ContinuousOn
      (fun t : ℝ => ∫ v in (3 : ℝ)..(t + 2), log (v - 1) / v) (Icc 1 3) := by
    apply hp.comp (continuousOn_id.add continuousOn_const)
    intro t ht
    rw [uIcc_of_le (by norm_num : (3 : ℝ) ≤ 5)]
    constructor <;> linarith [ht.1, ht.2]
  have h1 : ContinuousOn (fun t : ℝ => log (t + 1)) (Icc 1 3) :=
    (continuousOn_id.add continuousOn_const).log
      (fun t ht => by dsimp; linarith [ht.1])
  have h2 : ContinuousOn (fun t : ℝ => log ((t + 2) / 3)) (Icc 1 3) :=
    ((continuousOn_id.add continuousOn_const).div_const _).log
      (fun t ht => ne_of_gt (div_pos (by linarith [ht.1]) (by norm_num)))
  apply (((h1.mul h2).sub hc).div_const (1 - D0)).congr
  intro t ht
  exact congrArg (fun x => x / (1 - D0)) (sigma_numerator_identity ht).symm

theorem sigma_weight_integrable {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 1 3) :
    IntervalIntegrable (fun t => f t * sigma0 t / t) volume 1 3 := by
  have hc : ContinuousOn sigma0 (uIcc 1 3) := by
    simpa only [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] using sigma0_continuous
  exact profile_div_integrable (hf.mul_continuousOn hc)

theorem indicator_interval_integral {a b c d : ℝ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) (f : ℝ → ℝ) :
    (∫ t in a..b, (Icc c d).indicator f t) = ∫ t in c..d, f t := by
  rw [integral_Icc (hac.trans (hcd.trans hdb)),
    MeasureTheory.integral_indicator measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc,
    inter_eq_left.mpr (Icc_subset_Icc hac hdb), ← integral_Icc hcd]

def upperKernel (s t : ℝ) : ℝ :=
  sigma0 t / t * log (4 / (s - 1)) +
    (Icc (s - 2) 3).indicator (fun _ => (1 : ℝ)) t / t *
      log ((t + 1) / (s - 1))

theorem upperKernel_nonneg {s t : ℝ} (hs : s ∈ Icc 3 5) (ht : t ∈ Icc 1 3) :
    0 ≤ upperKernel s t := by
  apply add_nonneg
  · exact mul_nonneg (div_nonneg (sigma0_nonneg ht) (by linarith [ht.1]))
      (log_nonneg ((le_div_iff₀ (by linarith [hs.1] : 0 < s - 1)).2
        (by linarith [hs.2])))
  · by_cases hm : t ∈ Icc (s - 2) 3
    · rw [indicator_of_mem hm]
      exact mul_nonneg (by positivity)
        (log_nonneg ((le_div_iff₀ (by linarith [hs.1] : 0 < s - 1)).2
          (by linarith [hm.1])))
    · rw [indicator_of_notMem hm]
      simp

private theorem weighted_log_integrable {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 1 3) {s : ℝ} (hs : s ∈ Icc 3 5) :
    IntervalIntegrable (fun t => f t / t * log ((t + 1) / (s - 1))) volume 1 3 := by
  apply (profile_div_integrable hf).mul_continuousOn
  rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]
  exact ((continuousOn_id.add continuousOn_const).div_const _).log
    (fun t ht => ne_of_gt (div_pos (by linarith [ht.1]) (by linarith [hs.1])))

theorem upperKernel_integrable {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 1 3) {s : ℝ} (hs : s ∈ Icc 3 5) :
    IntervalIntegrable (fun t => f t * upperKernel s t) volume 1 3 := by
  have ht := weighted_log_integrable hf hs
  have hit : IntervalIntegrable ((Icc (s - 2) 3).indicator
      (fun t => f t / t * log ((t + 1) / (s - 1)))) volume 1 3 := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (1 : ℝ) ≤ 3)).mpr
    exact ((intervalIntegrable_iff_integrableOn_Icc_of_le
      (by norm_num : (1 : ℝ) ≤ 3)).mp ht).indicator measurableSet_Icc
  convert ((sigma_weight_integrable hf).mul_const (log (4 / (s - 1)))).add hit using 1
  ext t
  by_cases hm : t ∈ Icc (s - 2) 3 <;>
    simp only [upperKernel, indicator_of_mem, indicator_of_notMem, hm] <;> ring

theorem upperKernel_identity {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 1 3) {s : ℝ} (hs : s ∈ Icc 3 5) :
    (∫ t in (1 : ℝ)..3, f t * upperKernel s t) = eProfile f s := by
  have htail := weighted_log_integrable hf hs
  have hi : IntervalIntegrable ((Icc (s - 2) 3).indicator
      (fun t => f t / t * log ((t + 1) / (s - 1)))) volume 1 3 := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (1 : ℝ) ≤ 3)).mpr
    exact ((intervalIntegrable_iff_integrableOn_Icc_of_le
      (by norm_num : (1 : ℝ) ≤ 3)).mp htail).indicator measurableSet_Icc
  have he (t : ℝ) : f t * upperKernel s t =
      (f t * sigma0 t / t) * log (4 / (s - 1)) +
        (Icc (s - 2) 3).indicator
          (fun t => f t / t * log ((t + 1) / (s - 1))) t := by
    by_cases hm : t ∈ Icc (s - 2) 3 <;>
      simp only [upperKernel, indicator_of_mem, indicator_of_notMem, hm] <;> ring
  simp_rw [he]
  rw [intervalIntegral.integral_add
      ((sigma_weight_integrable hf).mul_const _) hi,
    intervalIntegral.integral_mul_const,
    indicator_interval_integral (by linarith [hs.1]) (by linarith [hs.2]) le_rfl]
  rfl

theorem lemma61 {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10) :
    (∫ t in (1 : ℝ)..3, wuImprovementLimit true δ t * (sigma0 t / t)) ≤
      wuImprovementLimit false δ 4 := by
  simpa only [aProfile, mul_div_assoc] using (actual_continuous_extension hd hdhi).1

theorem lemma62 {δ s : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10) (hs : s ∈ Icc 3 5) :
    (∫ t in (1 : ℝ)..3, wuImprovementLimit true δ t * upperKernel s t) ≤
      wuImprovementLimit true δ s := by
  rw [upperKernel_identity (wuImprovementLimit_intervalIntegrable true hd
    (by linarith : δ < 1 / 2) (by norm_num) (by norm_num) (by norm_num)) hs]
  exact (actual_continuous_extension hd hdhi).2.2 s hs

end WuPaper.RMapMSigma

#check @WuPaper.RMapMSigma.sigma_definition
#check @WuPaper.RMapMSigma.sigma0_definition
#check @WuPaper.RMapMSigma.sigma_denominator_pos
#check @WuPaper.RMapMSigma.sigma_numerator_identity
#check @WuPaper.RMapMSigma.sigma0_continuous
#check @WuPaper.RMapMSigma.sigma_weight_integrable
#check @WuPaper.RMapMSigma.indicator_interval_integral
#check @WuPaper.RMapMSigma.upperKernel
#check @WuPaper.RMapMSigma.upperKernel_nonneg
#check @WuPaper.RMapMSigma.upperKernel_integrable
#check @WuPaper.RMapMSigma.upperKernel_identity
#check @WuPaper.RMapMSigma.lemma61
#check @WuPaper.RMapMSigma.lemma62
#print axioms WuPaper.RMapMSigma.sigma_definition
#print axioms WuPaper.RMapMSigma.sigma0_definition
#print axioms WuPaper.RMapMSigma.sigma_denominator_pos
#print axioms WuPaper.RMapMSigma.sigma_numerator_identity
#print axioms WuPaper.RMapMSigma.sigma0_continuous
#print axioms WuPaper.RMapMSigma.sigma_weight_integrable
#print axioms WuPaper.RMapMSigma.indicator_interval_integral
#print axioms WuPaper.RMapMSigma.upperKernel
#print axioms WuPaper.RMapMSigma.upperKernel_nonneg
#print axioms WuPaper.RMapMSigma.upperKernel_integrable
#print axioms WuPaper.RMapMSigma.upperKernel_identity
#print axioms WuPaper.RMapMSigma.lemma61
#print axioms WuPaper.RMapMSigma.lemma62
