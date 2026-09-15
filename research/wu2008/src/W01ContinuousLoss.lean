import W01ContinuousIntegral

noncomputable section
namespace WuTarget.W01Continuous
open Set MeasureTheory QuarterTrim StaircaseShrink Wu2008DoubleSieve NodeExtension
open scoped Classical

def continuousFibre (x : Fin 9 → ℝ) (t a : ℝ) : ℝ :=
  ∫ b in beta..upper t a, kernel (hContinuous x) a b

def continuousMeasurableFibre (x : Fin 9 → ℝ) (t a : ℝ) : ℝ :=
  ∫ b : ℝ, (Ioc beta (upper t a)).indicator (kernel (hContinuous x) a) b

def continuousStrip (x : Fin 9 → ℝ) (t a : ℝ) : ℝ :=
  ∫ b in upper t a..upper 0 a, kernel (hContinuous x) a b

def continuousLoss (x : Fin 9 → ℝ) : ℝ :=
  4*(beta-alpha)*continuousBound x

theorem continuousLoss_nonneg {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    0 ≤ continuousLoss x :=
  mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr fixed_bounds.2.1.le))
    (continuousBound_nonneg hx)

theorem continuous_segment_integrable {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i)
    {a b c : ℝ} (ha : a ∈ Icc alpha beta) (hb : beta ≤ b)
    (hbc : b ≤ c) (hc : c ≤ upper 0 a) :
    IntervalIntegrable (kernel (hContinuous x) a) volume b c := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hbc).mpr
  apply Measure.integrableOn_of_bounded (M := continuousBound x) measure_Icc_lt_top.ne
    ((measurable_continuous_kernel x).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  have h := continuous_kernel_bounds hx (show (a,y) ∈ domain 0 from
    ⟨ha,hb.trans hy.1,hy.2.trans hc⟩)
  change ‖kernel (hContinuous x) a y‖ ≤ continuousBound x
  change 0 ≤ kernel (hContinuous x) a y ∧ kernel (hContinuous x) a y ≤ continuousBound x at h
  rw [Real.norm_eq_abs,abs_of_nonneg h.1]
  exact h.2

theorem continuous_inner_integrable {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i)
    {t a : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1/1000) (ha : a ∈ Icc alpha beta) :
    IntervalIntegrable (kernel (hContinuous x) a) volume beta (upper t a) :=
  continuous_segment_integrable hx ha le_rfl (upper_ge ht' ha.2) (upper_mono ht)

theorem continuous_strip_integrable {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i)
    {t a : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1/1000) (ha : a ∈ Icc alpha beta) :
    IntervalIntegrable (kernel (hContinuous x) a) volume (upper t a) (upper 0 a) :=
  continuous_segment_integrable hx ha (upper_ge ht' ha.2) (upper_mono ht) le_rfl

theorem continuous_fibre_difference {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i)
    {t a : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1/1000) (ha : a ∈ Icc alpha beta) :
    continuousFibre x 0 a-continuousFibre x t a = continuousStrip x t a := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (continuous_inner_integrable hx ht ht' ha) (continuous_strip_integrable hx ht ht' ha)
  dsimp [continuousFibre,continuousStrip]
  linarith only [h]

theorem continuous_strip_bounds {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i)
    {t a : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1/1000) (ha : a ∈ Icc alpha beta) :
    0 ≤ continuousStrip x t a ∧ continuousStrip x t a ≤ continuousBound x*t := by
  have hb (b : ℝ) (h : b ∈ Icc (upper t a) (upper 0 a)) :=
    continuous_kernel_bounds hx (show (a,b) ∈ domain 0 from
      ⟨ha,(upper_ge ht' ha.2).trans h.1,h.2⟩)
  constructor
  · exact intervalIntegral.integral_nonneg (upper_mono ht) (fun b h => (hb b h).1)
  · have h := intervalIntegral.integral_mono_on (upper_mono ht)
      (continuous_strip_integrable hx ht ht' ha) (intervalIntegrable_const (c := continuousBound x))
      (fun b h => (hb b h).2)
    simp only [intervalIntegral.integral_const,smul_eq_mul] at h
    exact h.trans (by nlinarith [(upper_loss (x := a) ht).2,continuousBound_nonneg hx])

theorem continuous_measurable_fibre (x : Fin 9 → ℝ) (t : ℝ) :
    Measurable (continuousMeasurableFibre x t) := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right
  apply Measurable.stronglyMeasurable
  unfold Function.uncurry Set.indicator
  apply Measurable.ite _ (measurable_continuous_kernel x) measurable_const
  exact (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd (by unfold upper; fun_prop))

theorem continuous_measurableFibre_eq (x : Fin 9 → ℝ) {t a : ℝ}
    (ht : t ≤ 1/1000) (ha : a ∈ Icc alpha beta) :
    continuousMeasurableFibre x t a = continuousFibre x t a := by
  unfold continuousMeasurableFibre continuousFibre
  rw [intervalIntegral.integral_of_le (upper_ge ht ha.2)]
  exact integral_indicator measurableSet_Ioc

theorem continuous_fibre_bounds {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i)
    {t a : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1/1000) (ha : a ∈ Icc alpha beta) :
    0 ≤ continuousFibre x t a ∧ continuousFibre x t a ≤ continuousBound x := by
  have hb (b : ℝ) (h : b ∈ Icc beta (upper t a)) :=
    continuous_kernel_bounds hx (domain_subset ht (show (a,b) ∈ domain t from ⟨ha,h⟩))
  constructor
  · exact intervalIntegral.integral_nonneg (upper_ge ht' ha.2) (fun b h => (hb b h).1)
  · have h := intervalIntegral.integral_mono_on (upper_ge ht' ha.2)
      (continuous_inner_integrable hx ht ht' ha) (intervalIntegrable_const (c := continuousBound x))
      (fun b h => (hb b h).2)
    simp only [intervalIntegral.integral_const,smul_eq_mul] at h
    have hu : upper t a ≤ (1/2-t)/2 := min_le_left _ _
    have hl : upper t a-beta ≤ 1 := by linarith [fixed_bounds.1]
    exact h.trans (by nlinarith [continuousBound_nonneg hx])

theorem continuous_outer_integrable {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i)
    {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1/1000) :
    IntervalIntegrable (continuousFibre x t) volume alpha beta := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le fixed_bounds.2.1.le).mpr
  have hi : IntegrableOn (continuousMeasurableFibre x t) (Icc alpha beta) := by
    apply Measure.integrableOn_of_bounded (M := continuousBound x) measure_Icc_lt_top.ne
      (continuous_measurable_fibre x t).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
    rw [Real.norm_eq_abs,continuous_measurableFibre_eq x ht' ha,
      abs_of_nonneg (continuous_fibre_bounds hx ht ht' ha).1]
    exact (continuous_fibre_bounds hx ht ht' ha).2
  exact hi.congr_fun (fun a ha => continuous_measurableFibre_eq x ht' ha) measurableSet_Icc

theorem continuous_outer_strip_integrable {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i)
    {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1/1000) :
    IntervalIntegrable (continuousStrip x t) volume alpha beta := by
  apply ((continuous_outer_integrable hx (t := 0) le_rfl (by norm_num)).sub
    (continuous_outer_integrable hx ht ht')).congr
  intro a ha
  rw [uIoc_of_le fixed_bounds.2.1.le] at ha
  exact continuous_fibre_difference hx ht ht' ⟨ha.1.le,ha.2⟩

theorem continuousGamma_eq_fibres {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i)
    {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1/1000) :
    continuousGamma x t = 4*∫ a in alpha..beta, continuousFibre x t a := by
  unfold continuousGamma
  rw [show (∫ v : ℝ × ℝ, continuousUniform x t v) =
    ∫ a, ∫ b, continuousUniform x t (a,b) from
      integral_prod _ (continuousUniform_integrable hx ht)]
  have hs : Function.support (fun a => ∫ b, continuousUniform x t (a,b)) ⊆ Icc alpha beta := by
    intro a ha
    by_contra hn
    apply ha
    have he : (fun b => continuousUniform x t (a,b)) = 0 := by
      funext b
      have hv : (a,b) ∉ domain t := fun hv => hn hv.1
      simp [continuousUniform,hv]
    change (∫ b, continuousUniform x t (a,b)) = 0
    rw [he]
    simp
  rw [truncatedSixthMass_integral_eq_interval fixed_bounds.2.1.le hs]
  congr 1
  apply intervalIntegral.integral_congr
  intro a ha
  rw [uIcc_of_le fixed_bounds.2.1.le] at ha
  have he : (fun b => continuousUniform x t (a,b)) =
      (Icc beta (upper t a)).indicator (kernel (hContinuous x) a) := by
    funext b
    simp only [continuousUniform,domain,mem_ofPred_eq,ha,true_and,indicator]
    split_ifs <;> rfl
  change (∫ b, continuousUniform x t (a,b)) = continuousFibre x t a
  rw [he,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc]
  exact (intervalIntegral.integral_of_le (upper_ge ht' ha.2)).symm

theorem continuousGamma_difference {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i)
    {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1/1000) :
    continuousGain x-continuousGamma x t =
      4*∫ a in alpha..beta, continuousStrip x t a := by
  rw [continuousGain,continuousGamma_eq_fibres hx le_rfl (by norm_num),
    continuousGamma_eq_fibres hx ht ht',← mul_sub,
    ← intervalIntegral.integral_sub
      (continuous_outer_integrable hx (t := 0) le_rfl (by norm_num))
      (continuous_outer_integrable hx ht ht')]
  congr 1
  apply intervalIntegral.integral_congr
  intro a ha
  rw [uIcc_of_le fixed_bounds.2.1.le] at ha
  exact continuous_fibre_difference hx ht ht' ha

/-- The actual deleted fibres, on the unchanged domain, pay the full continuous gain. -/
theorem continuousGain_loss {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i)
    {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1/1000) :
    0 ≤ continuousGain x-continuousGamma x t ∧
      continuousGain x-continuousGamma x t ≤ continuousLoss x*t := by
  rw [continuousGamma_difference hx ht ht']
  constructor
  · exact mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg fixed_bounds.2.1.le
      (fun a ha => (continuous_strip_bounds hx ht ht' ha).1))
  · have h := intervalIntegral.integral_mono_on fixed_bounds.2.1.le
      (continuous_outer_strip_integrable hx ht ht')
      (intervalIntegrable_const (c := continuousBound x*t))
      (fun a ha => (continuous_strip_bounds hx ht ht' ha).2)
    simp only [intervalIntegral.integral_const,smul_eq_mul] at h
    dsimp [continuousLoss]
    nlinarith only [h]

theorem continuousGain_Hadm_payment {x : Fin 9 → ℝ} {d0 ε : ℝ}
    (hn : ∀ i, 0 ≤ x i) (hd0 : 0 < d0)
    (hx : ∀ δ : ℝ, 0 < δ → δ ≤ d0 → ∀ i, x i ≤ actualNine δ i)
    (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ d ≤ d0 ∧ d ≤ 1/100 ∧
      ∀ δ : ℝ, 0 < δ → δ < d →
        continuousGain x-ε ≤ truncatedSixthLowerHadmdelta δ := by
  let L := continuousLoss x
  have hL : 0 ≤ L := continuousLoss_nonneg hn
  let t : ℝ := min (1/1000) (ε/(L+1))
  have ht : 0 < t := lt_min (by norm_num) (div_pos hε (by linarith))
  have ht' : t ≤ 1/1000 := min_le_left _ _
  have hpay : L*t < ε := by
    have h := (le_div_iff₀ (show 0 < L+1 by linarith)).mp
      (show t ≤ ε/(L+1) from min_le_right _ _)
    nlinarith only [h,ht]
  refine ⟨min d0 (min (1/100) (t/2)),
    lt_min hd0 (lt_min (by norm_num) (half_pos ht)),min_le_left _ _,
    (min_le_right _ _).trans (min_le_left _ _),?_⟩
  intro δ hδ hδd
  have hδ0 : δ ≤ d0 := hδd.le.trans (min_le_left _ _)
  have hδt : δ ≤ t/2 := hδd.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hl := (continuousGain_loss hn ht.le ht').2
  have hp := continuousGamma_payment hn ht ht' hδ hδt (hx δ hδ hδ0)
  change continuousGain x-continuousGamma x t ≤ L*t at hl
  linarith only [hl,hp,hpay]

end WuTarget.W01Continuous
