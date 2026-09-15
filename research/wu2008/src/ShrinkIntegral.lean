import ShrinkGeometry

open Set MeasureTheory QuarterTrim

namespace StaircaseShrink

noncomputable def fibre (t x : ℝ) : ℝ :=
  ∫ y in beta..upper t x, kernel Wu08Staircase.profile x y

noncomputable def gamma (t : ℝ) : ℝ := 4 * ∫ x in alpha..beta, fibre t x

noncomputable def strip (t x : ℝ) : ℝ :=
  ∫ y in upper t x..upper 0 x, kernel Wu08Staircase.profile x y

theorem segment_integrable {x a b : ℝ} (hx : x ∈ Icc alpha beta)
    (ha : beta ≤ a) (hab : a ≤ b) (hb : b ≤ upper 0 x) :
    IntervalIntegrable (kernel Wu08Staircase.profile x) volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
  apply Measure.integrableOn_of_bounded (M := bound) measure_Icc_lt_top.ne
    ((Wu08Staircase.measurable_kernel.comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  have h := kernel_bounds (show (x,y) ∈ domain 0 from
    ⟨hx,ha.trans hy.1,hy.2.trans hb⟩)
  change ‖kernel Wu08Staircase.profile x y‖ ≤ bound
  rw [Real.norm_eq_abs, abs_of_nonneg h.1]
  exact h.2

theorem inner_integrable {t x : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 1000)
    (hx : x ∈ Icc alpha beta) :
    IntervalIntegrable (kernel Wu08Staircase.profile x) volume beta (upper t x) :=
  segment_integrable hx le_rfl (upper_ge ht' hx.2) (upper_mono ht)

theorem strip_integrable {t x : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 1000)
    (hx : x ∈ Icc alpha beta) :
    IntervalIntegrable (kernel Wu08Staircase.profile x) volume (upper t x) (upper 0 x) :=
  segment_integrable hx (upper_ge ht' hx.2) (upper_mono ht) le_rfl

/-- Exact additivity on the literal moving fibre, including both degenerate cases. -/
theorem fibre_sub_eq_strip {t x : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 1000)
    (hx : x ∈ Icc alpha beta) : fibre 0 x - fibre t x = strip t x := by
  have he := intervalIntegral.integral_add_adjacent_intervals
    (inner_integrable ht ht' hx) (strip_integrable ht ht' hx)
  dsimp [fibre, strip]
  linarith

theorem strip_bounds {t x : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 1000)
    (hx : x ∈ Icc alpha beta) : 0 ≤ strip t x ∧ strip t x ≤ bound * t := by
  have hbounds : ∀ y ∈ Icc (upper t x) (upper 0 x),
      0 ≤ kernel Wu08Staircase.profile x y ∧ kernel Wu08Staircase.profile x y ≤ bound := by
    intro y hy
    exact kernel_bounds ⟨hx, (upper_ge ht' hx.2).trans hy.1, hy.2⟩
  constructor
  · exact intervalIntegral.integral_nonneg (upper_mono ht) (fun y hy => (hbounds y hy).1)
  · have hm := intervalIntegral.integral_mono_on (upper_mono ht)
      (strip_integrable ht ht' hx) (intervalIntegrable_const (c := bound))
      (fun y hy => (hbounds y hy).2)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hm
    exact hm.trans (by nlinarith [(upper_loss (x := x) ht).2, bound_pos])

noncomputable def measurableFibre (t x : ℝ) : ℝ :=
  ∫ y : ℝ, (Ioc beta (upper t x)).indicator (kernel Wu08Staircase.profile x) y

theorem measurable_fibre (t : ℝ) : Measurable (measurableFibre t) := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right
  apply Measurable.stronglyMeasurable
  classical
  unfold Function.uncurry Set.indicator
  apply Measurable.ite _ Wu08Staircase.measurable_kernel measurable_const
  apply MeasurableSet.inter
  · exact measurableSet_lt measurable_const measurable_snd
  · apply measurableSet_le measurable_snd
    unfold upper
    fun_prop

theorem measurableFibre_eq {t x : ℝ} (ht' : t ≤ 1 / 1000)
    (hx : x ∈ Icc alpha beta) : measurableFibre t x = fibre t x := by
  unfold fibre measurableFibre
  rw [intervalIntegral.integral_of_le (upper_ge ht' hx.2)]
  exact integral_indicator measurableSet_Ioc

theorem fibre_bounds {t x : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 1000)
    (hx : x ∈ Icc alpha beta) : 0 ≤ fibre t x ∧ fibre t x ≤ bound := by
  have hbounds : ∀ y ∈ Icc beta (upper t x),
      0 ≤ kernel Wu08Staircase.profile x y ∧ kernel Wu08Staircase.profile x y ≤ bound := by
    intro y hy
    exact kernel_bounds (domain_subset ht ⟨hx,hy⟩)
  constructor
  · exact intervalIntegral.integral_nonneg (upper_ge ht' hx.2) (fun y hy => (hbounds y hy).1)
  · have hm := intervalIntegral.integral_mono_on (upper_ge ht' hx.2)
      (inner_integrable ht ht' hx) (intervalIntegrable_const (c := bound))
      (fun y hy => (hbounds y hy).2)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hm
    have hu : upper t x ≤ (1 / 2 - t) / 2 := min_le_left _ _
    have hl : upper t x - beta ≤ 1 := by linarith [fixed_bounds.1]
    exact hm.trans (by nlinarith [bound_pos])

theorem outer_integrable {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 1000) :
    IntervalIntegrable (fibre t) volume alpha beta := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le fixed_bounds.2.1.le).2
  have hi : IntegrableOn (measurableFibre t) (Icc alpha beta) volume := by
    apply Measure.integrableOn_of_bounded (M := bound) measure_Icc_lt_top.ne
      (measurable_fibre t).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [measurableFibre_eq ht' hx, Real.norm_eq_abs,
      abs_of_nonneg (fibre_bounds ht ht' hx).1]
    exact (fibre_bounds ht ht' hx).2
  exact hi.congr_fun (fun x hx => measurableFibre_eq ht' hx) measurableSet_Icc

theorem outer_strip_integrable {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 1000) :
    IntervalIntegrable (strip t) volume alpha beta := by
  apply ((outer_integrable (t := 0) le_rfl (by norm_num)).sub
    (outer_integrable ht ht')).congr
  intro x hx
  apply fibre_sub_eq_strip ht ht'
  rw [uIoc_of_le fixed_bounds.2.1.le] at hx
  exact ⟨hx.1.le,hx.2⟩

/-- The true difference is the integral of the deleted fibres, not a supplied deficit. -/
theorem gamma_sub_eq {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 1000) :
    gamma 0 - gamma t = 4 * ∫ x in alpha..beta, strip t x := by
  unfold gamma
  rw [← mul_sub, ← intervalIntegral.integral_sub
    (outer_integrable (t := 0) le_rfl (by norm_num)) (outer_integrable ht ht')]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  apply fibre_sub_eq_strip ht ht'
  simpa only [uIcc_of_le fixed_bounds.2.1.le] using hx

/-- Fully instantiated O(t) loss for the original rational staircase. -/
theorem gamma_loss_bounds {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 1000) :
    0 ≤ gamma 0 - gamma t ∧
    gamma 0 - gamma t ≤ (2 * q * (beta - alpha) / (alpha ^ 2 * beta)) * t := by
  rw [gamma_sub_eq ht.le ht']
  constructor
  · exact mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg fixed_bounds.2.1.le
      (fun x hx => (strip_bounds ht.le ht' hx).1))
  · have hm := intervalIntegral.integral_mono_on fixed_bounds.2.1.le
      (outer_strip_integrable ht.le ht') (intervalIntegrable_const (c := bound * t))
      (fun x hx => (strip_bounds ht.le ht' hx).2)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hm
    calc
      4 * (∫ x in alpha..beta, strip t x) ≤ 4 * ((beta - alpha) * (bound * t)) := by linarith
      _ = (2 * q * (beta - alpha) / (alpha ^ 2 * beta)) * t := by unfold bound; ring

/-- Literal closed-domain fibre identification; only Lebesgue endpoints are omitted. -/
theorem domain_fibre {t x : ℝ} (hx : x ∈ Icc alpha beta) :
    {y : ℝ | (x,y) ∈ domain t} = Icc beta (upper t x) := by
  ext y
  simp only [domain, mem_ofPred_eq]
  exact and_iff_right hx

theorem gamma_as_domain_fibres {t : ℝ} (ht' : t ≤ 1 / 1000) :
    gamma t = 4 * ∫ x in Icc alpha beta,
      ∫ y in {y : ℝ | (x,y) ∈ domain t}, kernel Wu08Staircase.profile x y := by
  unfold gamma
  congr 1
  rw [intervalIntegral.integral_of_le fixed_bounds.2.1.le, integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  have hxc : x ∈ Icc alpha beta := ⟨hx.1.le,hx.2⟩
  dsimp only
  rw [domain_fibre (t := t) hxc, integral_Icc_eq_integral_Ioc]
  exact intervalIntegral.integral_of_le (upper_ge ht' hxc.2)

theorem removed_fibre {t x : ℝ} (ht' : t ≤ 1 / 1000)
    (hx : x ∈ Icc alpha beta) :
    {y : ℝ | (x,y) ∈ domain 0 ∧ (x,y) ∉ domain t} = Ioc (upper t x) (upper 0 x) := by
  ext y
  change (x ∈ Icc alpha beta ∧ y ∈ Icc beta (upper 0 x)) ∧
      ¬ (x ∈ Icc alpha beta ∧ y ∈ Icc beta (upper t x)) ↔ _
  simp only [hx, true_and, mem_Icc, mem_Ioc]
  constructor
  · rintro ⟨⟨hy,hy'⟩,hnot⟩
    exact ⟨lt_of_not_ge (fun hle => hnot ⟨hy,hle⟩),hy'⟩
  · rintro ⟨hy,hy'⟩
    exact ⟨⟨(upper_ge ht' hx.2).trans hy.le,hy'⟩,fun hle => (not_lt_of_ge hle.2) hy⟩

theorem gamma_sub_as_removed {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 1000) :
    gamma 0 - gamma t = 4 * ∫ x in Icc alpha beta,
      ∫ y in {y : ℝ | (x,y) ∈ domain 0 ∧ (x,y) ∉ domain t},
        kernel Wu08Staircase.profile x y := by
  rw [gamma_sub_eq ht ht']
  congr 1
  rw [intervalIntegral.integral_of_le fixed_bounds.2.1.le, integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  dsimp only
  rw [removed_fibre ht' ⟨hx.1.le,hx.2⟩]
  exact intervalIntegral.integral_of_le (upper_mono ht)

end StaircaseShrink
