import DirectProfile

open Set MeasureTheory QuarterTrim
open scoped Classical

namespace DirectFiniteF6
noncomputable section

def bound (w : Fin 21 → ℝ) : ℝ := mass w / (2 * alpha ^ 2 * beta)

theorem bound_nonneg (w : Fin 21 → ℝ) : 0 ≤ bound w :=
  div_nonneg (mass_nonneg w) (by have := alpha_pos; have := StaircaseShrink.fixed_bounds.1; positivity)

theorem denominator_bounds {x y : ℝ} (h : (x,y) ∈ StaircaseShrink.domain 0) :
    0 < x*y*(1/2-x-y) ∧ 2*alpha^2*beta ≤ x*y*(1/2-x-y) := by
  obtain ⟨ha, _, hc, _, he⟩ := (StaircaseShrink.domain_iff 0 x y).mp h
  have hx : 0 < x := alpha_pos.trans_le ha
  have hy : 0 < y := StaircaseShrink.fixed_bounds.1.trans_le hc
  have hz : 2*alpha ≤ 1/2-x-y := by linarith
  have hxy := mul_le_mul ha hc StaircaseShrink.fixed_bounds.1.le hx.le
  have hm := mul_le_mul hxy hz (by have := alpha_pos; positivity : 0 ≤ 2*alpha) (mul_nonneg hx.le hy.le)
  exact ⟨mul_pos (mul_pos hx hy) (by linarith [alpha_pos]), by nlinarith only [hm]⟩

theorem kernel_abs (w : Fin 21 → ℝ) {x y : ℝ}
    (h : (x,y) ∈ StaircaseShrink.domain 0) : |kernel (profile w) x y| ≤ bound w := by
  obtain ⟨hp, hb⟩ := denominator_bounds h
  change |profile w (u x y) / (x*y*(1/2-x-y))| ≤ _
  rw [abs_div, abs_of_pos hp]
  exact div_le_div₀ (mass_nonneg w) (profile_abs w _) (by have := alpha_pos; have := StaircaseShrink.fixed_bounds.1; positivity) hb

theorem kernel_nonneg {w : Fin 21 → ℝ} (hw : ∀ j, 0 ≤ w j) {x y : ℝ}
    (h : (x,y) ∈ StaircaseShrink.domain 0) : 0 ≤ kernel (profile w) x y :=
  div_nonneg (profile_nonneg hw _) (denominator_bounds h).1.le

theorem kernel_mono {w z : Fin 21 → ℝ} (hw : ∀ j, w j ≤ z j) {x y : ℝ}
    (h : (x,y) ∈ StaircaseShrink.domain 0) : kernel (profile w) x y ≤ kernel (profile z) x y :=
  div_le_div_of_nonneg_right (profile_mono hw _) (denominator_bounds h).1.le

theorem measurable_kernel (w : Fin 21 → ℝ) :
    Measurable (fun v : ℝ × ℝ => kernel (profile w) v.1 v.2) := by
  unfold kernel
  apply Measurable.div
  · apply (measurable_profile w).comp
    unfold u
    fun_prop
  · fun_prop

def uniform (w : Fin 21 → ℝ) (t : ℝ) (v : ℝ × ℝ) : ℝ :=
  if v ∈ StaircaseShrink.domain t then kernel (profile w) v.1 v.2 else 0

def Gamma (w : Fin 21 → ℝ) (t : ℝ) : ℝ := 4 * ∫ v : ℝ × ℝ, uniform w t v

theorem domain_measurable {t : ℝ} (ht : 0 ≤ t) : MeasurableSet (StaircaseShrink.domain t) := by
  rw [StaircaseActual.domain_eq ht]
  exact (Wu2008DoubleSieve.truncatedSixthMass_regions_measurable t).2

theorem uniform_integrable (w : Fin 21 → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (uniform w t) := by
  have hs := domain_measurable ht
  have hsub : StaircaseShrink.domain t ⊆ Icc alpha beta ×ˢ Icc beta (1/4) := by
    intro v hv
    have h := (StaircaseShrink.domain_iff t v.1 v.2).mp hv
    exact ⟨hv.1, h.2.2.1, by linarith [h.2.2.2.1]⟩
  apply (integrable_indicator_iff hs).mpr
  apply Measure.integrableOn_of_bounded (M := bound w)
    (ne_of_lt (lt_of_le_of_lt (measure_mono hsub) (isCompact_Icc.prod isCompact_Icc).measure_lt_top))
    (measurable_kernel w).aestronglyMeasurable
  filter_upwards [ae_restrict_mem hs] with v hv
  exact (Real.norm_eq_abs _).symm ▸ kernel_abs w (StaircaseShrink.domain_subset ht hv)

theorem uniform_nonneg {w : Fin 21 → ℝ} (hw : ∀ j, 0 ≤ w j)
    {t : ℝ} (ht : 0 ≤ t) (v : ℝ × ℝ) : 0 ≤ uniform w t v := by
  unfold uniform
  split_ifs with hv
  · exact kernel_nonneg hw (StaircaseShrink.domain_subset ht hv)
  · exact le_rfl

theorem Gamma_nonneg {w : Fin 21 → ℝ} (hw : ∀ j, 0 ≤ w j)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Gamma w t :=
  mul_nonneg (by norm_num) (integral_nonneg (uniform_nonneg hw ht))

theorem uniform_mono {w z : Fin 21 → ℝ} (hw : ∀ j, w j ≤ z j)
    {t : ℝ} (ht : 0 ≤ t) (v : ℝ × ℝ) : uniform w t v ≤ uniform z t v := by
  unfold uniform
  split_ifs with hv
  · exact kernel_mono hw (StaircaseShrink.domain_subset ht hv)
  · exact le_rfl

theorem Gamma_mono {w z : Fin 21 → ℝ} (hw : ∀ j, w j ≤ z j)
    {t : ℝ} (ht : 0 ≤ t) : Gamma w t ≤ Gamma z t :=
  mul_le_mul_of_nonneg_left (integral_mono (uniform_integrable w ht)
    (uniform_integrable z ht) (uniform_mono hw ht)) (by norm_num)

theorem uniform_sub_mul (w d : Fin 21 → ℝ) (a t : ℝ) (v : ℝ × ℝ) :
    uniform (fun j => w j - a*d j) t v = uniform w t v - a*uniform d t v := by
  unfold uniform
  split_ifs
  · unfold kernel
    rw [profile_sub_mul]
    ring
  · ring

theorem Gamma_sub_mul (w d : Fin 21 → ℝ) (a : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Gamma (fun j => w j - a*d j) t = Gamma w t - a*Gamma d t := by
  unfold Gamma
  simp_rw [uniform_sub_mul]
  rw [integral_sub (uniform_integrable w ht) ((uniform_integrable d ht).const_mul a), integral_const_mul]
  ring

def fibre (w : Fin 21 → ℝ) (t x : ℝ) : ℝ :=
  ∫ y in beta..StaircaseShrink.upper t x, kernel (profile w) x y

theorem segment_integrable (w : Fin 21 → ℝ) {x a b : ℝ}
    (hx : x ∈ Icc alpha beta) (ha : beta ≤ a) (hab : a ≤ b)
    (hb : b ≤ StaircaseShrink.upper 0 x) :
    IntervalIntegrable (kernel (profile w) x) volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  apply Measure.integrableOn_of_bounded (M := bound w) measure_Icc_lt_top.ne
    ((measurable_kernel w).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  rw [Real.norm_eq_abs]
  exact kernel_abs w ⟨hx, ha.trans hy.1, hy.2.trans hb⟩

theorem inner_integrable (w : Fin 21 → ℝ) {t x : ℝ} (ht : 0 ≤ t)
    (ht' : t ≤ 1/1000) (hx : x ∈ Icc alpha beta) :
    IntervalIntegrable (kernel (profile w) x) volume beta (StaircaseShrink.upper t x) :=
  segment_integrable w hx le_rfl (StaircaseShrink.upper_ge ht' hx.2) (StaircaseShrink.upper_mono ht)

theorem Gamma_eq_fibres (w : Fin 21 → ℝ) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1/1000) :
    Gamma w t = 4 * ∫ x in alpha..beta, fibre w t x := by
  unfold Gamma
  rw [show (∫ v : ℝ × ℝ, uniform w t v) = ∫ x, ∫ y, uniform w t (x,y) from
    integral_prod _ (uniform_integrable w ht)]
  have hs : Function.support (fun x => ∫ y, uniform w t (x,y)) ⊆ Icc alpha beta := by
    intro x hx
    by_contra hn
    apply hx
    have he : (fun y => uniform w t (x,y)) = 0 := by
      funext y
      have hv : (x,y) ∉ StaircaseShrink.domain t := fun hv => hn hv.1
      simp [uniform, hv]
    change (∫ y, uniform w t (x,y)) = 0
    rw [he]
    simp
  rw [Wu2008DoubleSieve.truncatedSixthMass_integral_eq_interval StaircaseShrink.fixed_bounds.2.1.le hs]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le StaircaseShrink.fixed_bounds.2.1.le] at hx
  have he : (fun y => uniform w t (x,y)) =
      (Icc beta (StaircaseShrink.upper t x)).indicator (kernel (profile w) x) := by
    funext y
    simp only [uniform, StaircaseShrink.domain, mem_ofPred_eq, hx, true_and, indicator]
    split_ifs <;> rfl
  change (∫ y, uniform w t (x,y)) = fibre w t x
  rw [he, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc]
  exact (intervalIntegral.integral_of_le (StaircaseShrink.upper_ge ht' hx.2)).symm

end
end DirectFiniteF6
