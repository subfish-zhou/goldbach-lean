import DirectIntegral

open Set MeasureTheory QuarterTrim StaircaseShrink
open scoped Classical

namespace DirectFiniteF6
noncomputable section

/-- A measurable representative of the genuine moving inner integral. -/
def measurableFibre (w : Fin 21 → ℝ) (t x : ℝ) : ℝ :=
  ∫ y : ℝ, (Ioc beta (upper t x)).indicator (kernel (profile w) x) y

theorem measurable_fibre (w : Fin 21 → ℝ) (t : ℝ) : Measurable (measurableFibre w t) := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right
  apply Measurable.stronglyMeasurable
  unfold Function.uncurry Set.indicator
  apply Measurable.ite _ (measurable_kernel w) measurable_const
  exact (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd (by unfold upper; fun_prop))

theorem measurableFibre_eq (w : Fin 21 → ℝ) {t x : ℝ} (ht : t ≤ 1/1000)
    (hx : x ∈ Icc alpha beta) : measurableFibre w t x = fibre w t x := by
  unfold measurableFibre fibre
  rw [intervalIntegral.integral_of_le (upper_ge ht hx.2)]
  exact integral_indicator measurableSet_Ioc

theorem fibre_abs (w : Fin 21 → ℝ) {t x : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1/1000)
    (hx : x ∈ Icc alpha beta) : |fibre w t x| ≤ bound w := by
  have hk : ∀ y ∈ Icc beta (upper t x), |kernel (profile w) x y| ≤ bound w :=
    fun y hy => kernel_abs w (domain_subset ht ⟨hx,hy⟩)
  have hp := intervalIntegral.integral_mono_on (upper_ge ht' hx.2)
    (inner_integrable w ht ht' hx) (intervalIntegrable_const (c := bound w))
    (fun y hy => (le_abs_self _).trans (hk y hy))
  have hn := intervalIntegral.integral_mono_on (upper_ge ht' hx.2)
    (intervalIntegrable_const (c := -bound w)) (inner_integrable w ht ht' hx)
    (fun y hy => (neg_le_neg (hk y hy)).trans (neg_abs_le _))
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hp hn
  have hl : upper t x - beta ≤ 1 := by
    have hu := min_le_left ((1/2-t)/2) (1/2-t-2*alpha-x)
    change upper t x ≤ (1/2-t)/2 at hu
    linarith [fixed_bounds.1]
  have hm := mul_le_mul_of_nonneg_right hl (bound_nonneg w)
  apply abs_le.mpr
  constructor <;> dsimp [fibre] <;> nlinarith only [hp,hn,hm]

theorem outer_integrable (w : Fin 21 → ℝ) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1/1000) :
    IntervalIntegrable (fibre w t) volume alpha beta := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le fixed_bounds.2.1.le).mpr
  have hi : IntegrableOn (measurableFibre w t) (Icc alpha beta) := by
    apply Measure.integrableOn_of_bounded (M := bound w) measure_Icc_lt_top.ne
      (measurable_fibre w t).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, measurableFibre_eq w ht' hx]
    exact fibre_abs w ht ht' hx
  exact hi.congr_fun (fun x hx => measurableFibre_eq w ht' hx) measurableSet_Icc

def strip (w : Fin 21 → ℝ) (t x : ℝ) : ℝ :=
  ∫ y in upper t x..upper 0 x, kernel (profile w) x y

theorem strip_integrable (w : Fin 21 → ℝ) {t x : ℝ} (ht : 0 ≤ t)
    (ht' : t ≤ 1/1000) (hx : x ∈ Icc alpha beta) :
    IntervalIntegrable (kernel (profile w) x) volume (upper t x) (upper 0 x) :=
  segment_integrable w hx (upper_ge ht' hx.2) (upper_mono ht) le_rfl

theorem fibre_difference (w : Fin 21 → ℝ) {t x : ℝ} (ht : 0 ≤ t)
    (ht' : t ≤ 1/1000) (hx : x ∈ Icc alpha beta) :
    fibre w 0 x - fibre w t x = strip w t x := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (inner_integrable w ht ht' hx) (strip_integrable w ht ht' hx)
  dsimp [fibre, strip]
  linarith only [h]

theorem strip_bounds {w : Fin 21 → ℝ} (hw : ∀ j, 0 ≤ w j) {t x : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1/1000) (hx : x ∈ Icc alpha beta) :
    0 ≤ strip w t x ∧ strip w t x ≤ bound w * t := by
  have hdom : ∀ y ∈ Icc (upper t x) (upper 0 x), (x,y) ∈ domain 0 :=
    fun y hy => ⟨hx, (upper_ge ht' hx.2).trans hy.1,hy.2⟩
  constructor
  · exact intervalIntegral.integral_nonneg (upper_mono ht)
      (fun y hy => kernel_nonneg hw (hdom y hy))
  · have hi := intervalIntegral.integral_mono_on (upper_mono ht)
      (strip_integrable w ht ht' hx) (intervalIntegrable_const (c := bound w))
      (fun y hy => (le_abs_self _).trans (kernel_abs w (hdom y hy)))
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
    exact hi.trans (by nlinarith [(upper_loss (x := x) ht).2, bound_nonneg w])

theorem outer_strip_integrable (w : Fin 21 → ℝ) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1/1000) :
    IntervalIntegrable (strip w t) volume alpha beta := by
  apply ((outer_integrable w (t := 0) le_rfl (by norm_num)).sub
    (outer_integrable w ht ht')).congr
  intro x hx
  rw [uIoc_of_le fixed_bounds.2.1.le] at hx
  exact fibre_difference w ht ht' ⟨hx.1.le,hx.2⟩

theorem Gamma_difference (w : Fin 21 → ℝ) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1/1000) :
    Gamma w 0 - Gamma w t = 4 * ∫ x in alpha..beta, strip w t x := by
  rw [Gamma_eq_fibres w le_rfl (by norm_num), Gamma_eq_fibres w ht ht', ← mul_sub,
    ← intervalIntegral.integral_sub (outer_integrable w (t := 0) le_rfl (by norm_num))
      (outer_integrable w ht ht')]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le fixed_bounds.2.1.le] at hx
  exact fibre_difference w ht ht' hx

def loss (w : Fin 21 → ℝ) : ℝ := 4 * (beta-alpha) * bound w

theorem loss_nonneg (w : Fin 21 → ℝ) : 0 ≤ loss w :=
  mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr fixed_bounds.2.1.le)) (bound_nonneg w)

/-- Exact deleted fibres yield O(t), with no comparison of independent lower bounds. -/
theorem Gamma_loss {w : Fin 21 → ℝ} (hw : ∀ j, 0 ≤ w j) {t : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1/1000) :
    0 ≤ Gamma w 0 - Gamma w t ∧ Gamma w 0 - Gamma w t ≤ loss w * t := by
  rw [Gamma_difference w ht ht']
  constructor
  · exact mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg fixed_bounds.2.1.le
      (fun x hx => (strip_bounds hw ht ht' hx).1))
  · have hi := intervalIntegral.integral_mono_on fixed_bounds.2.1.le
      (outer_strip_integrable w ht ht') (intervalIntegrable_const (c := bound w*t))
      (fun x hx => (strip_bounds hw ht ht' hx).2)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
    dsimp [loss]
    nlinarith only [hi]

end
end DirectFiniteF6
