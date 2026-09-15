import RMapMSixthClassical

noncomputable section
namespace WuPaper.RMapMSixth
open Real Set MeasureTheory QuarterTrim Wu2008DoubleSieve
open WuSource.SrcSixthGain
open scoped Interval

def c6KernelFloor : ℝ := alpha*(3-beta/alpha)*(2*beta)
def c6Width : ℝ := (1/2-beta-3*alpha)/alpha

theorem c6_error_constants : 0 < c6KernelFloor ∧ 0 < c6Width := by
  norm_num [c6KernelFloor,c6Width,alpha,beta]

theorem c6_width (t : ℝ) : c6Upper t-c6Lower t = c6Width := by
  unfold c6Upper c6Lower c6Width
  ring

theorem c6_kernel_floor {t s : ℝ} (ht : t ∈ Icc alpha beta)
    (hs : s ∈ Icc (c6Lower t) (c6Upper t)) :
    c6KernelFloor ≤ t*s*(1-2*t-2*alpha*s) := by
  have hr := c6_parameter_range ht hs
  have hp := c6_denominator_positive ht hs
  have hlo : 0 ≤ 3-beta/alpha := by norm_num [alpha,beta]
  have hb : 0 ≤ 2*beta := by norm_num [beta]
  have hz : 2*beta ≤ 1-2*t-2*alpha*s := by
    have h := (le_div_iff₀ alpha_pos).mp hs.2
    linarith
  exact mul_le_mul (mul_le_mul ht.1 hr.1 hlo hp.1.le) hz hb
    (mul_nonneg hp.1.le hp.2.1.le)

theorem c6_kernel_error {p q : ℝ → ℝ} {t s E : ℝ}
    (ht : t ∈ Icc alpha beta) (hs : s ∈ Icc (c6Lower t) (c6Upper t))
    (hE : 0 ≤ E) (he : |p s-q s| ≤ E) :
    |paperKernel p t s-paperKernel q t s| ≤ E/c6KernelFloor := by
  have hd := c6_kernel_floor ht hs
  unfold paperKernel
  rw [← sub_div,abs_div,abs_of_pos (c6_error_constants.1.trans_le hd)]
  exact div_le_div₀ hE he c6_error_constants.1 hd

theorem interval_sub_error {f g : ℝ → ℝ} {a b E : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b)
    (he : ∀ x ∈ Icc a b, |f x-g x| ≤ E) :
    |(∫ x in a..b, f x)-(∫ x in a..b, g x)| ≤ E*(b-a) := by
  rw [← intervalIntegral.integral_sub hf hg]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const' hab
    (fun x hx => show ‖f x-g x‖ ≤ E by simpa only [Real.norm_eq_abs] using he x hx)
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab)] using h

theorem c6_inner_error {p q : ℝ → ℝ} {t E : ℝ}
    (ht : t ∈ Icc alpha beta) (hE : 0 ≤ E)
    (hp : IntervalIntegrable (paperKernel p t) volume (c6Lower t) (c6Upper t))
    (hq : IntervalIntegrable (paperKernel q t) volume (c6Lower t) (c6Upper t))
    (he : ∀ s ∈ Icc (c6Lower t) (c6Upper t), |p s-q s| ≤ E) :
    |(∫ s in c6Lower t..c6Upper t, paperKernel p t s)-
      (∫ s in c6Lower t..c6Upper t, paperKernel q t s)| ≤
        (E/c6KernelFloor)*c6Width := by
  simpa only [c6_width] using interval_sub_error (c6_interval t) hp hq
    (fun s hs => c6_kernel_error ht hs hE (he s hs))

theorem c6_function_error {p q : ℝ → ℝ} {E : ℝ} (hE : 0 ≤ E)
    (hp : ∀ t ∈ Icc alpha beta,
      IntervalIntegrable (paperKernel p t) volume (c6Lower t) (c6Upper t))
    (hq : ∀ t ∈ Icc alpha beta,
      IntervalIntegrable (paperKernel q t) volume (c6Lower t) (c6Upper t))
    (hpOuter : IntervalIntegrable
      (fun t => ∫ s in c6Lower t..c6Upper t, paperKernel p t s) volume alpha beta)
    (hqOuter : IntervalIntegrable
      (fun t => ∫ s in c6Lower t..c6Upper t, paperKernel q t s) volume alpha beta)
    (he : ∀ t ∈ Icc alpha beta, ∀ s ∈ Icc (c6Lower t) (c6Upper t), |p s-q s| ≤ E) :
    |paperC6 p-paperC6 q| ≤ 8*((E/c6KernelFloor)*c6Width)*(beta-alpha) := by
  have h := interval_sub_error envelope_bounds.1 hpOuter hqOuter
    (fun t ht => c6_inner_error ht hE (hp t ht) (hq t ht) (he t ht))
  unfold paperC6
  rw [← mul_sub,abs_mul]
  norm_num only [abs_ofNat]
  nlinarith only [h]

theorem c6_actual_inner_integrable {t : ℝ} (ht : t ∈ Icc alpha beta) :
    IntervalIntegrable (paperKernel wuLowerCoefficient t) volume (c6Lower t) (c6Upper t) := by
  have hc : ContinuousOn wuLowerCoefficient (Ioi 0) := by
    unfold wuLowerCoefficient
    exact (continuousOn_id.mul
      MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne.continuousOn_jr1965f).div_const _
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (c6_interval t)]
  apply ContinuousOn.div
  · exact hc.mono (fun s hs => (c6_denominator_positive ht hs).2.1)
  · fun_prop
  · intro s hs
    have hp := c6_denominator_positive ht hs
    exact (mul_pos (mul_pos hp.1 hp.2.1) hp.2.2).ne'

theorem c6_regular_eq {t y : ℝ} (ht : t ∈ Icc alpha beta)
    (hy : y ∈ Icc beta (1/2-3*alpha)) :
    truncatedSixthZeroDeltaRegular 0 (t,y) = kernel wuLowerCoefficient t y := by
  have h := truncatedSixthZeroDelta_regular_eq (δ := 0) (by norm_num) ht hy
  by_cases hr : truncatedSixthLowerRegion 0 t y
  · rw [if_pos hr] at h
    exact h
  · rw [if_neg hr] at h
    have hz := (truncatedSixthZeroDelta_discarded_zero ht hy hr).2.2
    change wuLowerCoefficient (u t y) = 0 at hz
    rw [h,kernel,hz,zero_div]

theorem c6_actual_outer_integrable :
    IntervalIntegrable
      (fun t => ∫ s in c6Lower t..c6Upper t, paperKernel wuLowerCoefficient t s)
      volume alpha beta := by
  have hc : Continuous (fun t : ℝ =>
      (1/2 : ℝ)*(∫ y in beta..(1/2-3*alpha), truncatedSixthZeroDeltaRegular 0 (t,y))) := by
    apply Continuous.const_mul
    apply gamma5Gain_moving_integral
      (f := fun t y : ℝ => truncatedSixthZeroDeltaRegular 0 (t,y))
    · exact truncatedSixthZeroDelta_regular_continuous.comp
        (f := fun v : ℝ × ℝ => (0,v)) (by fun_prop)
    · fun_prop
    · fun_prop
  apply (hc.intervalIntegrable alpha beta).congr
  intro t ht
  rw [uIcc_of_le envelope_bounds.1] at ht
  have hi : (∫ y in beta..(1/2-3*alpha), truncatedSixthZeroDeltaRegular 0 (t,y)) =
      ∫ y in beta..(1/2-3*alpha), kernel wuLowerCoefficient t y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le (by norm_num [alpha,beta] : beta ≤ 1/2-3*alpha)] at hy
    exact c6_regular_eq ht hy
  dsimp only
  rw [hi,← c6_inner_transport]
  ring

theorem c6_layered_lower {q Q : ℝ → ℝ} {Epoint Einner Eouter value : ℝ}
    (hE : 0 ≤ Epoint)
    (hq : ∀ t ∈ Icc alpha beta,
      IntervalIntegrable (paperKernel q t) volume (c6Lower t) (c6Upper t))
    (hqOuter : IntervalIntegrable
      (fun t => ∫ s in c6Lower t..c6Upper t, paperKernel q t s) volume alpha beta)
    (hQ : IntervalIntegrable Q volume alpha beta)
    (hpoint : ∀ t ∈ Icc alpha beta, ∀ s ∈ Icc (c6Lower t) (c6Upper t),
      |wuLowerCoefficient s-q s| ≤ Epoint)
    (hinner : ∀ t ∈ Icc alpha beta,
      |(∫ s in c6Lower t..c6Upper t, paperKernel q t s)-Q t| ≤ Einner)
    (houter : |(∫ t in alpha..beta, Q t)-value| ≤ Eouter) :
    8*value-8*(Eouter+Einner*(beta-alpha)+
      ((Epoint/c6KernelFloor)*c6Width)*(beta-alpha)) ≤ paperC6 wuLowerCoefficient := by
  have hf := c6_function_error hE (fun _ ht => c6_actual_inner_integrable ht) hq
    c6_actual_outer_integrable hqOuter hpoint
  have hi := interval_sub_error envelope_bounds.1 hqOuter hQ hinner
  have hf' := (abs_le.mp hf).1
  have hi' := (abs_le.mp hi).1
  have ho' := (abs_le.mp houter).1
  unfold paperC6 at hf'
  unfold paperC6
  linarith only [hf',hi',ho']

#check @c6KernelFloor
#check @c6Width
#check @c6_error_constants
#check @c6_width
#check @c6_kernel_floor
#check @c6_kernel_error
#check @interval_sub_error
#check @c6_inner_error
#check @c6_function_error
#check @c6_actual_inner_integrable
#check @c6_regular_eq
#check @c6_actual_outer_integrable
#check @c6_layered_lower
#print axioms c6KernelFloor
#print axioms c6Width
#print axioms c6_error_constants
#print axioms c6_width
#print axioms c6_kernel_floor
#print axioms c6_kernel_error
#print axioms interval_sub_error
#print axioms c6_inner_error
#print axioms c6_function_error
#print axioms c6_actual_inner_integrable
#print axioms c6_regular_eq
#print axioms c6_actual_outer_integrable
#print axioms c6_layered_lower
end WuPaper.RMapMSixth
