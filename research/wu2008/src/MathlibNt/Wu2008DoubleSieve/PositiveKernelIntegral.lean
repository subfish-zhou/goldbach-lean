import MathlibNt.Wu2008DoubleSieve.PositiveKernelOriginal

namespace Wu2008DoubleSieve
open Set MeasureTheory Real
open scoped Interval

/-- The ratio in the cancelled parameter derivative is at least one on its full domain. -/
theorem positiveKernel_ratio_domain {a b t : ℝ} (ha : 2 < a) (_hb : 3 ≤ b)
    (hcap : b ≤ a/(a-2)) (ht : t ∈ Icc 3 b) :
    0 < (a-1)*t-a ∧ 1 ≤ t/((a-1)*t-a) := by
  have ht3 : 3 ≤ t := ht.1
  have ha2 : 0 < a-2 := by linarith
  have hh := (le_div_iff₀ ha2).mp (ht.2.trans hcap)
  have hp : 0 < (a-1)*t-a := by
    nlinarith [mul_nonneg (show 0 ≤ a-2 by linarith) (show 0 ≤ t-3 by linarith)]
  exact ⟨hp, (one_le_div hp).mpr (by nlinarith)⟩

/-- Continuous actual positive kernel, with no caller regularity premise. -/
theorem positiveKernel_continuous {a b : ℝ} (ha : 2 < a) (hb : 3 ≤ b)
    (hcap : b ≤ a/(a-2)) :
    ContinuousOn (fun t : ℝ => log (t/((a-1)*t-a))/(t-1)) (Icc 3 b) := by
  have hp (t : ℝ) (ht : t ∈ Icc 3 b) := positiveKernel_ratio_domain ha hb hcap ht
  apply ContinuousOn.div
    ((continuousOn_id.div
      ((continuousOn_const.mul continuousOn_id).sub continuousOn_const)
      (fun t ht => (hp t ht).1.ne')).log
      (fun t ht => ne_of_gt (lt_of_lt_of_le (by norm_num) (hp t ht).2)))
    (continuousOn_id.sub continuousOn_const)
    (fun t ht => ne_of_gt (by change 0 < t-1; linarith [ht.1]))

/-- Pointwise comparison after the exact logarithmic ratio cancellation. -/
theorem positiveKernel_pointwise {a b t : ℝ} (ha : 2 < a) (hb : 3 ≤ b)
    (hcap : b ≤ a/(a-2)) (ht : t ∈ Icc 3 b) :
    (2/a)*(2/(t-1)^2-(a-2)/(t-1)) ≤ log (t/((a-1)*t-a))/(t-1) := by
  have hp := positiveKernel_ratio_domain ha hb hcap ht
  have ht1 : 0 < t-1 := by linarith [ht.1]
  have ha0 : a ≠ 0 := by linarith
  have hq : t/((a-1)*t-a)+1 ≠ 0 := by linarith [hp.2]
  have hl := div_le_div_of_nonneg_right (positiveKernel_log_lower hp.2) ht1.le
  have he : (2*(t/((a-1)*t-a)-1)/(t/((a-1)*t-a)+1))/(t-1) =
      (2/a)*(2/(t-1)^2-(a-2)/(t-1)) := by
    rw [div_sub_one hp.1.ne', div_add_one hp.1.ne']
    rw [show t + ((a-1)*t-a) = a*(t-1) by ring]
    have hp' : t*(a-1)-a ≠ 0 := by nlinarith [hp.1]
    field_simp [ha0, ht1.ne', hp.1.ne', hp']
    ring
  rwa [he] at hl

/-- The full positive-kernel integral admits the fixed rational lower expression. -/
theorem positiveKernel_integral_lower {a b : ℝ} (ha : 2 < a) (hb : 3 ≤ b)
    (hcap : b ≤ a/(a-2)) :
    (2/a)*(1-2/(b-1)-(a-2)*((((b-1)/2)^2-1)/(2*((b-1)/2)))) ≤
      ∫ t in (3 : ℝ)..b, log (t/((a-1)*t-a))/(t-1) := by
  let g : ℝ → ℝ := fun t => (2/a)*(2/(t-1)^2-(a-2)/(t-1))
  let P : ℝ → ℝ := fun t => (2/a)*(-2/(t-1)-(a-2)*log (t-1))
  have cg : ContinuousOn g (Icc 3 b) := by
    apply continuousOn_const.mul
    apply ContinuousOn.sub
    · exact continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow 2)
        (fun t ht => pow_ne_zero _ (by linarith [ht.1]))
    · exact continuousOn_const.div (continuousOn_id.sub continuousOn_const)
        (fun t ht => by linarith [ht.1])
  have hd (t : ℝ) (ht : t ∈ uIcc 3 b) : HasDerivAt P (g t) t := by
    rw [uIcc_of_le hb] at ht
    have ht1 : t-1 ≠ 0 := by linarith [ht.1]
    convert! ((((hasDerivAt_const t (-2)).div ((hasDerivAt_id t).sub_const 1) ht1).sub
      ((((hasDerivAt_id t).sub_const 1).log ht1).const_mul (a-2))).const_mul (2/a)) using 1
    dsimp [P, g]
    field_simp
    ring
  have hg : IntervalIntegrable g volume 3 b := cg.intervalIntegrable_of_Icc hb
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hg
  have hm := intervalIntegral.integral_mono_on hb hg
    ((positiveKernel_continuous ha hb hcap).intervalIntegrable_of_Icc hb)
    (fun t ht => positiveKernel_pointwise ha hb hcap ht)
  have hb1 : 0 < b-1 := by linarith
  have hex : log ((b-1)/2) = log (b-1)-log 2 := log_div hb1.ne' (by norm_num)
  have heval : P b - P 3 = (2/a)*(1-2/(b-1)-(a-2)*log ((b-1)/2)) := by
    dsimp [P]
    rw [hex]
    norm_num
    ring
  rw [he, heval] at hm
  have hl := positiveKernel_log_upper (x := (b-1)/2) (by linarith)
  have ha0 : 0 ≤ 2/a := by positivity
  have hp := mul_le_mul_of_nonneg_left hl (show 0 ≤ a-2 by linarith)
  have hm' := mul_le_mul_of_nonneg_left (sub_le_sub_left hp (1-2/(b-1))) ha0
  exact hm'.trans hm

end Wu2008DoubleSieve
