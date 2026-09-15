import SixthLogTotalMagnitude

namespace Wu2008DoubleSieve.SixthFullRationalEnclosure
open Real Set MeasureTheory SharpLogRecurrence JointLogTotalComparison TotalEndpointComparison
open ClassicalLossBottleneck ClassicalAnalyticLeaves SharpMassBalance
open PositiveSixthFTC DynamicSixthEnvelope
open scoped Interval
noncomputable section

/-- A majorant of the existing rational gap, not a new logarithm expansion. -/
theorem gap_cubic {t : ℝ} (ht : 1 ≤ t) :
    log t-lowerLog t ≤ (t-1)^3/464 := by
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < t+1 := by linarith
  have hA : 8*(t-1) ≤ (t+1)^2 := by nlinarith [sq_nonneg (t-3)]
  have hB : (29/5)*(t-1) ≤ t*(t+1) := by nlinarith [sq_nonneg (t-12/5)]
  have hmul := mul_le_mul hA hB (by positivity : 0 ≤ (29/5)*(t-1)) (sq_nonneg (t+1))
  have hden : (232/5)*(t-1)^2 ≤ t*(t+1)^3 := by nlinarith only [hmul]
  have hprod := mul_le_mul_of_nonneg_left hden (show 0 ≤ (t-1)^3 by positivity)
  have hg : (3/5)*(upperLog t-lowerLog t) ≤ (t-1)^3/464 := by
    have he : (3/5)*(upperLog t-lowerLog t) = (t-1)^5/(10*t*(t+1)^3) := by
      unfold upperLog lowerLog
      field_simp
      ring
    rw [he]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith only [hprod]
  have hv := log_le_V ht
  unfold V at hv
  linarith only [hv,hg]

def firstA : ℝ := 1/(464*a^4*b*(1/2-2*b))
def poly (r : ℝ) : ℝ := 8/3-4*r+2*r^2-(2/3)*r^3
def originalRatio : ℝ := 2*a/(1/2-a)
def sCap : ℝ := poly originalRatio/(1/2-b)
def secondA : ℝ := sCap/a*((1/(2*a)^3+1/b^3)/464)
def payment : ℝ :=
  firstA*((lam-a-b)^5-(lam-2*b)^5)/5+
  secondA*((lam-a-b)^4-(lam-2*b)^4)

theorem fixed_signs : 0 < 1/2-2*b ∧ 0 ≤ firstA ∧ 0 ≤ secondA ∧
    0 ≤ poly originalRatio ∧ 0 < 1/2-b ∧ 0 ≤ originalRatio ∧ originalRatio ≤ 1 := by
  norm_num [firstA,secondA,sCap,poly,originalRatio,a,b,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

theorem first_pointwise {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc b (lam-x)) :
    sixthLogRegular x y ≤ Phase25.exactKernel x y+firstA*(lam-x-y)^3 := by
  have hg := Phase25.mask_geometry hx hy
  have ha := geometry.1
  have hb := geometry.2.2.1
  have hba : b ≤ 2*a := by norm_num [a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  have hs2 : 2 ≤ truncatedSixthLowerS 0 x y := by
    apply (le_div_iff₀ ha).2
    dsimp [truncatedSixthLowerC]
    simpa only [sub_zero] using hg.2.2.2.2
  have hgap := gap_cubic (t := truncatedSixthLowerS 0 x y-1) (by linarith)
  have hdshape : truncatedSixthLowerS 0 x y-1-1 = (lam-x-y)/a := by
    unfold truncatedSixthLowerS truncatedSixthLowerC lam
    field_simp
    ring
  rw [hdshape] at hgap
  have hdy : b*(1/2-2*b) ≤ y*(1/2-x-y) := by
    have hp := mul_nonneg (sub_nonneg.mpr hy.1)
      (show 0 ≤ 1/2-x-y-b by linarith [hg.2.2.2.2])
    have hq := mul_nonneg hb.le (show 0 ≤ b-x by linarith [hx.2])
    nlinarith only [hp,hq]
  have hden : a*b*(1/2-2*b) ≤ x*y*(1/2-x-y) := by
    have hp := mul_le_mul hx.1 hdy (mul_nonneg hb.le fixed_signs.1.le) hg.1.le
    nlinarith only [hp]
  have he : Phase25.exactKernel x y = lowerLog (truncatedSixthLowerS 0 x y-1)/(x*y*(1/2-x-y)) := by
    have hz' : 1-x*2-y*2 ≠ 0 := by linarith [hg.2.2.2.1]
    simp only [Phase25.exactKernel,lowerLog,truncatedSixthLowerS,truncatedSixthLowerC,lam,sub_zero]
    field_simp [ha.ne',hg.1.ne',hg.2.1.ne',hg.2.2.2.1.ne',hz']
    ring
  have hn : 0 ≤ lam-x-y := by linarith [hy.2]
  have hdiv := div_le_div_of_nonneg_right hgap
    (mul_pos (mul_pos hg.1 hg.2.1) hg.2.2.2.1).le
  have hdiv2 := div_le_div_of_nonneg_left
    (show 0 ≤ ((lam-x-y)/a)^3/464 by positivity)
    (show 0 < a*b*(1/2-2*b) by exact mul_pos (mul_pos ha hb) fixed_signs.1) hden
  have he2 : (((lam-x-y)/a)^3/464)/(a*b*(1/2-2*b)) = firstA*(lam-x-y)^3 := by
    unfold firstA
    field_simp
  rw [he2] at hdiv2
  rw [sixth_log_retained hx hy,he]
  rw [sub_div] at hdiv
  linarith only [hdiv,hdiv2]

theorem S_cap {x : ℝ} (hx : x ∈ Icc a b) : Phase25.S (1/2-x) (2*a) ≤ sCap := by
  have hg := Phase25.outer_geometry hx
  have ha := geometry.1
  have hc : 0 < 1/2-a := by norm_num [a,truncatedSixthLowerAlpha]
  have hr : originalRatio ≤ 2*a/(1/2-x) := by
    unfold originalRatio
    exact div_le_div_of_nonneg_left (by positivity) hg.2.1 (by linarith [hx.1])
  have hr1 : 2*a/(1/2-x) ≤ 1 := by
    apply (div_le_iff₀ hg.2.1).2
    linarith [hg.2.2.2.1]
  have hr0 : 0 ≤ 2*a/(1/2-x) := div_nonneg (by positivity) hg.2.1.le
  have hp : poly (2*a/(1/2-x)) ≤ poly originalRatio := by
    have hq : 0 ≤ 4-2*(2*a/(1/2-x)+originalRatio)+
        (2/3)*((2*a/(1/2-x))^2+(2*a/(1/2-x))*originalRatio+originalRatio^2) := by
      have hlin : 0 ≤ 4-2*(2*a/(1/2-x)+originalRatio) := by linarith [fixed_signs.2.2.2.2.2.2]
      have hrp := fixed_signs.2.2.2.2.2.1
      positivity
    have hm := mul_nonneg (sub_nonneg.mpr hr) hq
    unfold poly
    nlinarith only [hm]
  have generic (c h : ℝ) (hc : c ≠ 0) : Phase25.S c h = poly (h/c)/c := by
    unfold Phase25.S poly
    field_simp [hc]
  have he := generic (1/2-x) (2*a) hg.2.1.ne'
  rw [he]
  exact (div_le_div_of_nonneg_right hp hg.2.1.le).trans
    (div_le_div_of_nonneg_left fixed_signs.2.2.2.1 fixed_signs.2.2.2.2.1
      (by linarith [hx.2]))

theorem second_pointwise {x : ℝ} (hx : x ∈ Icc a b) :
    Phase25.movingExact x ≤ Phase25.rationalInner (1/2-x)+secondA*(lam-b-x)^3 := by
  have hg := Phase25.outer_geometry hx
  have ha := geometry.1
  have hb := geometry.2.2.1
  have h1 : 1 ≤ (1/2-x-b)/(2*a) := (le_div_iff₀ (by positivity)).2 (by linarith [hg.2.2.2.2])
  have h2 : 1 ≤ (1/2-x-2*a)/b := (le_div_iff₀ hb).2 (by linarith [hg.2.2.2.2])
  have he1 := gap_cubic h1
  have he2 := gap_cubic h2
  have he : ((1/2-x-b)/(2*a)-1)^3/464+((1/2-x-2*a)/b-1)^3/464 =
      ((1/(2*a)^3+1/b^3)/464)*(lam-b-x)^3 := by
    unfold lam
    field_simp
    ring
  have herr : (log ((1/2-x-b)/(2*a))-lowerLog ((1/2-x-b)/(2*a)))+
      (log ((1/2-x-2*a)/b)-lowerLog ((1/2-x-2*a)/b)) ≤
      ((1/(2*a)^3+1/b^3)/464)*(lam-b-x)^3 := by linarith only [he1,he2,he]
  have hs := Phase25.S_pos (h := 2*a) hg.2.1 (by linarith [hg.2.2.2.1])
  have hcoef : Phase25.S (1/2-x) (2*a)/x ≤ sCap/a :=
    (div_le_div_of_nonneg_right (S_cap hx) hg.1.le).trans
      (div_le_div_of_nonneg_left
        (div_nonneg fixed_signs.2.2.2.1 fixed_signs.2.2.2.2.1.le) ha hx.1)
  have hp := mul_le_mul hcoef herr
    (show 0 ≤ (log ((1/2-x-b)/(2*a))-lowerLog ((1/2-x-b)/(2*a)))+
      (log ((1/2-x-2*a)/b)-lowerLog ((1/2-x-2*a)/b)) from
      add_nonneg (sub_nonneg.mpr (log_lower h1)) (sub_nonneg.mpr (log_lower h2)))
    (show 0 ≤ sCap/a by exact div_nonneg (div_nonneg fixed_signs.2.2.2.1 fixed_signs.2.2.2.2.1.le) ha.le)
  rw [Phase25.movingExact_endpoint,Phase25.endpoint_difference hg.2.2.1 hg.2.2.2.1]
  unfold Phase25.rationalInner secondA
  rw [show (1/2:ℝ)-(1/2-x)=x by ring]
  ring_nf at hp ⊢
  linarith only [hp]

theorem inner_cap {x : ℝ} (hx : x ∈ Icc a b) :
    (∫ y in b..s, sixthLogRegular x y) ≤ Phase25.rationalInner (1/2-x)+
      secondA*(lam-b-x)^3+firstA*(lam-b-x)^4/4 := by
  have hc := sixth_log_continuous.comp (f := fun y : ℝ => (x,y)) (by fun_prop)
  have hp : Continuous (fun y : ℝ => firstA*(lam-x-y)^3) := by fun_prop
  have he : (∫ y in b..(lam-x), firstA*(lam-x-y)^3) = firstA*(lam-b-x)^4/4 := by
    have hd (y : ℝ) : HasDerivAt (fun y : ℝ => -firstA*(lam-x-y)^4/4) (firstA*(lam-x-y)^3) y := by
      convert (((((hasDerivAt_const y (lam-x)).sub (hasDerivAt_id y)).pow 4).const_mul (-firstA)).div_const 4) using 1 <;>
        first | rfl | (dsimp; ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y) (hp.intervalIntegrable b (lam-x))]
    ring
  have hi := intervalIntegral.integral_mono_on (μ := volume) (moving_geometry hx).1
    (hc.intervalIntegrable b (lam-x)) ((Phase25.inner_integrable hx).add (hp.intervalIntegrable b (lam-x)))
    (fun y hy => first_pointwise hx hy)
  rw [intervalIntegral.integral_add (Phase25.inner_integrable hx) (hp.intervalIntegrable b (lam-x)),
    Phase25.inner_ftc hx,he] at hi
  have hcomp : (∫ y in (lam-x)..s, sixthLogRegular x y) = 0 := by
    calc
      _ = ∫ _y in (lam-x)..s, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro y hy
        have hy' : y ∈ Icc (lam-x) s := uIcc_of_le (moving_geometry hx).2 ▸ hy
        have hh := sixth_log_pointwise hx ⟨(moving_geometry hx).1.trans hy'.1,hy'.2⟩
        rw [sixth_complement_zero hx hy'] at hh
        have hn := sixth_log_nonnegative x y
        linarith only [hh.1,hn]
      _ = 0 := by simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable b (lam-x)) (hc.intervalIntegrable (lam-x) s)
  simp only [Function.comp_apply] at hi hadd
  rw [hcomp,add_zero] at hadd
  rw [← hadd]
  linarith only [hi,second_pointwise hx]

/-- Exact FTC on the original outer interval, with both moving widths retained. -/
theorem error_ftc : (∫ x in a..b,
    secondA*(lam-b-x)^3+firstA*(lam-b-x)^4/4) = payment/4 := by
  have hc : Continuous (fun x : ℝ => secondA*(lam-b-x)^3+firstA*(lam-b-x)^4/4) := by fun_prop
  have hd (x : ℝ) : HasDerivAt
      (fun x : ℝ => -secondA*(lam-b-x)^4/4-firstA*(lam-b-x)^5/20)
      (secondA*(lam-b-x)^3+firstA*(lam-b-x)^4/4) x := by
    have hh := (hasDerivAt_const x (lam-b)).sub (hasDerivAt_id x)
    convert (((hh.pow 4).const_mul (-secondA)).div_const 4).sub
      (((hh.pow 5).const_mul firstA).div_const 20) using 1 <;>
      first | rfl | (dsimp; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hc.intervalIntegrable a b)]
  unfold payment
  ring

/-- An upper bound on the actual entire log recovery, not on a lower certificate. -/
theorem sixth_log_loss_enclosure : 0 ≤ sixthLogIntegral-AnalyticTotalThreshold.sixthEndpoint ∧
    sixthLogIntegral-AnalyticTotalThreshold.sixthEndpoint ≤ payment := by
  have hc : Continuous (fun x : ℝ => ∫ y in b..s, sixthLogRegular x y) := by
    apply gamma5Gain_moving_integral (f := sixthLogRegular) sixth_log_continuous <;> fun_prop
  have hp : Continuous (fun x : ℝ => secondA*(lam-b-x)^3+firstA*(lam-b-x)^4/4) := by fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) geometry.2.1
    (hc.intervalIntegrable a b) (Phase25.rationalInner_integrable.add (hp.intervalIntegrable a b))
    (fun x hx => show (∫ y in b..s, sixthLogRegular x y) ≤
      Phase25.rationalInner (1/2-x)+(secondA*(lam-b-x)^3+firstA*(lam-b-x)^4/4) by
      linarith only [inner_cap hx])
  rw [intervalIntegral.integral_add Phase25.rationalInner_integrable (hp.intervalIntegrable a b),
    Phase25.outer_ftc,error_ftc] at hi
  refine ⟨sub_nonneg.mpr sixth_endpoint_le_logIntegral,?_⟩
  unfold sixthLogIntegral AnalyticTotalThreshold.sixthEndpoint
  linarith only [hi]

theorem payment_rational : payment =
    12668392205825669083051546998568581059/184907485620484188577841127859200000000 := by
  norm_num [payment,firstA,secondA,sCap,poly,originalRatio,lam,a,b,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

theorem sixth_log_loss_lt : sixthLogIntegral-AnalyticTotalThreshold.sixthEndpoint < 7/100 := by
  have h := sixth_log_loss_enclosure.2
  rw [payment_rational] at h
  linarith only [h]

/-- The original full sixth term; the recurrence surplus is included once. -/
theorem actual_sixth_loss_lt : AnalyticTotalThreshold.sixthLoss < 7001/100000 := by
  have h := sixth_loss_localization.2
  have h6 := sixth_log_loss_lt
  linarith only [h,h6]

end
end Wu2008DoubleSieve.SixthFullRationalEnclosure
