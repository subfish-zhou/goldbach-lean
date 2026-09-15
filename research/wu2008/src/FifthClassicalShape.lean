import SignedTotalCorrelation

namespace Wu2008DoubleSieve.FifthClassicalShape
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence
open SharpMassBalance
open scoped Interval

noncomputable def q : ℝ := (1/2-2*a)/a
noncomputable def f (s : ℝ) : ℝ := lowerLog (s-1)/s
noncomputable def c : ℝ := (f q-f s0)/(q-s0)
noncomputable def g (r : ℝ) : ℝ := 8*r/3-8*r^2+8*r^3-16*r^4/3

 theorem parameters : 3 < s0 ∧ s0 < q ∧ q < 5 := by
  norm_num [s0,q,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

 theorem c_pos : 0 < c := by
  norm_num [c,f,q,s0,lowerLog,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

 theorem f_recip {s : ℝ} (hs : s ≠ 0) : f s = g (1/s) := by
  dsimp [f,g,lowerLog]
  field_simp [hs]
  ring

 theorem g_chord {l r h : ℝ} (hl : 0 ≤ l) (hlr : l ≤ r) (hrh : r ≤ h)
    (hh : h ≤ 1/3) (hlh : l < h) :
    ((h-r)*g l+(r-l)*g h)/(h-l) ≤ g r := by
  have hr := hl.trans hlr
  have hh0 := hr.trans hrh
  have hsum : 0 ≤ 8-8*(r+l+h) := by linarith
  have hquad : 0 ≤ r^2+(l+h)*r+l^2+l*h+h^2 := by positivity
  have hprod := mul_nonneg (mul_nonneg (sub_nonneg.mpr hlr) (sub_nonneg.mpr hrh))
    (add_nonneg hsum (mul_nonneg (by norm_num : (0:ℝ) ≤ 16/3) hquad))
  have hid : g r-((h-r)*g l+(r-l)*g h)/(h-l) =
      (r-l)*(h-r)*(8-8*(r+l+h)+(16/3)*(r^2+(l+h)*r+l^2+l*h+h^2)) := by
    dsimp [g]
    field_simp [(sub_pos.mpr hlh).ne']
    ring
  linarith

 theorem f_chord {s : ℝ} (hp : s0 ≤ s) (hq : s ≤ q) :
    f s0+c*(s-s0) ≤ f s := by
  have hp0 : 0 < s0 := by linarith [parameters.1]
  have hq0 : 0 < q := hp0.trans parameters.2.1
  have hs0 := hp0.trans_le hp
  have hrec := g_chord (l := 1/q) (r := 1/s) (h := 1/s0)
    (by positivity) (one_div_le_one_div_of_le hs0 hq)
    (one_div_le_one_div_of_le hp0 hp)
    (by apply (div_le_div_iff₀ hp0 (by norm_num : (0:ℝ)<3)).2; linarith [parameters.1])
    ((one_div_lt_one_div hq0 hp0).2 parameters.2.1)
  rw [← f_recip hq0.ne',← f_recip hs0.ne',← f_recip hp0.ne'] at hrec
  have hid : ((1/s0-1/s)*f q+(1/s-1/q)*f s0)/(1/s0-1/q) =
      f s0+c*(s-s0)*(q/s) := by
    dsimp [c]
    field_simp [hs0.ne',hp0.ne',hq0.ne',(sub_pos.mpr parameters.2.1).ne', (ne_of_lt parameters.2.1)]
    ring
  rw [hid] at hrec
  have hrat : 1 ≤ q/s := (le_div_iff₀ hs0).2 (by simpa using hq)
  have hnon := mul_nonneg c_pos.le (sub_nonneg.mpr hp)
  have hm := mul_le_mul_of_nonneg_left hrat hnon
  nlinarith

noncomputable def shapeKernel (x y : ℝ) : ℝ :=
  (fifthDensity+(c/a^2)*(2*b-x-y))/(x*y)

 theorem shape_lower {x y : ℝ} (hx : a ≤ x) (hxy : x ≤ y) (hy : y ≤ b) :
    shapeKernel x y ≤ fifthPairRegular 0 (x,y) := by
  have ha := truncatedSixthLower_parameters.1
  have hx0 := ha.trans_le hx
  have hy0 := hx0.trans_le hxy
  have hslo : s0 ≤ truncatedSixthLowerS 0 x y := by
    apply (div_le_div_iff_of_pos_right ha).2
    dsimp [s0,truncatedSixthLowerC]
    linarith [hxy.trans hy]
  have hshi : truncatedSixthLowerS 0 x y ≤ q := by
    apply (div_le_div_iff_of_pos_right ha).2
    dsimp [q,truncatedSixthLowerC]
    linarith [hx.trans hxy]
  have hs2 : 2 ≤ truncatedSixthLowerS 0 x y := by linarith [parameters.1]
  have hspos : 0 < truncatedSixthLowerS 0 x y := by linarith
  have hz : 0 < 1/2-x-y := by
    have hb : b < 1/4 := by norm_num [b,truncatedSixthLowerBeta]
    linarith [hxy.trans hy]
  have hlog := (log_lower (t := truncatedSixthLowerS 0 x y-1) (by linarith)).trans
    (lower_ge_log hs2)
  have hf := f_chord hslo hshi
  have hdiv := div_le_div_of_nonneg_right hlog hspos.le
  have hall : f s0+c*(truncatedSixthLowerS 0 x y-s0) ≤
      wuLowerCoefficient (truncatedSixthLowerS 0 x y)/truncatedSixthLowerS 0 x y := hf.trans hdiv
  have hh := div_le_div_of_nonneg_right hall (mul_pos ha (mul_pos hx0 hy0)).le
  rw [ClassicalPositiveBounds.fifth_regular_eq hx hxy hy]
  have hz' : 1-x*2-y*2 ≠ 0 := by linarith
  convert hh using 1 <;> first | rfl |
    (simp only [shapeKernel,fifthDensity,f,s0,truncatedSixthLowerS,truncatedSixthLowerC,sub_zero]
     field_simp [ha.ne',hx0.ne',hy0.ne',hz.ne',hz']
     <;> ring)

noncomputable def k : ℝ := c/a^2
noncomputable def innerShape (y : ℝ) : ℝ :=
  ((fifthDensity+k*(2*b-y))*(log y-log a)-k*(y-a))/y
noncomputable def primitive (y : ℝ) : ℝ :=
  (fifthDensity/2+k*b)*(log y-log a)^2-k*(y-a)*(log y-log a)

 theorem inner_integral {y : ℝ} (hy : a ≤ y) :
    (∫ x in a..y, shapeKernel x y) = innerShape y := by
  have ha := truncatedSixthLower_parameters.1
  have hy0 := ha.trans_le hy
  have hn (x : ℝ) (hx : x ∈ uIcc a y) : x ≠ 0 := by
    rw [uIcc_of_le hy] at hx
    exact (ha.trans_le hx.1).ne'
  have hi : IntervalIntegrable (fun x => shapeKernel x y) volume a y := by
    apply ContinuousOn.intervalIntegrable
    unfold shapeKernel
    exact (continuousOn_const.add (continuousOn_const.mul
      ((continuousOn_const.sub continuousOn_id).sub continuousOn_const))).div
      (continuousOn_id.mul continuousOn_const) (fun x hx => mul_ne_zero (hn x hx) hy0.ne')
  have hd (x : ℝ) (hx : x ∈ uIcc a y) :
      HasDerivAt (fun x => ((fifthDensity+k*(2*b-y))*log x-k*x)/y)
        (shapeKernel x y) x := by
    have hh := (((hasDerivAt_log (hn x hx)).const_mul (fifthDensity+k*(2*b-y))).sub
      ((hasDerivAt_id x).const_mul k)).div_const y
    convert hh using 1 <;> first | rfl | (dsimp [shapeKernel,k]; field_simp [hn x hx,hy0.ne']; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  dsimp [innerShape]
  ring

 theorem primitive_derivative {y : ℝ} (hy : a ≤ y) :
    HasDerivAt primitive (innerShape y) y := by
  have ha := truncatedSixthLower_parameters.1
  have hlog := (hasDerivAt_log (ha.trans_le hy).ne').sub_const (log a)
  have hh := ((hlog.pow 2).const_mul (fifthDensity/2+k*b)).sub
    ((((hasDerivAt_id y).sub_const a).const_mul k).mul hlog)
  convert hh using 1 <;> first | rfl | (dsimp [innerShape]; field_simp [(ha.trans_le hy).ne']; ring)

 theorem shape_integral_lower :
    2*fifthDensity*(log b-log a)^2 +
      4*k*(b*(log b-log a)^2-(b-a)*(log b-log a)) ≤ fifthPairFlin := by
  have hp := truncatedSixthLower_parameters
  have hc : Continuous (fun v : ℝ × ℝ => fifthPairRegular 0 (v.1,v.2)) :=
    fifthPair_regular_continuous.comp (f := fun v : ℝ × ℝ => (0,v)) (by fun_prop)
  have hinner : Continuous (fun y : ℝ => ∫ x in a..y, fifthPairRegular 0 (x,y)) := by
    apply gamma5Gain_moving_integral (f := fun y x : ℝ => fifthPairRegular 0 (x,y))
    · exact hc.comp (f := fun v : ℝ × ℝ => (v.2,v.1)) (by fun_prop)
    · fun_prop
    · fun_prop
  have hn (y : ℝ) (hy : y ∈ uIcc a b) : y ≠ 0 := by
    rw [uIcc_of_le hp.2.1.le] at hy
    exact (hp.1.trans_le hy.1).ne'
  have hil : ContinuousOn (fun y : ℝ => log y-log a) (uIcc a b) :=
    (continuousOn_id.log (fun y hy => hn y hy)).sub continuousOn_const
  have hi0 : IntervalIntegrable innerShape volume a b := by
    apply ContinuousOn.intervalIntegrable
    unfold innerShape
    exact (((continuousOn_const.add (continuousOn_const.mul
      (continuousOn_const.sub continuousOn_id))).mul hil).sub
      (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))).div
      continuousOn_id (fun y hy => hn y hy)
  have hpoint (y : ℝ) (hy : y ∈ Icc a b) :
      innerShape y ≤ ∫ x in a..y, fifthPairRegular 0 (x,y) := by
    rw [← inner_integral hy.1]
    have hy0 := hp.1.trans_le hy.1
    have hi : IntervalIntegrable (fun x => shapeKernel x y) volume a y := by
      apply ContinuousOn.intervalIntegrable
      unfold shapeKernel
      apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro x hx
        rw [uIcc_of_le hy.1] at hx
        exact mul_ne_zero (hp.1.trans_le hx.1).ne' hy0.ne'
    exact intervalIntegral.integral_mono_on hy.1 hi
      ((hc.comp (f := fun x : ℝ => (x,y)) (by fun_prop)).intervalIntegrable a y)
      (fun x hx => shape_lower hx.1 hx.2 hy.2)
  have hi := intervalIntegral.integral_mono_on hp.2.1.le hi0 (hinner.intervalIntegrable a b) hpoint
  have hd (y : ℝ) (hy : y ∈ uIcc a b) : HasDerivAt primitive (innerShape y) y := by
    rw [uIcc_of_le hp.2.1.le] at hy
    exact primitive_derivative hy.1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi0] at hi
  have hf : fifthPairFlin = 4*∫ y in a..b, ∫ x in a..y, fifthPairRegular 0 (x,y) := by
    unfold fifthPairFlin fifthPairFdelta
    congr 1
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hp.2.1.le] at hy
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hy.1] at hx
    simpa [truncatedSixthLowerC] using (ClassicalPositiveBounds.fifth_regular_eq hx.1 hx.2 hy.2).symm
  rw [hf]
  dsimp [primitive] at hi
  nlinarith

noncomputable def ell : ℝ := lowerLog (b/a)
noncomputable def gain : ℝ := 4*k*(b*ell^2-(b-a)*ell)
noncomputable def payment : ℝ := UnroundedPayments.fifthRational+gain

 theorem gain_eq : gain =
    (1795553815637706348019306386522551526163767104000/
      36411738079303669111954326479710727233818552234261 : ℝ) := by
  norm_num [gain,k,c,f,q,s0,ell,lowerLog,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

 theorem gain_gt : (1/25 : ℝ) < gain := by
  rw [gain_eq]
  norm_num

 theorem payment_lt_fifthPairFlin : payment < fifthPairFlin := by
  have hl := UnroundedPayments.lowerLog_lt_log (t := b/a)
    (by norm_num [a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta])
  obtain ⟨hd,he⟩ := UnroundedPayments.fifth_payment_positive
  have hlower : ell < log b-log a := by
    rw [← log_div (by norm_num [b,truncatedSixthLowerBeta])
      (by norm_num [a,truncatedSixthLowerAlpha])]
    exact hl
  have he0 : 0 < ell := he
  have hk : 0 < k := div_pos c_pos (sq_pos_of_pos truncatedSixthLower_parameters.1)
  have hb : 0 < b := by norm_num [b,truncatedSixthLowerBeta]
  have hm : 0 < b*ell-(b-a) := by
    norm_num [ell,lowerLog,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  have hs : ell^2 < (log b-log a)^2 := by nlinarith
  have hbase := mul_lt_mul_of_pos_left hs (mul_pos (by norm_num : (0:ℝ)<2) hd)
  have hfactor : 0 ≤ (log b-log a-ell)*(b*(log b-log a+ell)-(b-a)) := by
    apply mul_nonneg (by linarith)
    nlinarith
  have hquad : b*ell^2-(b-a)*ell ≤
      b*(log b-log a)^2-(b-a)*(log b-log a) := by nlinarith
  have hgain := mul_le_mul_of_nonneg_left hquad (mul_nonneg (by norm_num : (0:ℝ)≤4) hk.le)
  have hi := shape_integral_lower
  dsimp [payment,UnroundedPayments.fifthRational,gain,ell] at *
  linarith

 theorem old_payment_add_gain_lt :
    UnroundedPayments.fifthRational+gain < fifthPairFlin := payment_lt_fifthPairFlin

 theorem old_payment_add_one_twentyfifth_lt :
    UnroundedPayments.fifthRational+1/25 < fifthPairFlin := by
  linarith [old_payment_add_gain_lt,gain_gt]

#print axioms shape_lower
#print axioms shape_integral_lower
#print axioms gain_eq
#print axioms payment_lt_fifthPairFlin
#print axioms old_payment_add_one_twentyfifth_lt
end Wu2008DoubleSieve.FifthClassicalShape
