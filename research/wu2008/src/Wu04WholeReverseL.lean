import Wu04WholePaidActual

namespace Wu04WholeReverseL
open Wu2008DoubleSieve Real Set MeasureTheory SharpLogRecurrence JointLogTotalComparison
open Wu04FactorEnvelopes Wu04FactorLPrimitive
noncomputable section

theorem V_inverse {x : ℝ} (hx : 0<x) : V (1/x) = -V x := by
  have hp : x+1≠0 := by linarith
  have hp' : 1+x≠0 := by linarith
  unfold V lowerLog upperLog
  field_simp [hx.ne',hp,hp']
  ring

theorem factor_inverse {x : ℝ} (hx : 0<x) :
    leftFactor (1/x)=1/rightFactor x ∧ rightFactor (1/x)=1/leftFactor x := by
  have hp : 1+x≠0 := by linarith
  constructor <;> unfold leftFactor rightFactor <;> field_simp [hx.ne',hp]
  <;> ring

theorem upper_inverse {x : ℝ} (hx : 0<x) : upper (1/x) = -upper x := by
  obtain ⟨hl,hr⟩ := factor_inverse hx
  have hleft : 0<leftFactor x := by unfold leftFactor; positivity
  have hright : 0<rightFactor x := by unfold rightFactor; positivity
  unfold upper
  rw [hl,hr,V_inverse hright,V_inverse hleft]
  ring

theorem upper_le_log_small {x : ℝ} (hx : 0<x) (hx1 : x≤1) : upper x≤log x := by
  have h := log_le_upper ((le_div_iff₀ hx).2 (by linarith) : (1:ℝ)≤1/x)
  rw [upper_inverse hx] at h
  simp only [one_div,log_inv] at h
  linarith only [h]

/-- The SAME rational primitive, newly differentiated on its actual denominator domain. -/
theorem rational_deriv_small {t : ℝ} (ht : 1<t) :
    HasDerivAt rationalPart
      (1/20-2/(5*t^2)-32/(15*(t+2)^2)+128/(15*(t+2)^3)+
        32/(27*(3*t-2)^2)-128/(135*(3*t-2)^3)) t := by
  have ht0 : t≠0 := by linarith
  have hp : t+2≠0 := by linarith
  have hq : 3*t-2≠0 := by linarith
  have dp := (hasDerivAt_id t).add_const 2
  have dq := ((hasDerivAt_id t).const_mul 3).sub_const 2
  have hh := ((((((hasDerivAt_id t).div_const 20).add
    ((hasDerivAt_const t (2:ℝ)).div ((hasDerivAt_id t).const_mul 5)
      (by simpa using mul_ne_zero (by norm_num : (5:ℝ)≠0) ht0))).add
    ((hasDerivAt_const t (32:ℝ)).div (dp.const_mul 15)
      (by simpa using mul_ne_zero (by norm_num : (15:ℝ)≠0) hp))).sub
    ((hasDerivAt_const t (64:ℝ)).div ((dp.pow 2).const_mul 15)
      (by simpa using mul_ne_zero (by norm_num : (15:ℝ)≠0) (pow_ne_zero 2 hp)))).sub
    ((hasDerivAt_const t (32:ℝ)).div (dq.const_mul 81)
      (by simpa using mul_ne_zero (by norm_num : (81:ℝ)≠0) hq))).add
    ((hasDerivAt_const t (64:ℝ)).div ((dq.pow 2).const_mul 405)
      (by simpa using mul_ne_zero (by norm_num : (405:ℝ)≠0) (pow_ne_zero 2 hq)))
  convert hh using 1 <;> first | rfl | (dsimp; field_simp [ht0,hp,hq]; ring)

theorem primitive_deriv_small {t : ℝ} (ht : 1<t) : HasDerivAt primitive (lDensity t) t := by
  have ht0 : t≠0 := by linarith
  have hm : t-1≠0 := by linarith
  have hp : t+2≠0 := by linarith
  have hq : 3*t-2≠0 := by linarith
  have hh := ((((rational_deriv_small ht).add ((hasDerivAt_log ht0).div_const 5)).sub
    ((((hasDerivAt_id t).sub_const 1).log hm).div_const 20)).add
    ((((hasDerivAt_id t).add_const 2).log hp).const_mul (56/15))).sub
    (((((hasDerivAt_id t).const_mul 3).sub_const 2).log hq).const_mul (536/405))
  convert hh using 1 <;> first | rfl | skip
  · have hq' : 2*(t-1)+t≠0 := by linarith
    dsimp [lDensity,upper,V,lowerLog,upperLog,leftFactor,rightFactor]
    field_simp [ht0,hm,hp,hq,hq']
    ring_nf
    have hn : -8+t*36-t^2*54+t^3*27≠0 := by
      convert pow_ne_zero 3 hq using 1
      ring
    field_simp [hn]
    ring

theorem integrable_small {A : ℝ} (hA : 2<A) (hA3 : A≤3) :
    IntervalIntegrable lDensity volume (A-1) 2 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (μ:=volume) (h:=by linarith)
  intro t ht
  apply ContinuousAt.continuousWithinAt
  unfold lDensity
  apply ContinuousAt.div
  · exact (upper_continuous (by linarith [ht.1])).comp (by fun_prop)
  · fun_prop
  · linarith [ht.1]

theorem actual_upper_small {A : ℝ} (hA : 2<A) (hA3 : A≤3) :
    fourthRowClassicalL A≤upperL A := by
  have he : (∫ t in (A-1)..(2:ℝ), lDensity t)=primitive 2-primitive (A-1) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=primitive)
    · intro t ht
      rw [uIcc_of_le (by linarith : A-1≤2)] at ht
      exact primitive_deriv_small (by linarith [ht.1])
    · exact integrable_small hA hA3
  have h : (∫ t in (A-1)..(2:ℝ), lDensity t)≤
      ∫ t in (A-1)..(2:ℝ), log (t-1)/t := by
    apply intervalIntegral.integral_mono_on (by linarith) (integrable_small hA hA3)
      (fourthRowClassical_L_integrable hA).symm
    intro t ht
    exact div_le_div_of_nonneg_right (upper_le_log_small (by linarith [ht.1])
      (by linarith [ht.2])) (by linarith [ht.1])
  rw [he,intervalIntegral.integral_symm] at h
  change primitive 2-primitive (A-1)≤-fourthRowClassicalL A at h
  unfold upperL
  linarith only [h]

theorem collected_small {A : ℝ} (hA : 2<A) : upperL A=
    rationalPart (A-1)-rationalPart 2+log ((A-1)/2)/5-log (A-2)/20+
    (976/405)*log ((A+1)/4)-(536/405)*log ((3*A-5)/(A+1)) := by
  have h1 : A-1≠0 := by linarith
  have h2 : A-2≠0 := by linarith
  have h3 : A+1≠0 := by linarith
  have h4 : 3*A-5≠0 := by linarith
  rw [log_div h1 (by norm_num : (2:ℝ)≠0),
    log_div h3 (by norm_num : (4:ℝ)≠0),log_div h4 h3]
  unfold upperL primitive
  norm_num only [show (2:ℝ)-1=1 by norm_num,show (2:ℝ)+2=4 by norm_num,
    show 3*(2:ℝ)-2=4 by norm_num,log_one]
  rw [show A-1-1=A-2 by ring,show A-1+2=A+1 by ring,show 3*(A-1)-2=3*A-5 by ring]
  ring

end
end Wu04WholeReverseL
