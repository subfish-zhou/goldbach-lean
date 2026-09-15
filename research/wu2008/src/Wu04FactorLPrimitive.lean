import Wu04FactorEnvelopes

namespace Wu04FactorLPrimitive
open Wu2008DoubleSieve Wu04FactorEnvelopes Real Set MeasureTheory
open SharpLogRecurrence JointLogTotalComparison
noncomputable section

/-- Exact partial fractions of the fixed, once-factorized V kernel. -/
def rationalPart (t : ℝ) : ℝ :=
  t/20+2/(5*t)+32/(15*(t+2))-64/(15*(t+2)^2)-32/(81*(3*t-2))+64/(405*(3*t-2)^2)
def primitive (t : ℝ) : ℝ := rationalPart t+log t/5-log (t-1)/20+
  (56/15)*log (t+2)-(536/405)*log (3*t-2)

theorem rational_deriv {t : ℝ} (ht : 2≤t) :
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

theorem primitive_deriv {t : ℝ} (ht : 2≤t) : HasDerivAt primitive (lDensity t) t := by
  have ht0 : t≠0 := by linarith
  have hm : t-1≠0 := by linarith
  have hp : t+2≠0 := by linarith
  have hq : 3*t-2≠0 := by linarith
  have hh := ((((rational_deriv ht).add ((hasDerivAt_log ht0).div_const 5)).sub
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

def upperL (A : ℝ) : ℝ := primitive (A-1)-primitive 2

/-- Literal FTC on the old full integration domain; no numerical quadrature. -/
theorem integral_eq {A : ℝ} (hA : 3≤A) : lIntegral A=upperL A := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=primitive)
  · intro t ht
    rw [uIcc_of_le (by linarith : (2:ℝ)≤A-1)] at ht
    exact primitive_deriv ht.1
  · exact l_integrable hA

theorem actual_upper {A : ℝ} (hA : 3≤A) : fourthRowClassicalL A≤upperL A := by
  rw [← integral_eq hA]
  exact l_upper hA

/-- Exact collection before any endpoint logarithm is paid. -/
theorem collected {A : ℝ} (hA : 3≤A) : upperL A=
    rationalPart (A-1)-rationalPart 2 + log ((A-1)/2)/5-log (A-2)/20+
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
end Wu04FactorLPrimitive
