import Wu18938Campaign.M3.Confirmed.FifthMoments

noncomputable section

namespace Wu18938Campaign.M3.Confirmed.FifthClassical

open Real Wu2008DoubleSieve SharpMassBalance FifthShape FifthMoments

def offset : ℝ := 1/(2*a)-4
def p0 : ℝ :=
  (center/4+linear*offset+quadratic*offset^2+cubic*offset^3-quartic*offset^4)/a
def p1 : ℝ := -(linear+2*quadratic*offset+3*cubic*offset^2-4*quartic*offset^3)/a^2
def p2 : ℝ := (quadratic+3*cubic*offset-6*quartic*offset^2)/a^3
def p3 : ℝ := -(cubic-4*quartic*offset)/a^4
def p4 : ℝ := -quartic/a^5
def logCoefficient : ℝ :=
  4*p1*(b-a)+2*p2*(b^2-a^2)+(4/3)*p3*(b^3-a^3)+p4*(b^4-a^4)
def constantCoefficient : ℝ :=
  4*p2*(b-a)^2+6*p3*(b-a)*(b^2-a^2)+
    p4*((16/3)*(b-a)*(b^3-a^3)+3*(b^2-a^2)^2)
def rationalLower : ℝ :=
  2*p0*(TableBounds.logLower (b/a))^2+
    logCoefficient*TableBounds.logLower (b/a)+constantCoefficient

theorem kernel_identity (x y : ℝ) :
    kernel p0 p1 p2 p3 p4 x y = shape ((1/2-x-y)/a)/(a*x*y) := by
  simp only [kernel,WuTarget.FifthClassicalClosure.quadratic_kernel_literal,
    p0,p1,p2,p3,p4,shape,offset]
  field_simp [truncatedSixthLower_parameters.1.ne']
  ring

theorem original_kernel_lower {x y : ℝ} (hx : a ≤ x) (hxy : x ≤ y) (hy : y ≤ b) :
    kernel p0 p1 p2 p3 p4 x y ≤ FifthActualIntegralRecovery.logRegular x y := by
  have ha := truncatedSixthLower_parameters.1
  have hx0 := ha.trans_le hx
  have hy0 := hx0.trans_le hxy
  have hp := FifthActualIntegralRecovery.parameter_range hx hxy hy
  have hs : 17/5 ≤ truncatedSixthLowerS 0 x y := by
    have h0 : (17/5:ℝ) ≤ s0 := by
      norm_num [s0,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
    exact h0.trans hp.1
  have hh := div_le_div_of_nonneg_right (scalar_lower hs)
    (mul_pos ha (mul_pos hx0 hy0)).le
  have hz : 0 < 1/2-x-y := by
    have hb : b < 1/4 := by norm_num [b,truncatedSixthLowerBeta]
    linarith [hxy.trans hy]
  rw [FifthActualIntegralRecovery.log_literal hx hxy hy,kernel_identity]
  convert! hh using 1 <;>
    simp only [truncatedSixthLowerS,truncatedSixthLowerC,sub_zero,a] <;>
    field_simp [ha.ne',hx0.ne',hy0.ne',hz.ne']

theorem endpoint_lower :
    endpoint p0 p1 p2 p3 p4 ≤ Wu08TerminalAlignment.fifthMain := by
  have h := endpoint_comparison p0 p1 p2 p3 p4
    (fun _ _ hx hxy hy => original_kernel_lower hx hxy hy)
  have hd := FifthActualIntegralRecovery.integral_distance.1
  change _ ≤ fifthPairFlin
  linarith only [h,hd]

theorem endpoint_collected :
    endpoint p0 p1 p2 p3 p4 =
      2*p0*(log b-log a)^2+logCoefficient*(log b-log a)+constantCoefficient := by
  unfold endpoint WuTarget.FifthClassicalClosure.quadraticEndpoint primitive3 primitive4
    logCoefficient constantCoefficient
  ring

theorem rational_lower :
    rationalLower ≤ Wu08TerminalAlignment.fifthMain := by
  have hl := TableBounds.logLower_le (by
    norm_num [a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta] :
      (1:ℝ) ≤ b/a)
  have ha := truncatedSixthLower_parameters.1
  have hb := ha.trans truncatedSixthLower_parameters.2.1
  rw [log_div hb.ne' ha.ne'] at hl
  have hs : 0 ≤ p0 ∧ 0 ≤ logCoefficient ∧ 0 ≤ TableBounds.logLower (b/a) := by
    norm_num [p0,p1,p2,p3,p4,logCoefficient,offset,center,linear,quadratic,cubic,quartic,
      a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,TableBounds.logLower,
      Finset.sum_range_succ]
  have hq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.2.2 hl 2)
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hs.1)
  have hlin := mul_le_mul_of_nonneg_left hl hs.2.1
  have h := endpoint_lower
  rw [endpoint_collected] at h
  unfold rationalLower
  linarith only [hq,hlin,h]

theorem fifth_main_lower :
    (1654752/1000000:ℝ) ≤ Wu08TerminalAlignment.fifthMain := by
  apply le_trans _ rational_lower
  norm_num [rationalLower,p0,p1,p2,p3,p4,logCoefficient,constantCoefficient,
    offset,center,linear,quadratic,cubic,quartic,a,b,truncatedSixthLowerAlpha,
    truncatedSixthLowerBeta,TableBounds.logLower,Finset.sum_range_succ]

theorem fifth_actual_lower {ε : ℝ} (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((1654752/1000000:ℝ)-ε)*truncatedSixthMassScale N ≤ (fifthPairCount N : ℝ) := by
  obtain ⟨T,hT,h⟩ := fifthPair_actual_lower he
  refine ⟨T,hT,fun N hN hEven => ?_⟩
  apply (mul_le_mul_of_nonneg_right (sub_le_sub_right fifth_main_lower ε)
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))).trans
  convert! h N hN hEven using 1
  unfold truncatedSixthMassScale Wu08TerminalAlignment.fifthMain
  ring

end Wu18938Campaign.M3.Confirmed.FifthClassical
