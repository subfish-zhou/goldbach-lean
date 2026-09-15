import MathlibNt.Wu2008DoubleSieve.GVariableIntegral

namespace Wu2008DoubleSieve.GVariableQuadratic
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence
open FixedCoefficientScalarEnclosure FixedCoefficientUpperEnclosure FixedCoefficientHLowerEnclosure
open GVariableIntegral
open scoped Interval

noncomputable def quadraticPrimitive (t : ℝ) : ℝ :=
  (2*s^2/(9*a^2))*log t-2*log (1/2-t)-t/(9*a^2)

/-- Exact gain primitive for the third low segment of each original G. -/
theorem quadratic_derivative {t : ℝ} (ht : 0 < t) (ht1 : t < 1/2) :
    HasDerivAt quadraticPrimitive ((((1/2-t)/a-3)^2/9)/(t*(1/2-t))) t := by
  have ha := truncatedSixthLower_parameters.1.ne'
  have hn : 1/2-t ≠ 0 := by linarith
  have hn2 : 1-t*2 ≠ 0 := by linarith
  have hh := (((hasDerivAt_log ht.ne').const_mul (2*s^2/(9*a^2))).sub
    ((((hasDerivAt_const t (1/2 : ℝ)).sub (hasDerivAt_id t)).log hn).const_mul 2)).sub
    ((hasDerivAt_id t).div_const (9*a^2))
  convert hh using 1 <;> first | rfl |
    (dsimp [s,truncatedSixthLowerSigma]; field_simp [ha,ht.ne',hn2]; ring_nf; field_simp [hn2]; ring)

theorem quadratic_segment :
    reciprocalPrimitive s-reciprocalPrimitive (c 4)+
      quadraticPrimitive s-quadraticPrimitive (c 4) ≤
      ∫ t in c 4..s, ClassicalSingleBounds.g t := by
  have hl : a ≤ c 4 := by norm_num [c,a,truncatedSixthLowerAlpha]
  have hlr : c 4 ≤ s := by norm_num [c,s,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
  have hs3 := truncatedSixthLower_parameters.2.2.2.1.le
  have ha := truncatedSixthLower_parameters.1
  have hl0 := ha.trans_le hl
  have hi : IntervalIntegrable
      (fun t : ℝ => (1+((1/2-t)/a-3)^2/9)/(t*(1/2-t))) volume (c 4) s := by
    apply ContinuousOn.intervalIntegrable
    exact (by fun_prop : ContinuousOn (fun t : ℝ => 1+((1/2-t)/a-3)^2/9) _).div
      (by fun_prop) (fun t ht => by
        rw [uIcc_of_le hlr] at ht
        exact mul_ne_zero (hl0.trans_le ht.1).ne' (by linarith [ht.2]))
  have hm := intervalIntegral.integral_mono_on hlr hi
    (ClassicalSingleBounds.g_integrable hl hs3 hlr) (fun t ht => by
      have ht0 := hl0.trans_le ht.1
      have hd : 0 < 1/2-t := by linarith [ht.2]
      have hu3 : 3 ≤ (1/2-t)/a := (le_div_iff₀ ha).2 (by
        have hs : s=1/2-3*a := rfl
        rw [hs] at ht
        linarith [ht.2])
      have hu4 : (1/2-t)/a ≤ 4 := (div_le_iff₀ ha).2 (by dsimp [c] at ht; linarith [ht.1])
      exact div_le_div_of_nonneg_right (SharpSingleBalance.upper_quadratic hu3 hu4)
        (mul_pos ht0 hd).le)
  have hd (t : ℝ) (ht : t ∈ uIcc (c 4) s) :
      HasDerivAt (fun t => reciprocalPrimitive t+quadraticPrimitive t)
        ((1+((1/2-t)/a-3)^2/9)/(t*(1/2-t))) t := by
    rw [uIcc_of_le hlr] at ht
    have ht0 := hl0.trans_le ht.1
    have ht1 : t < 1/2 := by linarith [ht.2]
    convert (reciprocal_derivative ht0 ht1).add (quadratic_derivative ht0 ht1) using 1 <;>
      first | rfl | ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi] at hm
  linarith

noncomputable def quadraticPayment : ℝ :=
  (2*s^2/(9*a^2))*lowerLog (s/c 4)+2*lowerLog ((1/2-c 4)/(1/2-s))-(s-c 4)/(9*a^2)

theorem quadratic_payment_lower :
    quadraticPayment ≤ quadraticPrimitive s-quadraticPrimitive (c 4) := by
  have hl : 0 < c 4 := by norm_num [c,a,truncatedSixthLowerAlpha]
  have hr : 0 < s := by norm_num [s,truncatedSixthLowerSigma,truncatedSixthLowerAlpha]
  have hd1 : 0 < 1/2-c 4 := by norm_num [c,a,truncatedSixthLowerAlpha]
  have hd2 : 0 < 1/2-s := by norm_num [s,truncatedSixthLowerSigma,truncatedSixthLowerAlpha]
  have hq1 : 1 ≤ s/c 4 := by norm_num [c,s,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
  have hq2 : 1 ≤ (1/2-c 4)/(1/2-s) := by
    norm_num [c,s,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
  have h1 := log_lower hq1
  have h2 := log_lower hq2
  rw [log_div hr.ne' hl.ne'] at h1
  rw [log_div hd1.ne' hd2.ne'] at h2
  have hp : 0 ≤ 2*s^2/(9*a^2) := by positivity
  have hm := mul_le_mul_of_nonneg_left h1 hp
  dsimp [quadraticPayment,quadraticPrimitive]
  rw [sub_div s (c 4)]
  nlinarith only [hm,h2]

#print axioms quadratic_segment
#print axioms quadratic_payment_lower
end Wu2008DoubleSieve.GVariableQuadratic
