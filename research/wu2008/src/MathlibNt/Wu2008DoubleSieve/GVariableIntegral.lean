import MathlibNt.Wu2008DoubleSieve.GVariableRecurrence

namespace Wu2008DoubleSieve.GVariableIntegral
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence
open FixedCoefficientScalarEnclosure FixedCoefficientUpperEnclosure FixedCoefficientHLowerEnclosure
open GVariableRecurrence
open scoped Interval

noncomputable def affinePrimitive (j t : ℝ) : ℝ :=
  (2*c j/a)*log t+2*j*log (1/2-t)

/-- Exact primitive of the variable gain, with both original denominators retained. -/
theorem affine_derivative {j t : ℝ} (ht : 0 < t) (ht1 : t < 1/2) :
    HasDerivAt (affinePrimitive j) (((1/2-t)/a-j)/(t*(1/2-t))) t := by
  have ha := truncatedSixthLower_parameters.1.ne'
  have hn : 1/2-t ≠ 0 := by linarith
  have hn2 : 1-t*2 ≠ 0 := by linarith
  have hh := ((hasDerivAt_log ht.ne').const_mul (2*c j/a)).add
    ((((hasDerivAt_const t (1/2 : ℝ)).sub (hasDerivAt_id t)).log hn).const_mul (2*j))
  convert hh using 1 <;> first | rfl | (dsimp [c]; field_simp [ha,ht.ne',hn2]; ring_nf; field_simp [hn2]; ring)

theorem reciprocal_derivative {t : ℝ} (ht : 0 < t) (ht1 : t < 1/2) :
    HasDerivAt reciprocalPrimitive (1/(t*(1/2-t))) t := by
  have hn : 1/2-t ≠ 0 := by linarith
  have hn2 : 1-t*2 ≠ 0 := by linarith
  have hh := ((hasDerivAt_log ht.ne').sub
    (((hasDerivAt_const t (1/2 : ℝ)).sub (hasDerivAt_id t)).log hn)).const_mul 2
  convert hh using 1 <;> first | rfl | (dsimp; field_simp [hn2]; ring)

theorem affine_segment {j C d l r : ℝ}
    (hA : ∀ u : ℝ, j ≤ u → C+d*(u-j) ≤ wuUpperCoefficient u)
    (hl : a ≤ l) (hr : r ≤ c j) (hr3 : r ≤ 1/3) (hlr : l ≤ r) :
    C*(reciprocalPrimitive r-reciprocalPrimitive l)+
      d*(affinePrimitive j r-affinePrimitive j l) ≤
      ∫ t in l..r, ClassicalSingleBounds.g t := by
  have ha := truncatedSixthLower_parameters.1
  have hl0 := ha.trans_le hl
  have hi : IntervalIntegrable
      (fun t : ℝ => (C+d*((1/2-t)/a-j))/(t*(1/2-t))) volume l r := by
    apply ContinuousOn.intervalIntegrable
    exact (by fun_prop : ContinuousOn (fun t : ℝ => C+d*((1/2-t)/a-j)) _).div
      (by fun_prop) (fun t ht => by
        rw [uIcc_of_le hlr] at ht
        exact mul_ne_zero (hl0.trans_le ht.1).ne' (by linarith [ht.2]))
  have hm := intervalIntegral.integral_mono_on hlr hi
    (ClassicalSingleBounds.g_integrable hl hr3 hlr) (fun t ht => by
      have ht0 := hl0.trans_le ht.1
      have hd : 0 < 1/2-t := by linarith [ht.2]
      have hju : j ≤ (1/2-t)/a := (le_div_iff₀ ha).2 (by dsimp [c] at hr; linarith [ht.2])
      exact div_le_div_of_nonneg_right (hA _ hju) (mul_pos ht0 hd).le)
  have hd (t : ℝ) (ht : t ∈ uIcc l r) :
      HasDerivAt (fun t => C*reciprocalPrimitive t+d*affinePrimitive j t)
        ((C+d*((1/2-t)/a-j))/(t*(1/2-t))) t := by
    rw [uIcc_of_le hlr] at ht
    have ht0 := hl0.trans_le ht.1
    have ht1 : t < 1/2 := by linarith [ht.2]
    convert ((reciprocal_derivative ht0 ht1).const_mul C).add
      ((affine_derivative (j := j) ht0 ht1).const_mul d) using 1 <;>
      first | rfl | ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi] at hm
  linarith

noncomputable def affinePayment (j l r : ℝ) : ℝ :=
  (2*c j/a)*lowerLog (r/l)-2*j*upperLog ((1/2-l)/(1/2-r))

theorem affine_payment_lower {j l r : ℝ} (hj : 0 ≤ j)
    (hl : 0 < l) (hlr : l ≤ r) (hr : r < 1/2) (hjc : 0 ≤ c j) :
    affinePayment j l r ≤ affinePrimitive j r-affinePrimitive j l := by
  have hr0 := hl.trans_le hlr
  have hld : 0 < 1/2-l := by linarith
  have hrd : 0 < 1/2-r := by linarith
  have hq1 : 1 ≤ r/l := (le_div_iff₀ hl).2 (by linarith)
  have hq2 : 1 ≤ (1/2-l)/(1/2-r) := (le_div_iff₀ hrd).2 (by linarith)
  have h1 := log_lower hq1
  have h2 := log_upper hq2
  rw [log_div hr0.ne' hl.ne'] at h1
  rw [log_div hld.ne' hrd.ne'] at h2
  have hp : 0 ≤ 2*c j/a := div_nonneg (by positivity) truncatedSixthLower_parameters.1.le
  have hm1 := mul_le_mul_of_nonneg_left h1 hp
  have hm2 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 2*j by positivity)
  dsimp [affinePayment,affinePrimitive]
  nlinarith only [hm1,hm2]

#print axioms affine_segment
#print axioms affine_payment_lower
end Wu2008DoubleSieve.GVariableIntegral
