import RemainingHfDensity
namespace RemainingHf
open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension FirstFeedbackIntegrals
open SharpLogRecurrence FirstErrorFullPayment
open scoped Interval BigOperators
noncomputable section

def signed (c x : ℝ) : ℝ := if 0 ≤ c then c*splitLower x else c*splitUpper x

theorem signed_le (c : ℝ) {x : ℝ} (hx : 1 ≤ x) : signed c x ≤ c*log x := by
  by_cases hc : 0 ≤ c
  · simpa [signed,hc] using mul_le_mul_of_nonneg_left (splitLower_le hx) hc
  · simpa [signed,hc] using mul_le_mul_of_nonpos_left (le_splitUpper hx) (le_of_not_ge hc)

def paidCell (S a b : ℝ) : ℝ :=
  let d := cellScale S b*2/(21*(S-1))
  signed (ea S+d*qa S) (b/a)+signed (d*qb S) ((b+1)/(a+1))+
  signed (eb S+d*qc S) ((b+S)/(a+S))+d*(b-a)-
  (ec S+d*qd S)*(1/(b+S)-1/(a+S))-
  (ed S+d*qe S)/2*(1/(b+S)^2-1/(a+S)^2)+
  residualPrimitive S b b-residualPrimitive S b a

theorem paidCell_le_primitive {S a b : ℝ} (hS : 3 ≤ S) (ha : 0 < a) (hab : a ≤ b) :
    paidCell S a b ≤ ePrimitive S b-ePrimitive S a+
      cellScale S b*(errorPrimitive S b-errorPrimitive S a)+
      residualPrimitive S b b-residualPrimitive S b a := by
  have hb : 0 < b := ha.trans_le hab
  have ha1 : 0 < a+1 := by linarith
  have hb1 : 0 < b+1 := by linarith
  have has : 0 < a+S := by linarith
  have hbs : 0 < b+S := by linarith
  have h0 := signed_le (ea S+cellScale S b*2/(21*(S-1))*qa S)
    ((one_le_div ha).mpr hab)
  have h1 := signed_le (cellScale S b*2/(21*(S-1))*qb S)
    ((one_le_div ha1).mpr (by linarith : a+1 ≤ b+1))
  have h2 := signed_le (eb S+cellScale S b*2/(21*(S-1))*qc S)
    ((one_le_div has).mpr (by linarith : a+S ≤ b+S))
  rw [log_div hb.ne' ha.ne'] at h0
  rw [log_div hb1.ne' ha1.ne'] at h1
  rw [log_div hbs.ne' has.ne'] at h2
  dsimp [paidCell,ePrimitive,errorPrimitive]
  simp only [div_eq_mul_inv,mul_inv_rev] at h0 h1 h2 ⊢
  ring_nf at h0 h1 h2 ⊢
  linarith only [h0,h1,h2]

theorem paidCell_paid {S a b : ℝ} (hS : 3 ≤ S) (ha : S-2 ≤ a) (hab : a ≤ b) :
    paidCell S a b ≤ ∫ t in a..b,log ((t+1)/(S-1))/t := by
  have ha0 : 0 < a := by linarith
  have hi := lower_e_integrable hS ha0 hab
  have hj : IntervalIntegrable (errorDensity S) volume a b :=
    (errorDensity_continuous hS ha0 hab).intervalIntegrable
  have hk : Continuous (residualDensity S b) := by unfold residualDensity; fun_prop
  have he : (∫ t in a..b,lowerLog ((t+1)/(S-1))/t+cellScale S b*errorDensity S t+
      residualDensity S b t) = ePrimitive S b-ePrimitive S a+
      cellScale S b*(errorPrimitive S b-errorPrimitive S a)+
      residualPrimitive S b b-residualPrimitive S b a := by
    rw [intervalIntegral.integral_add (hi.add (hj.const_mul _)) (hk.intervalIntegrable a b),
      intervalIntegral.integral_add hi (hj.const_mul _),intervalIntegral.integral_const_mul,
      error_integral hS ha0 hab]
    have hl : (∫ t in a..b,lowerLog ((t+1)/(S-1))/t)=ePrimitive S b-ePrimitive S a := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro t ht
        rw [uIcc_of_le hab] at ht
        exact ePrimitive_deriv hS (ha0.trans_le ht.1)
      · exact hi
    rw [hl,intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => residualPrimitive_deriv S b t) (hk.intervalIntegrable a b)]
    ring
  refine ((paidCell_le_primitive hS ha0 hab).trans_eq he.symm).trans ?_
  apply intervalIntegral.integral_mono_on hab ((hi.add (hj.const_mul _)).add (hk.intervalIntegrable a b))
  · apply ContinuousOn.intervalIntegrable_of_Icc (h := hab)
    intro t ht
    have ht0 : 0 < t := ha0.trans_le ht.1
    have hs0 : 0 < S-1 := by linarith
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  · intro t ht
    exact paidDensity_le hS (ha.trans ht.1) ht.2

end
end RemainingHf
