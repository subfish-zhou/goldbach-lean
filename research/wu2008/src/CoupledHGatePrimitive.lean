import CoupledFullyFinite

namespace CoupledHGateRecovery
open Real Set MeasureTheory Wu2008DoubleSieve MotherPair
open GatedDensityPayment
open scoped Interval
noncomputable section

/-- The actual gamma-eight gate meeting, forced by L = U. -/
def gateStart (p : SecondFunctionalParameters) : ℝ := p.kappa1*(1-1/p.kappa2)-1

/-- A full-cross-ratio lower density, on the first actual open branch. -/
def gateKernel (p : SecondFunctionalParameters) (v : ℝ) : ℝ :=
  p.kappa2*(v-gateStart p)/(v*(v+1))

/-- The primitive of the restored gate density, with no endpoint box. -/
def gatePrimitive (p : SecondFunctionalParameters) (v : ℝ) : ℝ :=
  p.kappa2*((gateStart p+1)*log (v+1)-gateStart p*log v)

theorem gateKernel_deriv (p : SecondFunctionalParameters) {v : ℝ} (hv : 0<v) :
    HasDerivAt (gatePrimitive p) (gateKernel p v) v := by
  have hv1 : v+1≠0 := by linarith
  have h := ((((hasDerivAt_id v).add_const 1).log hv1).const_mul (gateStart p+1)).sub
    ((hasDerivAt_log hv.ne').const_mul (gateStart p))
  convert h.const_mul p.kappa2 using 1 <;> first | rfl | skip
  unfold gateKernel
  simp only [id_eq]
  field_simp
  ring

theorem gateKernel_continuous (p : SecondFunctionalParameters) {a b : ℝ}
    (ha : 0<a) (hab : a≤b) : ContinuousOn (gateKernel p) (uIcc a b) := by
  rw [uIcc_of_le hab]
  intro v hv
  have h0 : v≠0 := ne_of_gt (ha.trans_le hv.1)
  have h1 : v+1≠0 := by linarith [hv.1]
  have hmul : v*(v+1)≠0 := mul_ne_zero h0 h1
  apply ContinuousAt.continuousWithinAt
  unfold gateKernel
  fun_prop (disch := assumption)

theorem gateKernel_integral (p : SecondFunctionalParameters) {a b : ℝ}
    (ha : 0<a) (hab : a≤b) :
    (∫ v in a..b,gateKernel p v)=gatePrimitive p b-gatePrimitive p a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro v hv
    rw [uIcc_of_le hab] at hv
    exact gateKernel_deriv p (ha.trans_le hv.1)
  · exact (gateKernel_continuous p ha hab).intervalIntegrable

/-- Universal log bound used on the complete original cross-ratio. -/
theorem reciprocal_log_lower {x : ℝ} (hx : 0<x) : 1-1/x≤log x := by
  have h := log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [log_inv] at h
  simpa only [one_div] using (by linarith only [h] : 1-x⁻¹≤log x)

theorem branch_geometry {p : SecondFunctionalParameters}
    (hk : 2<p.kappa2) (hS : 0<p.S)
    (ha : 1≤gateStart p) (_hb : upperSwitch p≤3)
    (hs : upperSwitch p≤lowerSwitch p) {v : ℝ}
    (hv : v∈Icc (gateStart p) (upperSwitch p)) :
    feedbackLower p .gammaEight v=(1-1/p.kappa2)/(v+1) ∧
    feedbackUpper p .gammaEight v=1/p.kappa1 ∧
    0<feedbackPole p .gammaEight v ∧
    feedbackUpper p .gammaEight v<feedbackPole p .gammaEight v := by
  have hv1 : 0<v+1 := by linarith [hv.1]
  have hv2 : 0<v+2 := by linarith [hv.1]
  have hk1 : 0<p.kappa1 := by unfold upperSwitch at hv; linarith [hv.1,hv.2]
  have hk2 : 0<p.kappa2 := by linarith
  have hhalf : (1:ℝ)/2≤1-1/p.kappa2 := by
    have h : 1/p.kappa2≤(1:ℝ)/2 := (div_le_iff₀ hk2).mpr (by linarith)
    linarith
  have hlow : 1/p.S≤(1-1/p.kappa2)/(v+1) := by
    apply (div_le_div_iff₀ hS hv1).mpr
    have h := hv.2.trans hs
    unfold lowerSwitch at h
    linarith
  have hh : 1/(2*(v+1))≤(1-1/p.kappa2)/(v+1) := by
    have h := div_le_div_of_nonneg_right hhalf hv1.le
    simpa only [div_div] using h
  have hu1 : 1/p.kappa1≤(1-1/p.kappa1)/(v+1) := by
    apply (div_le_div_iff₀ hk1 hv1).mpr
    have he : (1-1/p.kappa1)*p.kappa1=p.kappa1-1 := by field_simp
    rw [he]
    unfold upperSwitch at hv
    linarith [hv.2]
  have hu2 : 1/p.kappa1≤1/(v+2) := by
    apply one_div_le_one_div_of_le hv2
    unfold upperSwitch at hv
    linarith [hv.2]
  have hup : 1/p.kappa1<1/(v+1) := by
    apply one_div_lt_one_div_of_lt hv1
    unfold upperSwitch at hv
    linarith [hv.2]
  simp only [feedbackLower,feedbackUpper,feedbackPole,upperP,upperQ,lowerQ]
  exact ⟨by rw [max_eq_left hh,max_eq_right hlow],
    by rw [min_eq_left (le_min hu1 hu2)],
    one_div_pos.mpr hv1,(min_le_left _ _).trans_lt hup⟩

end
end CoupledHGateRecovery
