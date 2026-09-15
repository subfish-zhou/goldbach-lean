import CoupledHGatePrimitive

namespace CoupledHGateRecovery
open Real Set MeasureTheory Wu2008DoubleSieve MotherPair
open GatedDensityPayment
open scoped Interval
noncomputable section

/-- Finite restored mass on the entire first actual open branch. -/
def gatePayment (p : SecondFunctionalParameters) : ℝ :=
  gatePrimitive p (upperSwitch p)-gatePrimitive p (gateStart p)

theorem gateKernel_le_actual {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (ha : 1≤gateStart p) (hb : upperSwitch p≤3)
    (hs : upperSwitch p≤lowerSwitch p) {v : ℝ}
    (hv : v∈Icc (gateStart p) (upperSwitch p)) :
    gateKernel p v≤feedbackLogKernel p .gammaEight v := by
  have hk : 2<p.kappa2 := lt_of_lt_of_le hp.two_lt_s
    (hp.mother.s_le_kappa3.trans hp.mother.kappa3_lt_kappa2.le)
  have hS : 0<p.S := by linarith [hp.three_le_S]
  have hg := branch_geometry hk hS ha hb hs hv
  have hv0 : 0<v := by linarith [hv.1]
  have hv1 : 0<v+1 := by linarith
  have hk1 : 0<p.kappa1 := by unfold upperSwitch at hv; linarith [hv.2]
  have hk2 : 0<p.kappa2 := by linarith
  rcases eq_or_lt_of_le hv.1 with heq | hstrict
  · have he : gateKernel p v=0 := by rw [← heq]; simp [gateKernel]
    rw [he]
    exact feedback_log_nonnegative hp .gammaEight v
  have hgate : feedbackLower p .gammaEight v<feedbackUpper p .gammaEight v := by
    rw [hg.1,hg.2.1]
    apply (div_lt_div_iff₀ hv1 hk1).mpr
    unfold gateStart at hstrict
    linarith
  have hratio := ratio_pos (lower_pos hp .gammaEight v) hgate hg.2.2.2
  have hlog := reciprocal_log_lower hratio
  rw [feedbackLogKernel,if_pos ⟨⟨ha.trans hv.1,hv.2.trans hb⟩,hgate⟩]
  change _≤feedbackFactor p .gammaEight v*log (ratio (feedbackPole p .gammaEight v)
    (feedbackLower p .gammaEight v) (feedbackUpper p .gammaEight v))
  have hh := div_le_div_of_nonneg_right hlog hv0.le
  have hkm : p.kappa2-1≠0 := by linarith
  have hden : p.kappa1-v-1≠0 := by unfold upperSwitch at hv; linarith [hv.2]
  have he : (1-1/ratio (feedbackPole p .gammaEight v)
      (feedbackLower p .gammaEight v) (feedbackUpper p .gammaEight v))/v=gateKernel p v := by
    rw [hg.1,hg.2.1]
    simp only [feedbackPole,ratio,gateKernel,gateStart]
    field_simp [hk1.ne',hk2.ne',hv0.ne',hv1.ne',hkm,hden]
    ring
  rw [he] at hh
  simpa only [feedbackFactor,one_div,mul_comm,div_eq_mul_inv,mul_one] using hh

theorem gatePayment_le_actual {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (ha : 1≤gateStart p) (hab : gateStart p≤upperSwitch p) (hb : upperSwitch p≤3)
    (hs : upperSwitch p≤lowerSwitch p) :
    gatePayment p≤∫ v in (gateStart p)..(upperSwitch p),feedbackLogKernel p .gammaEight v := by
  rw [gatePayment,← gateKernel_integral p (by linarith) hab]
  exact intervalIntegral.integral_mono_on hab
    (gateKernel_continuous p (by linarith) hab).intervalIntegrable
    (feedback_log_integrable hp .gammaEight).intervalIntegrable
    (fun v hv => gateKernel_le_actual hp ha hb hs hv)

/-- Strict positivity is proved from the original open domain, not log numerics. -/
theorem gatePayment_pos {p : SecondFunctionalParameters} (hk : 0<p.kappa2)
    (ha : 0<gateStart p) (hab : gateStart p<upperSwitch p) : 0<gatePayment p := by
  rw [gatePayment,← gateKernel_integral p ha hab.le]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    (gateKernel_continuous p ha hab.le).intervalIntegrable ?_ hab
  intro v hv
  exact div_pos (mul_pos hk (sub_pos.mpr hv.1))
    (mul_pos (ha.trans hv.1) (by linarith [hv.1]))

end
end CoupledHGateRecovery
