import CoupledHGatePayment

namespace CoupledHGateRecovery
open Real Set MeasureTheory Wu2008DoubleSieve MotherPair NodeExtension ActualNineFeedback
open GatedDensityPayment FiniteEndpointPayment
open scoped Interval BigOperators
noncomputable section

theorem density_integral_four {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (a b : ℝ) :
    (∫ v in a..b,SecondFunctionalCoupledFeedback.density p v)=
      (∫ v in a..b,feedbackLogKernel p .gammaFive v)+
      (∫ v in a..b,feedbackLogKernel p .gammaSix v)+
      (∫ v in a..b,feedbackLogKernel p .gammaSeven v)+
      (∫ v in a..b,feedbackLogKernel p .gammaEight v) := by
  have h5 := (feedback_log_integrable hp .gammaFive).intervalIntegrable (a := a) (b := b)
  have h6 := (feedback_log_integrable hp .gammaSix).intervalIntegrable (a := a) (b := b)
  have h7 := (feedback_log_integrable hp .gammaSeven).intervalIntegrable (a := a) (b := b)
  have h8 := (feedback_log_integrable hp .gammaEight).intervalIntegrable (a := a) (b := b)
  simp only [SecondFunctionalCoupledFeedback.density,
    intervalIntegral.integral_add (h5.add h6 |>.add h7) h8,
    intervalIntegral.integral_add (h5.add h6) h7,intervalIntegral.integral_add h5 h6]

/-- The previously zero first gamma-eight endpoint is replaced, not counted twice. -/
theorem first_segment_add_gate {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (ha : 1≤gateStart p) (hab : gateStart p≤upperSwitch p) (hb : upperSwitch p≤3)
    (hs : upperSwitch p≤lowerSwitch p)
    (hz : kernelEndpoint p .gammaEight 1 (upperSwitch p)=0) :
    (upperSwitch p-1)*densityEndpoint p 1 (upperSwitch p)+gatePayment p≤
      ∫ v in (1:ℝ)..(upperSwitch p),SecondFunctionalCoupledFeedback.density p v := by
  have h8 := gatePayment_le_actual hp ha hab hb hs
  have h8more := intervalIntegral.integral_mono_interval ha hab le_rfl
    (Filter.Eventually.of_forall (fun v => feedback_log_nonnegative hp .gammaEight v))
    ((feedback_log_integrable hp .gammaEight).intervalIntegrable
      (a := (1:ℝ)) (b := upperSwitch p))
  have h5 := kernelEndpoint_integral_le hp .gammaFive le_rfl (ha.trans hab) hb
  have h6 := kernelEndpoint_integral_le hp .gammaSix le_rfl (ha.trans hab) hb
  have h7 := kernelEndpoint_integral_le hp .gammaSeven le_rfl (ha.trans hab) hb
  rw [density_integral_four hp]
  unfold densityEndpoint
  rw [hz]
  linarith only [h5,h6,h7,h8.trans h8more]

/-- All three old subintervals remain; only the lost true first-branch mass is added. -/
theorem first_cell_add_gate {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (ha : 1≤gateStart p) (hab : gateStart p≤upperSwitch p) (hb : upperSwitch p≤3)
    (hs : upperSwitch p≤lowerSwitch p)
    (hz : kernelEndpoint p .gammaEight 1 (upperSwitch p)=0)
    (hfirst : firstSplit p 1 (upperNode 0)=upperSwitch p) :
    intervalPayment p 1 (upperNode 0)+gatePayment p≤
      ∫ v in (1:ℝ)..(upperNode 0),SecondFunctionalCoupledFeedback.density p v := by
  have hn : (1:ℝ)≤upperNode 0 := by norm_num [upperNode]
  have hn3 : upperNode 0≤(3:ℝ) := by norm_num [upperNode]
  have ho := split_order p hn
  rw [hfirst] at ho
  have h0 := first_segment_add_gate hp ha hab hb hs hz
  have h1 := densityEndpoint_integral_le hp ho.1 ho.2.1 (ho.2.2.trans hn3)
  have h2 := densityEndpoint_integral_le hp (ho.1.trans ho.2.1) ho.2.2 hn3
  have hi := density_integrable p hp
  have he0 := intervalIntegral.integral_add_adjacent_intervals
    (a := (1:ℝ)) (b := upperSwitch p) (c := secondSplit p 1 (upperNode 0))
    hi.intervalIntegrable hi.intervalIntegrable
  have he1 := intervalIntegral.integral_add_adjacent_intervals
    (a := (1:ℝ)) (b := secondSplit p 1 (upperNode 0)) (c := upperNode 0)
    hi.intervalIntegrable hi.intervalIntegrable
  unfold intervalPayment
  rw [hfirst]
  linarith only [h0,h1,h2,he0,he1]

end
end CoupledHGateRecovery
