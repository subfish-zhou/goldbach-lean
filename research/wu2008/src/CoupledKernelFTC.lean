import NineOriginalTargets

namespace CoupledIntegralRecovery
open Real Set MeasureTheory NodeExtension ActualNineFeedback Wu2008DoubleSieve
open scoped Interval
noncomputable section

/-- The exact positive primitive on the ORIGINAL J interval, with no quadrature. -/
def odds (S a x : ℝ) : ℝ := log (x/a) + log ((S-a)/(S-x))

theorem odds_derivative {S x : ℝ} (hx : 0<x) (hxS : x<S) :
    HasDerivAt (fun y : ℝ => log y-log (S-y)) (S/(x*(S-x))) x := by
  have h := (hasDerivAt_log hx.ne').sub
    (((hasDerivAt_id x).const_sub S).log (by linarith : S-x≠0))
  convert h using 1 <;> first | rfl | (dsimp; field_simp [hx.ne', show S-x≠0 by linarith]; ring)

theorem odds_integral {S a b : ℝ} (ha : 0<a) (hab : a≤b) (hb : b<S) :
    (∫ x in a..b, S/(x*(S-x))) = odds S a b := by
  have hc : ContinuousOn (fun x : ℝ => S/(x*(S-x))) (uIcc a b) := by
    apply continuousOn_const.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
    rw [uIcc_of_le hab]
    intro x hx
    change x*(S-x)≠0
    exact mul_ne_zero (by linarith [hx.1]) (by linarith [hx.2])
  have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => odds_derivative (by rw [uIcc_of_le hab] at hx; linarith [hx.1])
      (by rw [uIcc_of_le hab] at hx; linarith [hx.2])) hc.intervalIntegrable
  rw [ht]
  unfold odds
  rw [log_div (by linarith : b≠0) ha.ne',
    log_div (by linarith : S-a≠0) (by linarith : S-b≠0)]
  ring

theorem odds_nonneg {S a b : ℝ} (ha : 0<a) (hab : a≤b) (hb : b<S) :
    0≤odds S a b := by
  rw [← odds_integral ha hab hb]
  apply intervalIntegral.integral_nonneg hab
  intro x hx
  exact div_nonneg (by linarith) (mul_nonneg (by linarith [hx.1]) (by linarith [hx.2]))

/-- Fubini removes the moving inner tail without changing its complete profile. -/
theorem odds_tail {S a b : ℝ} (ha : 0<a) (hab : a≤b) (hb : b<S)
    {f : ℝ → ℝ} (hf : IntervalIntegrable f volume a b) :
    (∫ x in a..b, (∫ t in x..b, f t)*(S/(x*(S-x)))) =
      ∫ t in a..b, f t*odds S a t := by
  have hc : ContinuousOn (fun x : ℝ => S/(x*(S-x))) (uIcc a b) := by
    apply continuousOn_const.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
    rw [uIcc_of_le hab]
    intro x hx
    change x*(S-x)≠0
    exact mul_ne_zero (by linarith [hx.1]) (by linarith [hx.2])
  have hq := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp
    (hc.intervalIntegrable (μ := volume))
  have hp := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hf
  have hF : IntegrableOn (fun z : ℝ × ℝ => (S/(z.1*(S-z.1)))*f z.2)
      (Icc a b ×ˢ Icc a b) := by
    change Integrable _ ((volume.prod volume).restrict (Icc a b ×ˢ Icc a b))
    rw [← Measure.prod_restrict]
    exact hq.mul_prod hp
  calc
    _ = ∫ x in a..b, ∫ t in x..b, (S/(x*(S-x)))*f t := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [intervalIntegral.integral_const_mul]
      ring
    _ = ∫ t in a..b, ∫ x in a..t, (S/(x*(S-x)))*f t := triangle_swap hab _ hF
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hab] at ht
      dsimp only
      rw [intervalIntegral.integral_mul_const, odds_integral ha ht.1 (ht.2.trans_lt hb)]
      ring

/-- One full weighted tail, including its terminal constant, evaluated at original endpoints. -/
theorem odds_full_tail {S a b : ℝ} (ha : 0<a) (hab : a≤b) (hb : b<S)
    {f : ℝ → ℝ} (hf : IntervalIntegrable f volume a b) (c : ℝ) :
    (∫ x in a..b, (c+∫ t in x..b, f t)*(S/(x*(S-x)))) =
      c*odds S a b + ∫ t in a..b, f t*odds S a t := by
  have hc : ContinuousOn (fun x : ℝ => S/(x*(S-x))) (uIcc a b) := by
    apply continuousOn_const.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
    rw [uIcc_of_le hab]
    intro x hx
    change x*(S-x)≠0
    exact mul_ne_zero (by linarith [hx.1]) (by linarith [hx.2])
  have ht : ContinuousOn (fun x => ∫ t in x..b, f t) (uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval_left
      ((intervalIntegrable_iff' (by finiteness)).mp hf)
  have htc : IntervalIntegrable (fun x => (∫ t in x..b, f t)*(S/(x*(S-x)))) volume a b :=
    (ht.mul hc).intervalIntegrable
  simp_rw [add_mul]
  rw [intervalIntegral.integral_add (hc.intervalIntegrable.const_mul c)
    htc, intervalIntegral.integral_const_mul,
    odds_integral ha hab hb, odds_tail ha hab hb hf]

end
end CoupledIntegralRecovery
