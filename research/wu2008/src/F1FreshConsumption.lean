import F1FreshAOne
import F1FreshATwo
import F1FreshBOne
import F1FreshBTwo

noncomputable section
open Real Set MeasureTheory FirstCRationalPayment F1BFullFTC
open scoped Interval
namespace F1FreshFTC

theorem residual_first {x : ℝ} (hx : 0 < x) :
    F1LowerResidual.payment ((1+x)/2) =
      (x-1)^7*(5*x+19)/(210*(x+1)^2*(x+3)^4*(x^2+18*x+21)) := by
  unfold F1LowerResidual.payment F1LowerResidual.denom
  field_simp
  ring

theorem residual_second {x : ℝ} (hx : 0 < x) :
    F1LowerResidual.payment (2*x/(1+x)) =
      (x-1)^7*(17*x+7)/(840*x^2*(3*x+1)^4*(21*x^2+18*x+1)) := by
  unfold F1LowerResidual.payment F1LowerResidual.denom
  field_simp
  ring

theorem freshA_exact {u : ℝ} (hu : 2 ≤ u) :
    freshA u = AOne.kernel u+ATwo.kernel u := by
  have hu0 : 0 < u := by linarith
  have hum : 0 < u-1 := by linarith
  have ht : 0 < 3*u-2 := by linarith
  have hq : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
  unfold freshA splitFresh
  rw [residual_first hum,residual_second hum]
  unfold linearB AOne.kernel ATwo.kernel
  have hv : 0 ≤ u-2 := by linarith
  generalize he : u-2=v at hv
  have hu_eq : u=v+2 := by linarith
  rw [hu_eq]
  ring_nf
  field_simp
  ring

theorem scaled_first {k v : ℝ} (hk : 0 < k) (hv : 0 < v) :
    F1LowerResidual.payment ((1+k/v)/2) =
      (k-v)^7*(5*k+19*v)/(210*(k+v)^2*(k+3*v)^4*(k^2+18*k*v+21*v^2)) := by
  rw [residual_first (div_pos hk hv)]
  field_simp

theorem scaled_second {k v : ℝ} (hk : 0 < k) (hv : 0 < v) :
    F1LowerResidual.payment (2*(k/v)/(1+k/v)) =
      (k-v)^7*(17*k+7*v)/(840*k^2*(3*k+v)^4*(21*k^2+18*k*v+v^2)) := by
  rw [residual_second (div_pos hk hv)]
  field_simp

theorem freshB_exact {u : ℝ} (hu : 2 ≤ u) :
    freshB u = BOne.kernel u+BTwo.kernel u := by
  have hu0 : 0 < u := by linarith
  have hup : 0 < u+1 := by linarith
  have ht : 0 < 3*u-2 := by linarith
  have hr : 0 < ((1327:ℝ)/200-1)/(u+1) := by positivity
  unfold freshB splitFresh
  rw [scaled_first (by norm_num) hup,scaled_second (by norm_num) hup]
  have hl : linearA u/u=8*(u-2)/((u+2)*(3*u-2)) := by
    have hp : 0 < u+2 := by linarith
    unfold linearA
    generalize hpa : u+2=a at *
    generalize hpb : 3*u-2=b at *
    field_simp [hu0.ne',hp.ne',ht.ne']
    rw [← hpa,← hpb]
    ring
  rw [hl,mul_add]
  have hn : (1327:ℝ)/200-1-(u+1)=927/200-u := by ring
  have h1 : (1327:ℝ)/200-1+(u+1)=u+1327/200 := by ring
  have h3 : (1327:ℝ)/200-1+3*(u+1)=3*(u+1727/600) := by ring
  have h4 : 3*((1327:ℝ)/200-1)+(u+1)=u+3581/200 := by ring
  have hq1 : ((1327:ℝ)/200-1)^2+18*((1327:ℝ)/200-1)*(u+1)+21*(u+1)^2=
      F1BFullFTC.quadOne u := by unfold F1BFullFTC.quadOne; ring
  have hq2 : 21*((1327:ℝ)/200-1)^2+18*((1327:ℝ)/200-1)*(u+1)+(u+1)^2=
      F1BFullFTC.quadTwo u := by unfold F1BFullFTC.quadTwo; ring
  rw [hn,h1,h3,h4,hq1,hq2]
  apply congrArg₂ (·+·)
  · unfold BOne.kernel
    rw [show 3*u-2=3*(u-2/3) by ring]
    simp only [sub_neg_eq_add,pow_one,mul_pow,div_eq_mul_inv,mul_inv_rev]
    ring
  · unfold BTwo.kernel
    rw [show 3*u-2=3*(u-2/3) by ring]
    simp only [sub_neg_eq_add,pow_one,div_eq_mul_inv,mul_inv_rev]
    ring

theorem massA_exact : F1FreshMass.massA = AOne.mass+ATwo.mass := by
  unfold F1FreshMass.massA
  have h := intervalIntegral.integral_congr (μ := volume)
    (a := (2:ℝ)) (b := (927/200)) (fun u hu => freshA_exact (u := u) (by
      rw [uIcc_of_le (by norm_num : (2:ℝ) ≤ 927/200)] at hu
      exact hu.1))
  rw [intervalIntegral.integral_add
    (AOne.kernel_continuousOn.intervalIntegrable_of_Icc (by norm_num))
    (ATwo.kernel_continuousOn.intervalIntegrable_of_Icc (by norm_num)),
    AOne.integral_exact,ATwo.integral_exact] at h
  exact h

theorem massB_exact : F1FreshMass.massB = BOne.mass+BTwo.mass := by
  unfold F1FreshMass.massB
  have h := intervalIntegral.integral_congr (μ := volume)
    (a := (2:ℝ)) (b := (927/200)) (fun u hu => freshB_exact (u := u) (by
      rw [uIcc_of_le (by norm_num : (2:ℝ) ≤ 927/200)] at hu
      exact hu.1))
  rw [intervalIntegral.integral_add
    (BOne.kernel_continuousOn.intervalIntegrable_of_Icc (by norm_num))
    (BTwo.kernel_continuousOn.intervalIntegrable_of_Icc (by norm_num)),
    BOne.integral_exact,BTwo.integral_exact] at h
  exact h

end F1FreshFTC
