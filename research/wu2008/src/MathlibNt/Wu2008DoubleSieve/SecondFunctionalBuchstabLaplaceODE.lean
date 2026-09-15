import MathlibNt.Wu2008DoubleSieve.SecondFunctionalBuchstabLaplaceMoment

/-! Closed ODE and Euler normalization of the literal Buchstab Laplace transform.
No Abelian or Tauberian assertion about pointwise Buchstab limits is made here. -/
namespace Wu2008DoubleSieve.SecondFunctionalJointTail
open Set Filter MeasureTheory Real
open scoped Topology

/-- The true transform satisfies the closed first-order ODE on the positive ray. -/
theorem buchstabLaplace_hasDerivAt_closed {z : ℝ} (hz : 0 < z) :
    HasDerivAt buchstabLaplace (-(exp (-z) * (1 + buchstabLaplace z) / z)) z := by
  have hm := buchstabLaplace_moment_identity hz
  convert! buchstabLaplace_hasDerivAt hz using 1
  apply congrArg Neg.neg
  exact ((eq_div_iff (ne_of_gt hz)).mpr (by simpa only [mul_comm] using hm)).symm

/-- The logarithmic normalization has exactly zero derivative, using the actual moment. -/
theorem buchstabLaplace_log_sub_hasDerivAt {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z : ℝ => log (1 + buchstabLaplace z) - buchstabE1 z) 0 z := by
  have hp : 0 < 1 + buchstabLaplace z := by linarith [buchstabLaplace_nonneg z]
  have hd := (((buchstabLaplace_hasDerivAt_closed hz).const_add 1).log
    (ne_of_gt hp)).sub (buchstabE1_hasDerivAt hz)
  convert! hd using 1
  field_simp
  ring

/-- The large-parameter boundary fixes the otherwise free integration constant. -/
theorem buchstabLaplace_log_eq_E1 {z : ℝ} (hz : 0 < z) :
    log (1 + buchstabLaplace z) = buchstabE1 z := by
  let g : ℝ → ℝ := fun z => log (1 + buchstabLaplace z) - buchstabE1 z
  have hc : ∀ w : ℝ, 0 < w → g w = g z := by
    intro w hw
    exact isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi (0 : ℝ)).isPreconnected
      (fun x hx => (buchstabLaplace_log_sub_hasDerivAt hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (buchstabLaplace_log_sub_hasDerivAt hx).deriv) hw hz
  have hlim : Tendsto g atTop (𝓝 0) := by
    have hone : Tendsto (fun z => 1 + buchstabLaplace z) atTop (𝓝 (1 : ℝ)) := by
      simpa only [add_zero] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).add
          buchstabLaplace_tendsto_atTop)
    have hlog := ((continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto).comp hone
    have hh := hlog.sub buchstabE1_tendsto_atTop
    simpa only [g, Function.comp_def, log_one, sub_zero] using hh
  have he : g =ᶠ[atTop] fun _ => g z := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
    exact hc w hw
  have hzero : g z = 0 := tendsto_nhds_unique tendsto_const_nhds (hlim.congr' he)
  exact sub_eq_zero.mp hzero

/-- Identification of the original transform, not a separately defined ODE solution. -/
theorem buchstabLaplace_one_add_eq_exp_E1 {z : ℝ} (hz : 0 < z) :
    1 + buchstabLaplace z = exp (buchstabE1 z) := by
  rw [← buchstabLaplace_log_eq_E1 hz, exp_log]
  linarith [buchstabLaplace_nonneg z]

/-- Euler normalization for the actual scaled Laplace transform. -/
theorem buchstabLaplace_scaled_tendsto :
    Tendsto (fun z : ℝ => z * buchstabLaplace z) (𝓝[>] 0)
      (𝓝 (exp (-eulerMascheroniConstant))) := by
  have hz : Tendsto (fun z : ℝ => z) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have h := buchstabE1_scaled_exp_tendsto.sub hz
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [← buchstabLaplace_one_add_eq_exp_E1 hz]
  ring

end Wu2008DoubleSieve.SecondFunctionalJointTail
