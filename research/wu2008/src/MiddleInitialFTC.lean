import MiddleInitialEnvelope

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open SharpLogRecurrence
open FixedCoefficientUpperEnclosure (a)
open FixedCoefficientHLowerEnclosure (c)
open Phase22 (u)
namespace MiddleInitialFTC
open MiddleInitialEnvelope

def h : ℝ := 1327/200
def W (v : ℝ) : ℝ := -8/v+16/(h-v)
def partialDensity (v : ℝ) : ℝ :=
  (12/11)*v+8942741/7640325+(299524880/916839)/v+
  (-8547286566790892748321251/2986096125885620562045000)/(h-v)+
  (-1151264258336/12882918447)/(v-1)+(136261088/3810387)/(v-1)^2+
  (-93056/10143)/(v-1)^3+
  (-1766372040448/5150827583)/(v+2)+(815308800/2982529)/(v+2)^2+
  (-3881472/1727)/(v+2)^3

theorem laurent_identity {v : ℝ} (hv : v ∈ Icc (4:ℝ) 5) :
    W v*gainDensity v = partialDensity v := by
  have h0 : v ≠ 0 := by linarith [hv.1]
  have h1 : v-1 ≠ 0 := by linarith [hv.1]
  have h2 : v+2 ≠ 0 := by linarith [hv.1]
  have hh : h-v ≠ 0 := by dsimp [h]; linarith [hv.2]
  unfold W gainDensity rationalLower oldLower partialDensity
  norm_num [lowerLog]
  field_simp [h0,h1,h2,hh]
  norm_num [h]
  ring

/-- Generic finite-pole primitive; these are algebraic Laurent terms, not log series. -/
def polePrimitive (p A B C v : ℝ) : ℝ :=
  A*log (v-p)-B/(v-p)-C/(2*(v-p)^2)

theorem pole_derivative (p A B C v : ℝ) (hv : v-p ≠ 0) :
    HasDerivAt (polePrimitive p A B C)
      (A/(v-p)+B/(v-p)^2+C/(v-p)^3) v := by
  have hd := (hasDerivAt_id v).sub_const p
  convert (((hd.log hv).const_mul A).sub
    ((hasDerivAt_const v B).div hd hv)).sub
    ((hasDerivAt_const v C).div ((hd.pow 2).const_mul 2)
      (mul_ne_zero (by norm_num) (pow_ne_zero _ hv))) using 1 <;>
    first | rfl | (dsimp; field_simp [hv]; ring)

def primitive (v : ℝ) : ℝ :=
  (6/11)*v^2+(8942741/7640325)*v+(299524880/916839)*log v-
  (-8547286566790892748321251/2986096125885620562045000)*log (h-v)+
  polePrimitive 1 (-1151264258336/12882918447) (136261088/3810387) (-93056/10143) v+
  polePrimitive (-2) (-1766372040448/5150827583) (815308800/2982529) (-3881472/1727) v

theorem primitive_derivative {v : ℝ} (hv : v ∈ Icc (4:ℝ) 5) :
    HasDerivAt primitive (W v*gainDensity v) v := by
  have h0 : v ≠ 0 := by linarith [hv.1]
  have h1 : v-1 ≠ 0 := by linarith [hv.1]
  have h2 : v-(-2) ≠ 0 := by linarith [hv.1]
  have hh : h-v ≠ 0 := by dsimp [h]; linarith [hv.2]
  rw [laurent_identity hv]
  convert (((((((hasDerivAt_id v).pow 2).const_mul (6/11)).add
    ((hasDerivAt_id v).const_mul (8942741/7640325))).add
    ((hasDerivAt_log h0).const_mul (299524880/916839))).sub
    ((((hasDerivAt_const v h).sub (hasDerivAt_id v)).log hh).const_mul
      (-8547286566790892748321251/2986096125885620562045000))).add
    (pole_derivative 1 _ _ _ v h1)).add (pole_derivative (-2) _ _ _ v h2) using 1 <;>
    first | rfl | (dsimp [partialDensity]; ring)

/-- The full signed weight is used under the original affine coordinate. -/
theorem weight_identity {t : ℝ} (ht : t ∈ Icc (c 5) (c 4)) :
    W (u t)/a = SharedRationalEnvelope.weight t := by
  have hg := JointSharedTightEnclosure.middle_geometry ht
  unfold W u h SharedRationalEnvelope.weight
  norm_num [a,truncatedSixthLowerAlpha]
  have hn : 1-t*2 ≠ 0 := by linarith [hg.2.1]
  have ht0 : t ≠ 0 := hg.1.ne'
  field_simp [ht0,hn]
  ring_nf
  field_simp [ht0,hn]
  ring

def gainReal : ℝ := primitive 5-primitive 4

open scoped Interval

theorem gain_integrable : IntervalIntegrable
    (fun t => SharedRationalEnvelope.weight t*gainDensity (u t)) volume (c 5) (c 4) := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  rw [uIcc_of_le (show c 5 ≤ c 4 by norm_num [c,a,truncatedSixthLowerAlpha])] at ht
  have hg := JointSharedTightEnclosure.middle_geometry ht
  have h0 : t ≠ 0 := hg.1.ne'
  have hh : 1/2-t ≠ 0 := hg.2.1.ne'
  have h1 : u t-1 ≠ 0 := by linarith [hg.2.2.1]
  have h2 : u t+2 ≠ 0 := by linarith [hg.2.2.1]
  apply ContinuousAt.continuousWithinAt
  unfold SharedRationalEnvelope.weight gainDensity rationalLower oldLower
  have hu : Continuous (fun t : ℝ => u t) := by unfold u; fun_prop
  fun_prop (disch := positivity)

/-- Chain-rule FTC on the complete original t interval, without any new cut. -/
theorem full_signed_ftc :
    (∫ t in (c 5)..(c 4), SharedRationalEnvelope.weight t*gainDensity (u t)) = gainReal := by
  have hd (t : ℝ) (ht : t ∈ uIcc (c 5) (c 4)) :
      HasDerivAt (fun t => -primitive (u t))
        (SharedRationalEnvelope.weight t*gainDensity (u t)) t := by
    rw [uIcc_of_le (show c 5 ≤ c 4 by norm_num [c,a,truncatedSixthLowerAlpha])] at ht
    have hg := JointSharedTightEnclosure.middle_geometry ht
    have hu : HasDerivAt u ((-1)/a) t := by
      convert (((hasDerivAt_const t (1/2:ℝ)).sub (hasDerivAt_id t)).div_const a) using 1 <;>
        first | rfl | norm_num
    apply (((primitive_derivative hg.2.2).comp t hu).neg).congr_deriv
    rw [← weight_identity ht]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd gain_integrable]
  have h4 : u (c 4)=4 := by norm_num [u,c,a,truncatedSixthLowerAlpha]
  have h5 : u (c 5)=5 := by norm_num [u,c,a,truncatedSixthLowerAlpha]
  rw [h4,h5]
  unfold gainReal
  ring

theorem old_middle_integral :
    JointSharedTightEnclosure.weighted JointSharedTightEnclosure.middleHi (c 5) (c 4) =
      ExactWeightTripleEnclosure.middleUpper := by
  unfold JointSharedTightEnclosure.weighted ExactWeightTripleEnclosure.middleUpper
  rw [← ExactWeightTripleEnclosure.shifted_ftc _ _ _ _ _ _ _
    (by norm_num [c,a,truncatedSixthLowerAlpha])
    (by norm_num [c,a,truncatedSixthLowerAlpha])
    (by norm_num [c,a,truncatedSixthLowerAlpha])]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp [JointSharedTightEnclosure.middleHi,ExactWeightTripleEnclosure.shifted,
    ExactWeightTripleEnclosure.poly]
  ring

/-- New upper bound for the actual original middle kernel, not a proxy kernel. -/
theorem middle_upper : BaseGSharedActualRecovery.middleKernel ≤
    ExactWeightTripleEnclosure.middleUpper-gainReal := by
  have hl : a ≤ c 5 := by norm_num [a,c,truncatedSixthLowerAlpha]
  have hr := SharedRationalEnvelope.window_order.2.1
  have ho : c 5 ≤ c 4 := by norm_num [a,c,truncatedSixthLowerAlpha]
  have hk := BaseGSharedActualRecovery.kernel_integrable
    (fun v => GConvexChord.C+GConvexChord.m*v) hl hr ho (by fun_prop)
  have hi := JointSharedTightEnclosure.weighted_integrable JointSharedTightEnclosure.middleHi
    (by unfold JointSharedTightEnclosure.middleHi; fun_prop) hl hr ho
  have hm := intervalIntegral.integral_mono_on ho hk (hi.sub gain_integrable) (fun t ht => by
    rw [HighSharedKernelMagnitude.kernel_density (fun v => GConvexChord.C+GConvexChord.m*v)]
    have hp := mul_le_mul_of_nonneg_left
      (MiddleInitialEnvelope.middle_pointwise (JointSharedTightEnclosure.middle_geometry ht).2.2)
      (HighSharedKernelMagnitude.middle_weight ht).1
    simpa only [mul_sub] using hp)
  rw [intervalIntegral.integral_sub hi gain_integrable,full_signed_ftc] at hm
  change BaseGSharedActualRecovery.middleKernel ≤
    JointSharedTightEnclosure.weighted JointSharedTightEnclosure.middleHi (c 5) (c 4)-gainReal at hm
  rwa [old_middle_integral] at hm

end MiddleInitialFTC
