import SrcFourEnclosureMass

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve FourRoughClosedMass
open Wu08OriginalFourWeights

namespace WuSource.SrcFourEnclosure

theorem inner_bounds {l u x y z : ℝ}
    (hx : alpha ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hz : z ≤ beta)
    (hk : ∀ t ∈ Icc z (lam-z),
      l/(x*y^2*z*t) ≤ regularKernel x y z t ∧
        regularKernel x y z t ≤ u/(x*y^2*z*t)) :
    l/(x*y^2)*density z ≤ regularInner10 x y z+regularInner11 x y z ∧
      regularInner10 x y z+regularInner11 x y z ≤ u/(x*y^2)*density z := by
  have haz := hx.trans (hxy.trans hyz)
  have hz0 := geometry.1.trans_le haz
  have hzz : z ≤ lam-z := by linarith only [hz,geometry.2.2.2.2.1]
  have hcont := regularKernel_continuous.comp (f := fun t : ℝ => (x,y,z,t)) (by fun_prop)
  have hlo := SrcFour.integral_ge_two_tails (f := fun t => regularKernel x y z t)
    (C := l/(x*y^2*z)) (D := 0) hcont hz0 hzz 0 0 (fun t ht => by
      simpa only [pow_zero,mul_one,zero_mul,zero_div,add_zero,div_div,mul_assoc]
        using (hk t ht).1)
  have hup := ClassicalLogFourBounds.integral_le_log_tail
    (f := fun t => regularKernel x y z t) (C := u/(x*y^2*z))
    hcont hz0 hzz 0 (fun t ht => by
      simpa only [pow_zero,mul_one,div_div,mul_assoc] using (hk t ht).2)
  rw [SrcFour.inner_pair_merged,density_eq ⟨haz,hz⟩]
  norm_num only [Nat.cast_zero,zero_add,pow_one,div_one,zero_mul,zero_div,add_zero] at hlo hup
  constructor
  · convert hlo using 1
    unfold cross
    ring
  · convert hup using 1
    unfold cross
    ring

theorem middle_bounds {l u x y : ℝ}
    (hx : alpha ≤ x) (hxy : x ≤ y) (hy : y ≤ beta)
    (hk : ∀ z ∈ Icc y beta, ∀ t ∈ Icc z (lam-z),
      l/(x*y^2*z*t) ≤ regularKernel x y z t ∧
        regularKernel x y z t ≤ u/(x*y^2*z*t)) :
    l/(x*y^2)*G y ≤ regularMiddle10 x y+regularMiddle11 x y ∧
      regularMiddle10 x y+regularMiddle11 x y ≤ u/(x*y^2)*G y := by
  have hc10 := regularInner10_continuous.comp (f := fun z : ℝ => (x,y,z)) (by fun_prop)
  have hc11 := regularInner11_continuous.comp (f := fun z : ℝ => (x,y,z)) (by fun_prop)
  have hi10 := hc10.intervalIntegrable (μ := volume) y beta
  have hi11 := hc11.intervalIntegrable (μ := volume) y beta
  change IntervalIntegrable (fun z => regularInner10 x y z) volume y beta at hi10
  change IntervalIntegrable (fun z => regularInner11 x y z) volume y beta at hi11
  have hd := density_continuous.intervalIntegrable (μ := volume) y beta
  have hlo := intervalIntegral.integral_mono_on hy (hd.const_mul (l/(x*y^2)))
    (hi10.add hi11) (fun z hz => (inner_bounds hx hxy hz.1 hz.2 (hk z hz)).1)
  have hup := intervalIntegral.integral_mono_on hy (hi10.add hi11)
    (hd.const_mul (u/(x*y^2))) (fun z hz => (inner_bounds hx hxy hz.1 hz.2 (hk z hz)).2)
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add hi10 hi11] at hlo hup
  exact ⟨hlo,hup⟩

theorem outer_bounds {l u x : ℝ} (hx : x ∈ Icc alpha beta)
    (hk : ∀ y ∈ Icc x beta, ∀ z ∈ Icc y beta, ∀ t ∈ Icc z (lam-z),
      l/(x*y^2*z*t) ≤ regularKernel x y z t ∧
        regularKernel x y z t ≤ u/(x*y^2*z*t)) :
    l*outerMass x ≤ regularOuter10 x+regularOuter11 x ∧
      regularOuter10 x+regularOuter11 x ≤ u*outerMass x := by
  have hc10 := regularMiddle10_continuous.comp (f := fun y : ℝ => (x,y)) (by fun_prop)
  have hc11 := regularMiddle11_continuous.comp (f := fun y : ℝ => (x,y)) (by fun_prop)
  have hi10 := hc10.intervalIntegrable (μ := volume) x beta
  have hi11 := hc11.intervalIntegrable (μ := volume) x beta
  change IntervalIntegrable (fun y => regularMiddle10 x y) volume x beta at hi10
  change IntervalIntegrable (fun y => regularMiddle11 x y) volume x beta at hi11
  have hi := H_integrand_continuous.intervalIntegrable (μ := volume) x beta
  have hlo := intervalIntegral.integral_mono_on hx.2 (hi.const_mul (l/x))
    (hi10.add hi11) (fun y hy => by
      rw [clamp_eq ⟨hx.1.trans hy.1,hy.2⟩]
      convert (middle_bounds hx.1 hy.1 hy.2 (hk y hy)).1 using 1
      ring)
  have hup := intervalIntegral.integral_mono_on hx.2 (hi10.add hi11)
    (hi.const_mul (u/x)) (fun y hy => by
      rw [clamp_eq ⟨hx.1.trans hy.1,hy.2⟩]
      convert (middle_bounds hx.1 hy.1 hy.2 (hk y hy)).2 using 1
      ring)
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add hi10 hi11] at hlo hup
  rw [outerMass,clamp_eq hx]
  constructor
  · convert hlo using 1 <;> first | rfl | (unfold H; ring)
  · convert hup using 1 <;> first | rfl | (unfold H; ring)

theorem weighted_mono {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x ∈ Icc alpha beta, f x ≤ g x) : original f ≤ original g := by
  have hs := intervalIntegral.integral_mono_on geometry.2.2.2.2.2.1
    (weighted_integrable hf) (weighted_integrable hg) (fun x hx =>
      div_le_div_of_nonneg_right (hfg x ⟨hx.1,hx.2.trans geometry.2.2.2.2.2.2⟩)
        (by linarith only [hx.2]))
  have hl := intervalIntegral.integral_mono_on geometry.2.2.2.2.2.2
    (hf.intervalIntegrable (μ := volume) (1/10 : ℝ) beta)
    (hg.intervalIntegrable (μ := volume) (1/10 : ℝ) beta)
    (fun x hx => hfg x ⟨geometry.2.2.2.2.2.1.trans hx.1,hx.2⟩)
  unfold original
  linarith only [hs,hl]

theorem original_const_mul (c : ℝ) (f : ℝ → ℝ) :
    original (fun x => c*f x) = c*original f := by
  unfold original
  simp_rw [mul_div_assoc,intervalIntegral.integral_const_mul]
  ring

theorem original_pair_add :
    original (fun x => regularOuter10 x+regularOuter11 x) = original10+original11 := by
  unfold original original10 original11
  simp_rw [add_div]
  rw [intervalIntegral.integral_add (weighted_integrable regularOuter10_continuous)
    (weighted_integrable regularOuter11_continuous),
    intervalIntegral.integral_add
      (regularOuter10_continuous.intervalIntegrable (μ := volume) (1/10 : ℝ) beta)
      (regularOuter11_continuous.intervalIntegrable (μ := volume) (1/10 : ℝ) beta)]
  ring

theorem original_pair_uniform {l u : ℝ}
    (hl : ∀ v : ℝ, (3 : ℝ) ≤ v → l ≤ LiLiuPrereqBuchstab.buchstab v)
    (hu : ∀ v : ℝ, (3 : ℝ) ≤ v → LiLiuPrereqBuchstab.buchstab v ≤ u) :
    l*mass ≤ original10+original11 ∧ original10+original11 ≤ u*mass := by
  have hb (x : ℝ) (hx : x ∈ Icc alpha beta) :=
    outer_bounds hx (fun y hy z hz t ht =>
      merged_kernel_bounds hl hu hx.1 hy.1 hz.1 hz.2 ht)
  have hc := regularOuter10_continuous.add regularOuter11_continuous
  have h1 := weighted_mono (outerMass_continuous.const_mul l) hc (fun x hx => (hb x hx).1)
  have h2 := weighted_mono hc (outerMass_continuous.const_mul u) (fun x hx => (hb x hx).2)
  rw [original_const_mul,original_pair_add] at h1 h2
  exact ⟨h1,h2⟩

theorem original_pair_lower {l : ℝ}
    (hl : ∀ v : ℝ, (3 : ℝ) ≤ v → l ≤ LiLiuPrereqBuchstab.buchstab v) :
    l*mass ≤ original10+original11 :=
  (original_pair_uniform hl (fun _ hv =>
    SecondFunctionalFourSevenths.buchstab_le_four_sevenths
      (show (7/4 : ℝ) ≤ _ by linarith only [hv]))).1

#check @original_pair_uniform
#check @original_pair_lower
#print axioms original_pair_uniform
#print axioms original_pair_lower
end WuSource.SrcFourEnclosure
