import E10FourMajorEnvelopes

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open FourRoughClosedMass ClassicalLogFourBounds

namespace WuTarget.E10FourMajor

theorem kernel_upper {x y z t : ℝ} (hx : alpha ≤ x) (hy : alpha ≤ y)
    (hz : alpha ≤ z) (ht : alpha ≤ t) :
    regularKernel x y z t ≤ (4/7)/(x*y^2*z*t) := by
  have ha := fixed_geometry_major.1
  have hx0 := ha.trans_le hx
  have hy0 := ha.trans_le hy
  have hz0 := ha.trans_le hz
  have ht0 := ha.trans_le ht
  have h := SecondFunctionalFourSevenths.buchstab_le_four_sevenths
    (show (7/4 : ℝ) ≤ max 2 (parameter x y z t) from
      le_trans (by norm_num) (le_max_left _ _))
  have he : regularKernel x y z t =
      LiLiuPrereqBuchstab.buchstab (max 2 (parameter x y z t))/(x*y^2*z*t) := by
    simp only [regularKernel,clip,max_eq_right hx,max_eq_right hy,
      max_eq_right hz,max_eq_right ht]
  rw [he]
  exact div_le_div_of_nonneg_right h (by positivity)

theorem inner10_upper {x y z : ℝ} (hx : alpha ≤ x) (hy : alpha ≤ y)
    (hz : z ∈ Icc alpha beta) :
    regularInner10 x y z ≤ (4/7)/(x*y^2*z)*FourLogAffine.ell z := by
  have h := integral_le_log_tail (f := fun t => regularKernel x y z t)
    (C := (4/7)/(x*y^2*z))
    (regularKernel_continuous.comp (f := fun t : ℝ => (x,y,z,t)) (by fun_prop))
    (fixed_geometry_major.1.trans_le hz.1) hz.2 0 (fun t ht => by
      simpa only [pow_zero,mul_one,div_div,mul_assoc] using
        kernel_upper hx hy hz.1 (hz.1.trans ht.1))
  simpa only [regularInner10,FourLogAffine.ell,Nat.cast_zero,zero_add,pow_one,div_one] using h

theorem inner11_upper {x y z : ℝ} (hx : alpha ≤ x) (hy : alpha ≤ y)
    (hz : z ∈ Icc alpha beta) :
    regularInner11 x y z ≤
      (4/7)/(x*y^2*z)*(crossCap+slope*FourLogAffine.ell z) := by
  have ha := fixed_geometry_major.1
  have hb := fixed_geometry_major.2.2.2.2.2.1
  have ho : beta ≤ lam-z := by
    linarith only [hz.2,fixed_geometry_major.2.2.2.2.1]
  have h := integral_le_log_tail (f := fun t => regularKernel x y z t)
    (C := (4/7)/(x*y^2*z))
    (regularKernel_continuous.comp (f := fun t : ℝ => (x,y,z,t)) (by fun_prop))
    hb ho 0 (fun t ht => by
      simpa only [pow_zero,mul_one,div_div,mul_assoc] using
        kernel_upper hx hy hz.1 (fixed_geometry_major.2.1.trans ht.1))
  change regularInner11 x y z ≤ _ at h
  norm_num only [Nat.cast_zero,zero_add,pow_one,div_one] at h
  have hc : 0 ≤ (4/7)/(x*y^2*z) := by
    have hx0 := ha.trans_le hx
    have hy0 := ha.trans_le hy
    have hz0 := ha.trans_le hz.1
    positivity
  exact h.trans (mul_le_mul_of_nonneg_left (cross_tangent hz) hc)

theorem middle_pair_upper {x y : ℝ} (hx : alpha ≤ x) (hy : y ∈ Icc alpha beta) :
    regularMiddle10 x y+regularMiddle11 x y ≤
      (4/7)/(x*y^2)*
        (crossCap*FourLogAffine.ell y+(1+slope)*FourLogAffine.ell y^2/2) := by
  have hi10 := (regularInner10_continuous.comp
    (f := fun z : ℝ => (x,y,z)) (by fun_prop)).intervalIntegrable (μ := volume) y beta
  have hi11 := (regularInner11_continuous.comp
    (f := fun z : ℝ => (x,y,z)) (by fun_prop)).intervalIntegrable (μ := volume) y beta
  change IntervalIntegrable (fun z => regularInner10 x y z) volume y beta at hi10
  change IntervalIntegrable (fun z => regularInner11 x y z) volume y beta at hi11
  have hi := FourLogAffine.integral_le_two_tails
    (f := fun z => regularInner10 x y z+regularInner11 x y z)
    (C := (4/7)*crossCap/(x*y^2)) (D := (4/7)*(1+slope)/(x*y^2))
    ((regularInner10_continuous.comp (f := fun z : ℝ => (x,y,z)) (by fun_prop)).add
      (regularInner11_continuous.comp (f := fun z : ℝ => (x,y,z)) (by fun_prop)))
    (fixed_geometry_major.1.trans_le hy.1) hy.2 0 1 (fun z hz => by
      have h10 := inner10_upper hx hy.1 ⟨hy.1.trans hz.1,hz.2⟩
      have h11 := inner11_upper hx hy.1 ⟨hy.1.trans hz.1,hz.2⟩
      have hs := add_le_add h10 h11
      convert hs using 1 <;> first | rfl | (simp only [pow_zero,pow_one,FourLogAffine.ell]; ring))
  rw [intervalIntegral.integral_add hi10 hi11] at hi
  change regularMiddle10 x y+regularMiddle11 x y ≤ _ at hi
  convert hi using 1
  norm_num only [Nat.cast_zero,Nat.cast_one,zero_add,one_add_one_eq_two,pow_one,div_one]
  unfold FourLogAffine.ell
  ring

end WuTarget.E10FourMajor
