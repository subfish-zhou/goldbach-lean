import SrcFourGeometry

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open FourRoughClosedMass ClassicalLogFourBounds
open WuTarget.E10FourMajor

namespace WuSource.SrcFour

def scale (c : ℝ) : ℝ := 7*c/4

theorem inner10_fine {c x y z : ℝ}
    (hc : ∀ u : ℝ, (17/5 : ℝ) ≤ u → LiLiuPrereqBuchstab.buchstab u ≤ c)
    (hx : alpha ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hz : z ≤ beta) :
    regularInner10 x y z ≤ c/(x*y^2*z)*FourLogAffine.ell z := by
  have ha := geometry.2.2.2.1
  have haz := hx.trans (hxy.trans hyz)
  have hi := integral_le_log_tail (f := fun t => regularKernel x y z t)
    (C := c/(x*y^2*z))
    (regularKernel_continuous.comp (f := fun t : ℝ => (x,y,z,t)) (by fun_prop))
    (ha.trans_le haz) hz 0 (fun t ht => by
      simpa only [pow_zero,mul_one,div_div,mul_assoc] using
        fine_kernel hc hx (hx.trans hxy) haz (haz.trans ht.1)
          (ten_fine ⟨hx,hxy,hyz,ht.1,ht.2⟩))
  simpa only [regularInner10,FourLogAffine.ell,Nat.cast_zero,zero_add,pow_one,div_one] using hi

theorem inner11_fine {c x y z : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ u : ℝ, (17/5 : ℝ) ≤ u → LiLiuPrereqBuchstab.buchstab u ≤ c)
    (hx : alpha ≤ x) (hxc : x ≤ outerCut) (hxy : x ≤ y)
    (hyz : y ≤ z) (hz : z ≤ beta) :
    regularInner11 x y z ≤ c/(x*y^2*z)*(crossCap+slope*FourLogAffine.ell z) := by
  have ha := geometry.2.2.2.1
  have hb := fixed_geometry_major.2.2.2.2.2.1
  have haz := hx.trans (hxy.trans hyz)
  have ho : beta ≤ lam-z := by linarith only [hz,geometry.2.2.2.2.2]
  have hi := integral_le_log_tail (f := fun t => regularKernel x y z t)
    (C := c/(x*y^2*z))
    (regularKernel_continuous.comp (f := fun t : ℝ => (x,y,z,t)) (by fun_prop))
    hb ho 0 (fun t ht => by
      simpa only [pow_zero,mul_one,div_div,mul_assoc] using
        fine_kernel hc hx (hx.trans hxy) haz (haz.trans (hz.trans ht.1))
          (eleven_fine_of_outer ⟨hx,hxy,hyz,hz,ht.1,ht.2⟩ hxc))
  change regularInner11 x y z ≤ _ at hi
  norm_num only [Nat.cast_zero,zero_add,pow_one,div_one] at hi
  have hx0 := ha.trans_le hx
  have hy0 := hx0.trans_le hxy
  have hz0 := hy0.trans_le hyz
  exact hi.trans (mul_le_mul_of_nonneg_left (cross_tangent ⟨haz,hz⟩)
    (by positivity))

theorem middle_fine {c x y : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ u : ℝ, (17/5 : ℝ) ≤ u → LiLiuPrereqBuchstab.buchstab u ≤ c)
    (hx : alpha ≤ x) (hxc : x ≤ outerCut) (hxy : x ≤ y) (hy : y ≤ beta) :
    regularMiddle10 x y+regularMiddle11 x y ≤
      c/(x*y^2)*
        (crossCap*FourLogAffine.ell y+(1+slope)*FourLogAffine.ell y^2/2) := by
  have hi10 := (regularInner10_continuous.comp
    (f := fun z : ℝ => (x,y,z)) (by fun_prop)).intervalIntegrable (μ := volume) y beta
  have hi11 := (regularInner11_continuous.comp
    (f := fun z : ℝ => (x,y,z)) (by fun_prop)).intervalIntegrable (μ := volume) y beta
  change IntervalIntegrable (fun z => regularInner10 x y z) volume y beta at hi10
  change IntervalIntegrable (fun z => regularInner11 x y z) volume y beta at hi11
  have hi := FourLogAffine.integral_le_two_tails
    (f := fun z => regularInner10 x y z+regularInner11 x y z)
    (C := c*crossCap/(x*y^2)) (D := c*(1+slope)/(x*y^2))
    ((regularInner10_continuous.comp (f := fun z : ℝ => (x,y,z)) (by fun_prop)).add
      (regularInner11_continuous.comp (f := fun z : ℝ => (x,y,z)) (by fun_prop)))
    (geometry.2.2.2.1.trans_le (hx.trans hxy)) hy 0 1 (fun z hz => by
      have hs := add_le_add (inner10_fine hc hx hxy hz.1 hz.2)
        (inner11_fine hc0 hc hx hxc hxy hz.1 hz.2)
      convert hs using 1 <;> first | rfl |
        (simp only [pow_zero,pow_one,FourLogAffine.ell]; ring))
  rw [intervalIntegral.integral_add hi10 hi11] at hi
  change regularMiddle10 x y+regularMiddle11 x y ≤ _ at hi
  convert hi using 1
  norm_num only [Nat.cast_zero,Nat.cast_one,zero_add,one_add_one_eq_two,pow_one,div_one]
  unfold FourLogAffine.ell
  ring

theorem middle_scaled {c x y : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ u : ℝ, (17/5 : ℝ) ≤ u → LiLiuPrereqBuchstab.buchstab u ≤ c)
    (hx : alpha ≤ x) (hxc : x ≤ outerCut) (hxy : x ≤ y) (hy : y ≤ beta) :
    regularMiddle10 x y+regularMiddle11 x y ≤
      scale c*(∑ i : Fin 5, middleTerm i x y) := by
  rw [middle_sum_identity]
  have hx0 := geometry.2.2.2.1.trans_le hx
  have hy0 := hx0.trans_le hxy
  have hell := FourLogAffine.ell_nonneg (hx.trans hxy) hy
  have hs := slope_pos
  have hcross := crossCap_pos
  have hp := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (reciprocal_upper ⟨hx.trans hxy,hy⟩)
      (show 0 ≤ c/(x*y) by positivity))
    (show 0 ≤ crossCap*FourLogAffine.ell y+
      (1+slope)*FourLogAffine.ell y^2/2 by positivity)
  apply (middle_fine hc0 hc hx hxc hxy hy).trans
  convert hp using 1 <;> simp only [scale] <;> ring

theorem outer_fine {c x : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ u : ℝ, (17/5 : ℝ) ≤ u → LiLiuPrereqBuchstab.buchstab u ≤ c)
    (hx : x ∈ Icc alpha outerCut) :
    regularOuter10 x+regularOuter11 x ≤ scale c*profile x := by
  have hx0 := geometry.2.2.2.1.trans_le hx.1
  have hxb := hx.2.trans geometry.2.2.1.le
  have hi10 := (regularMiddle10_continuous.comp
    (f := fun y : ℝ => (x,y)) (by fun_prop)).intervalIntegrable (μ := volume) x beta
  have hi11 := (regularMiddle11_continuous.comp
    (f := fun y : ℝ => (x,y)) (by fun_prop)).intervalIntegrable (μ := volume) x beta
  change IntervalIntegrable (fun y => regularMiddle10 x y) volume x beta at hi10
  change IntervalIntegrable (fun y => regularMiddle11 x y) volume x beta at hi11
  have his : IntervalIntegrable (fun y => ∑ i : Fin 5, middleTerm i x y) volume x beta :=
    IntervalIntegrable.sum Finset.univ (fun i _ => middleTerm_integrable i hx0 hxb)
  have hi := intervalIntegral.integral_mono_on hxb (hi10.add hi11)
    (his.const_mul (scale c))
    (fun y hy => middle_scaled hc0 hc hx.1 hx.2 hy.1 hy.2)
  rw [intervalIntegral.integral_add hi10 hi11,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (fun i _ => middleTerm_integrable i hx0 hxb)] at hi
  change regularOuter10 x+regularOuter11 x ≤ _ at hi
  simp_rw [middleTerm_integral _ hx0 hxb] at hi
  exact hi

#check @outer_fine
#print axioms outer_fine
end WuSource.SrcFour
