import W13TightScalar

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open FourRoughClosedMass ClassicalLogFourBounds

namespace WuTarget.E10Four

def cross (x : ℝ) : ℝ := log (lam-x)-log beta
def kappa : ℝ := alpha/(lam-alpha)
def crossLoss (x : ℝ) : ℝ := kappa*(log x-log alpha)
def rebateCoeff : ℝ := (4/7)*kappa/(2*beta)
def rebate (x : ℝ) : ℝ :=
  rebateCoeff*(log x-log alpha)*(log beta-log x)^2/x

theorem cross_geometry {x : ℝ} (hx : x ∈ Icc alpha beta) :
    0 < x ∧ 0 < beta ∧ beta ≤ lam-x ∧ 0 < lam-alpha := by
  have ha := fixed_geometry.2.1
  have hb := ha.trans_le fixed_geometry.2.2.1
  have ho : beta ≤ lam-x := by
    linarith only [hx.2, fixed_geometry.2.2.2.2.2.2.1]
  exact ⟨ha.trans_le hx.1, hb, ho, by linarith only [hb, ho, hx.1]⟩

theorem cross_nonneg {x : ℝ} (hx : x ∈ Icc alpha beta) : 0 ≤ cross x :=
  sub_nonneg.mpr (log_le_log (cross_geometry hx).2.1 (cross_geometry hx).2.2.1)

theorem crossLoss_nonneg {x : ℝ} (hx : x ∈ Icc alpha beta) : 0 ≤ crossLoss x := by
  exact mul_nonneg (div_nonneg fixed_geometry.2.1.le (cross_geometry hx).2.2.2.le)
    (sub_nonneg.mpr (log_le_log fixed_geometry.2.1 hx.1))

theorem cross_correlation {x : ℝ} (hx : x ∈ Icc alpha beta) :
    cross x+crossLoss x ≤ crossLog := by
  obtain ⟨hx0, hb, ho, hla⟩ := cross_geometry hx
  have hlx : 0 < lam-x := hb.trans_le ho
  have hlog := log_le_sub_one_of_pos (div_pos hlx hla)
  rw [log_div hlx.ne' hla.ne'] at hlog
  have hlogx := log_le_sub_one_of_pos (div_pos hx0 fixed_geometry.2.1)
  rw [log_div hx0.ne' fixed_geometry.2.1.ne'] at hlogx
  have hxpay : alpha*(log x-log alpha) ≤ x-alpha := by
    have hm := mul_le_mul_of_nonneg_left hlogx fixed_geometry.2.1.le
    field_simp [fixed_geometry.2.1.ne'] at hm
    nlinarith only [hm]
  have hp := div_le_div_of_nonneg_right hxpay hla.le
  have he : (lam-x)/(lam-alpha)-1 = -(x-alpha)/(lam-alpha) := by
    field_simp
    ring
  rw [he] at hlog
  unfold cross crossLoss kappa crossLog
  ring_nf at hp hlog ⊢
  linarith only [hp, hlog]

theorem inner11_correlated {x y z : ℝ} (hx : x ∈ Icc alpha beta)
    (hxy : x ≤ y) (hyb : y ≤ beta) (hyz : y ≤ z) (hzb : z ≤ beta) :
    regularInner11 x y z ≤ (4/7)*FourLogAffine.affine y*cross x/(x*y*z) := by
  have ha := fixed_geometry.2.1
  have hy : alpha ≤ y := hx.1.trans hxy
  have hz : alpha ≤ z := hy.trans hyz
  have hb := (cross_geometry hx).2.1
  have horder : beta ≤ lam-z := (cross_geometry ⟨hz,hzb⟩).2.2.1
  have hi := integral_le_log_tail
    (f := fun t => regularKernel x y z t)
    (C := (4/7)*FourLogAffine.affine y/(x*y*z))
    (regularKernel_continuous.comp (f := fun t : ℝ => (x,y,z,t)) (by fun_prop))
    hb horder 0 (fun t ht => by
      simpa only [pow_zero, mul_one, div_div] using
        FourLogAffine.regular_le_affine hx.1 hy hyb hz
          (fixed_geometry.2.2.1.trans ht.1))
  change regularInner11 x y z ≤ _ at hi
  norm_num only [Nat.cast_zero, zero_add, pow_one, div_one] at hi
  have hl : log (lam-z) ≤ log (lam-x) :=
    log_le_log (hb.trans_le horder) (by linarith only [hxy,hyz])
  have hc : 0 ≤ (4/7)*FourLogAffine.affine y/(x*y*z) := by
    have hx0 := ha.trans_le hx.1
    have hy0 := ha.trans_le hy
    have hz0 := ha.trans_le hz
    have hp := FourLogAffine.affine_pos hy hyb
    positivity
  exact hi.trans (by
    have hp := mul_le_mul_of_nonneg_left (sub_le_sub_right hl (log beta)) hc
    unfold cross
    convert hp using 1
    ring)

theorem middle11_correlated {x y : ℝ} (hx : x ∈ Icc alpha beta)
    (hxy : x ≤ y) (hyb : y ≤ beta) :
    regularMiddle11 x y ≤ (4/7)*cross x*
      (FourLogAffine.C0*FourLogAffine.ell y+FourLogAffine.ell y^2/beta)/(x*y) := by
  have hi := integral_le_log_tail (f := fun z => regularInner11 x y z)
    (C := (4/7)*FourLogAffine.affine y*cross x/(x*y))
    (regularInner11_continuous.comp (f := fun z : ℝ => (x,y,z)) (by fun_prop))
    (fixed_geometry.2.1.trans_le (hx.1.trans hxy)) hyb 0 (fun z hz => by
      have hh := inner11_correlated hx hxy hyb hz.1 hz.2
      convert hh using 1
      simp only [pow_zero]
      ring)
  change regularMiddle11 x y ≤ _ at hi
  convert hi using 1
  unfold FourLogAffine.affine FourLogAffine.ell
  norm_num only [Nat.cast_zero, zero_add, pow_one, div_one]
  ring

theorem outer11_correlated {x : ℝ} (hx : x ∈ Icc alpha beta) :
    regularOuter11 x ≤ (4/7)*cross x*
      (FourLogAffine.C0*FourLogAffine.ell x^2/2+
        FourLogAffine.ell x^3/(3*beta))/x := by
  have hi := FourLogAffine.integral_le_two_tails
    (f := fun y => regularMiddle11 x y)
    (C := (4/7)*cross x*FourLogAffine.C0/x)
    (D := (4/7)*cross x/(beta*x))
    (regularMiddle11_continuous.comp (f := fun y : ℝ => (x,y)) (by fun_prop))
    (fixed_geometry.2.1.trans_le hx.1) hx.2 1 2 (fun y hy => by
      have hh := middle11_correlated hx hy.1 hy.2
      convert hh using 1
      unfold FourLogAffine.ell
      ring)
  change regularOuter11 x ≤ _ at hi
  convert hi using 1
  unfold FourLogAffine.ell
  norm_num only [Nat.cast_one, Nat.cast_ofNat]
  ring

end WuTarget.E10Four
