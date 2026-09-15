import Phase23Audit

namespace Wu2008DoubleSieve.Phase24
open Real Set MeasureTheory FourRoughClosedMass ClassicalLogFourBounds
open FourLogAffine (ell)
open scoped Interval
noncomputable section

def c : ℝ := lam-alpha
def A : ℝ := FourLogAffine.w+alpha/c

theorem c_pos : 0 < c := by
  norm_num [c,lam,alpha,truncatedSixthLowerLambda,truncatedSixthLowerAlpha]

theorem moving_log_tangent {z : ℝ} (_hz : alpha ≤ z) (hzb : z ≤ beta) :
    log (lam-z) ≤ log (lam-alpha)-(z-alpha)/(lam-alpha) := by
  have hb := fixed_geometry.2.1.trans_le fixed_geometry.2.2.1
  have ho : beta ≤ lam-z := by linarith [fixed_geometry.2.2.2.2.2.2.1]
  have hp := hb.trans_le ho
  have hc : 0 < lam-alpha := c_pos
  have h := log_le_sub_one_of_pos (div_pos hp hc)
  rw [log_div hp.ne' hc.ne'] at h
  have he : (lam-z)/(lam-alpha)-1 = -(z-alpha)/(lam-alpha) := by
    field_simp; ring
  rw [he,neg_div] at h
  linarith

/-- The adjacent-interval identity changes no finite closed labels or multiplicities. -/
theorem inner_join (x y z : ℝ) :
    regularInner10 x y z+regularInner11 x y z =
      ∫ t in z..lam-z, regularKernel x y z t := by
  have hc := regularKernel_continuous.comp
    (f := fun t : ℝ => (x,y,z,t)) (by fun_prop)
  exact intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable z beta) (hc.intervalIntegrable beta (lam-z))

theorem regular_reciprocal_sq {x y z t : ℝ}
    (hx : alpha ≤ x) (hy : alpha ≤ y) (hz : alpha ≤ z) (ht : alpha ≤ t) :
    regularKernel x y z t ≤ (4/7)/(x*y^2*z*t) := by
  have hx0 := fixed_geometry.2.1.trans_le hx
  have hy0 := fixed_geometry.2.1.trans_le hy
  have hz0 := fixed_geometry.2.1.trans_le hz
  have ht0 := fixed_geometry.2.1.trans_le ht
  have h := SecondFunctionalFourSevenths.buchstab_le_four_sevenths
    (show (7/4 : ℝ) ≤ max 2 (parameter x y z t) from
      le_trans (by norm_num) (le_max_left _ _))
  simp only [regularKernel,clip,max_eq_right hx,max_eq_right hy,
    max_eq_right hz,max_eq_right ht]
  exact div_le_div_of_nonneg_right h (by positivity)

/-- Both original t intervals are joined before the single Buchstab cap is applied. -/
theorem inner_upper {x y z : ℝ} (hx : alpha ≤ x) (hy : alpha ≤ y)
    (hz : alpha ≤ z) (hzb : z ≤ beta) :
    regularInner10 x y z+regularInner11 x y z ≤
      (4/7)/(x*y^2)*((A+ell z)/z-1/c) := by
  have hx0 := fixed_geometry.2.1.trans_le hx
  have hy0 := fixed_geometry.2.1.trans_le hy
  have hz0 := fixed_geometry.2.1.trans_le hz
  have ho : z ≤ lam-z := by linarith [fixed_geometry.2.2.2.2.2.2.1]
  rw [inner_join]
  have h := integral_le_log_tail (C := (4/7)/(x*y^2*z))
    (regularKernel_continuous.comp (f := fun t : ℝ => (x,y,z,t)) (by fun_prop))
    hz0 ho 0 (fun t ht => by
      have hh := regular_reciprocal_sq hx hy hz (hz.trans ht.1)
      convert hh using 1 <;> first | rfl | ring)
  norm_num only [Nat.cast_zero,zero_add,pow_one,div_one] at h
  have hl := moving_log_tangent hz hzb
  have hw := FourLogAffine.fixed_log_bounds.2.2.2.2
  have htail : log (lam-z)-log z ≤ A+ell z-z/c := by
    dsimp [A,ell,c,crossLog] at *
    rw [sub_div] at hl
    linarith
  have hm := mul_le_mul_of_nonneg_left htail
    (show 0 ≤ (4/7)/(x*y^2*z) by positivity)
  refine h.trans (hm.trans_eq ?_)
  field_simp

/-- The z primitive retains the full moving-endpoint subtraction. -/
def Z (z : ℝ) : ℝ := -A*ell z-ell z^2/2-z/c
def F (y : ℝ) : ℝ :=
  (-ell y^2/2+(1-A)*ell y+(A-1+beta/c))/y+log y/c
def H (x : ℝ) : ℝ := F beta*log x-
  (ell x^2/2+(A-2)*ell x+(3-2*A-beta/c))/x-log x^2/(2*c)

theorem ell_derivative {x : ℝ} (hx : x ≠ 0) : HasDerivAt ell (-1/x) x := by
  convert (hasDerivAt_const x (log beta)).sub (hasDerivAt_log hx) using 1 <;>
    first | rfl | ring

theorem Z_derivative {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt Z ((A+ell z)/z-1/c) z := by
  convert (((ell_derivative hz).const_mul (-A)).sub
    (((ell_derivative hz).pow 2).div_const 2)).sub
    ((hasDerivAt_id z).div_const c) using 1 <;>
    first | rfl | (field_simp; ring)

theorem F_derivative {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt F ((A*ell y+ell y^2/2-(beta-y)/c)/y^2) y := by
  have he := ell_derivative hy
  convert (((((he.pow 2).neg.div_const 2).add (he.const_mul (1-A))).add_const
    (A-1+beta/c)).div (hasDerivAt_id y) hy).add
    ((hasDerivAt_log hy).div_const c) using 1 <;>
    first | rfl | (dsimp; field_simp; ring)

theorem H_derivative {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt H ((F beta-F x)/x) x := by
  have he := ell_derivative hx
  convert (((hasDerivAt_log hx).const_mul (F beta)).sub
    (((((he.pow 2).div_const 2).add (he.const_mul (A-2))).add_const
      (3-2*A-beta/c)).div (hasDerivAt_id x) hx)).sub
    (((hasDerivAt_log hx).pow 2).div_const (2*c)) using 1 <;>
    first | rfl | (dsimp [F]; field_simp; ring)

/-- Signed FTC comparison, with explicit integrability of the whole derivative. -/
theorem compare_primitive {f g P : ℝ → ℝ} {l r : ℝ} (hlr : l ≤ r)
    (hf : Continuous f) (hg : ContinuousOn g (Icc l r))
    (hd : ∀ x ∈ Icc l r, HasDerivAt P (g x) x)
    (hb : ∀ x ∈ Icc l r, f x ≤ g x) :
    (∫ x in l..r, f x) ≤ P r-P l := by
  have hi : IntervalIntegrable g volume l r := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hlr] using hg
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hd x (uIcc_of_le hlr ▸ hx)) hi]
  exact intervalIntegral.integral_mono_on hlr (hf.intervalIntegrable l r) hi hb

theorem middle_upper {x y : ℝ} (hx : alpha ≤ x) (hy : alpha ≤ y) (hyb : y ≤ beta) :
    regularMiddle10 x y+regularMiddle11 x y ≤
      (4/7)/x*((A*ell y+ell y^2/2-(beta-y)/c)/y^2) := by
  have hi10 : Continuous (fun z => regularInner10 x y z) := regularInner10_continuous.comp (f := fun z : ℝ => (x,y,z)) (by fun_prop)
  have hi11 : Continuous (fun z => regularInner11 x y z) := regularInner11_continuous.comp (f := fun z : ℝ => (x,y,z)) (by fun_prop)
  have hn : ∀ z ∈ Icc y beta, z ≠ 0 := fun z hz =>
    (fixed_geometry.2.1.trans_le (hy.trans hz.1)).ne'
  have he : ContinuousOn ell (Icc y beta) :=
    continuousOn_const.sub (continuousOn_id.log hn)
  have h := compare_primitive (f := fun z => regularInner10 x y z+regularInner11 x y z)
    (g := fun z => (4/7)/(x*y^2)*((A+ell z)/z-1/c))
    (P := fun z => (4/7)/(x*y^2)*Z z) hyb (hi10.add hi11)
    (continuousOn_const.mul (((continuousOn_const.add he).div continuousOn_id hn).sub continuousOn_const))
    (fun z hz => (Z_derivative (hn z hz)).const_mul _) (fun z hz =>
      inner_upper hx hy (hy.trans hz.1) hz.2)
  rw [intervalIntegral.integral_add (hi10.intervalIntegrable y beta) (hi11.intervalIntegrable y beta)] at h
  change regularMiddle10 x y+regularMiddle11 x y ≤ _ at h
  convert h using 1
  simp only [Z,ell,sub_self]
  ring

theorem outer_upper {x : ℝ} (hx : alpha ≤ x) (hxb : x ≤ beta) :
    regularOuter10 x+regularOuter11 x ≤ (4/7)/x*(F beta-F x) := by
  have hi10 : Continuous (fun y => regularMiddle10 x y) := regularMiddle10_continuous.comp (f := fun y : ℝ => (x,y)) (by fun_prop)
  have hi11 : Continuous (fun y => regularMiddle11 x y) := regularMiddle11_continuous.comp (f := fun y : ℝ => (x,y)) (by fun_prop)
  have hn : ∀ y ∈ Icc x beta, y ≠ 0 := fun y hy =>
    (fixed_geometry.2.1.trans_le (hx.trans hy.1)).ne'
  have he : ContinuousOn ell (Icc x beta) := continuousOn_const.sub (continuousOn_id.log hn)
  have hg : ContinuousOn (fun y => (4/7)/x*((A*ell y+ell y^2/2-(beta-y)/c)/y^2)) (Icc x beta) :=
    continuousOn_const.mul ((((continuousOn_const.mul he).add ((he.pow 2).div_const 2)).sub
      ((continuousOn_const.sub continuousOn_id).div_const c)).div (continuousOn_id.pow 2)
        (fun y hy => pow_ne_zero 2 (hn y hy)))
  have h := compare_primitive (f := fun y => regularMiddle10 x y+regularMiddle11 x y) hxb (hi10.add hi11) hg
    (fun y hy => (F_derivative (hn y hy)).const_mul ((4/7)/x))
    (fun y hy => middle_upper hx (hx.trans hy.1) hy.2)
  rw [intervalIntegral.integral_add (hi10.intervalIntegrable x beta) (hi11.intervalIntegrable x beta)] at h
  change regularOuter10 x+regularOuter11 x ≤ _ at h
  convert h using 1; ring

def exactMass (L : ℝ) : ℝ :=
  (1/(2*alpha)+1/(2*c))*L^2+
    ((A-2)/alpha+(A-1+beta/c)/beta)*L+
    (3-2*A-beta/c)*(1/alpha-1/beta)

theorem complete_real_upper : 8*I10+8*I11 ≤ (32/7)*exactMass tailLog := by
  have hn : ∀ x ∈ Icc alpha beta, x ≠ 0 := fun x hx =>
    (fixed_geometry.2.1.trans_le hx.1).ne'
  have he : ContinuousOn ell (Icc alpha beta) := continuousOn_const.sub (continuousOn_id.log hn)
  have hf : ContinuousOn F (Icc alpha beta) := by
    exact (((((he.pow 2).neg.div_const 2).add (continuousOn_const.mul he)).add
      continuousOn_const).div continuousOn_id hn).add ((continuousOn_id.log hn).div_const c)
  have hg : ContinuousOn (fun x => (4/7)*((F beta-F x)/x)) (Icc alpha beta) :=
    continuousOn_const.mul ((continuousOn_const.sub hf).div continuousOn_id hn)
  have h := compare_primitive (f := fun x => regularOuter10 x+regularOuter11 x) fixed_geometry.2.2.1
    (regularOuter10_continuous.add regularOuter11_continuous) hg
    (fun x hx => (H_derivative (hn x hx)).const_mul (4/7)) (fun x hx => by
      convert outer_upper hx.1 hx.2 using 1; ring)
  rw [intervalIntegral.integral_add
    (regularOuter10_continuous.intervalIntegrable alpha beta)
    (regularOuter11_continuous.intervalIntegrable alpha beta),← I10_eq_regular,← I11_eq_regular] at h
  have heq : H beta-H alpha = exactMass tailLog := by
    dsimp [H,F,ell,exactMass,tailLog]
    ring
  have hh : (4/7)*H beta-(4/7)*H alpha = (4/7)*exactMass tailLog := by rw [← heq]; ring
  rw [hh] at h
  linarith

def newFour : ℝ := (32/7)*((1/(2*alpha)+1/(2*c))*FourLogAffine.u^2+
    ((A-2)/alpha+(A-1+beta/c)/beta)*FourLogAffine.l+
    (3-2*A-beta/c)*(1/alpha-1/beta))

theorem original_four_upper : 8*I10+8*I11 ≤ newFour := by
  obtain ⟨hl0,hl,hu,_,_⟩ := FourLogAffine.fixed_log_bounds
  have hp := pow_le_pow_left₀ (hl0.le.trans hl) hu 2
  have hpos : 0 ≤ 1/(2*alpha)+1/(2*c) := by
    have ha := fixed_geometry.2.1
    have hc := c_pos
    positivity
  have hneg : (A-2)/alpha+(A-1+beta/c)/beta ≤ 0 := by
    norm_num [A,c,FourLogAffine.w,SharpLogRecurrence.upperLog,alpha,beta,lam,
      truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerLambda]
  have h1 := mul_le_mul_of_nonneg_left hp hpos
  have h2 := mul_le_mul_of_nonpos_left hl hneg
  apply complete_real_upper.trans
  dsimp [exactMass,newFour]
  linarith

theorem strict_four_improvement : newFour < FourLogAffine.newFour := by
  norm_num [newFour,A,c,FourLogAffine.newFour,FourLogAffine.tenUpper,FourLogAffine.elevenUpper,
    FourLogAffine.u,FourLogAffine.l,FourLogAffine.w,SharpLogRecurrence.lowerLog,
    SharpLogRecurrence.upperLog,alpha,beta,lam,truncatedSixthLowerAlpha,
    truncatedSixthLowerBeta,truncatedSixthLowerLambda]

end
end Wu2008DoubleSieve.Phase24
