import SrcFourScalar

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve FourRoughClosedMass

namespace WuSource.SrcFour

def crossFloor : ℝ := SharpLogRecurrence.lowerLog ((lam-beta)/beta)
def slopeFloor : ℝ := alpha/(lam-alpha)
def lowerCoeff (i : Fin 4) : ℝ := ![1,1,1/2,1/6] i

theorem lower_constants :
    0 < crossFloor ∧ 0 < slopeFloor ∧ 0 < lam-beta ∧ 0 < lam-alpha := by
  norm_num [crossFloor,slopeFloor,SharpLogRecurrence.lowerLog,alpha,beta,lam,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerLambda]

theorem lowerCoeff_pos (i : Fin 4) : 0 < lowerCoeff i := by
  fin_cases i <;> norm_num [lowerCoeff]

theorem eleven_three {x y z t : ℝ} (h : ElevenDomain x y z t) :
    (3 : ℝ) ≤ parameter x y z t := by
  obtain ⟨hx,hxy,hyz,hz,_,ht⟩ := h
  have hy0 := geometry.2.2.2.1.trans_le (hx.trans hxy)
  rw [parameter,le_div_iff₀ hy0]
  have hb : 5*beta+lam ≤ 1 := by
    norm_num [beta,lam,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,
      truncatedSixthLowerLambda]
  linarith only [hxy,hyz,hz,ht,hb]

theorem cross_lower {z : ℝ} (hz : z ∈ Icc alpha beta) :
    crossFloor+slopeFloor*FourLogAffine.ell z ≤ log (lam-z)-log beta := by
  have ha := geometry.2.2.2.1
  have hz0 := ha.trans_le hz.1
  have hb := hz0.trans_le hz.2
  have hla := lower_constants.2.2.2
  have hlb := lower_constants.2.2.1
  have hlz : 0 < lam-z := by linarith only [hlb,hz.2]
  have hl := SharpLogRecurrence.log_lower
    ((le_div_iff₀ hb).mpr (by linarith only [geometry.2.2.2.2.2]))
  rw [log_div hlb.ne' hb.ne'] at hl
  have ht := log_le_sub_one_of_pos (div_pos hlb hlz)
  rw [log_div hlb.ne' hlz.ne'] at ht
  have ht' : (beta-z)/(lam-z) ≤ log (lam-z)-log (lam-beta) := by
    have he : (lam-beta)/(lam-z)-1 = -(beta-z)/(lam-z) := by field_simp; ring
    rw [he] at ht
    linarith only [ht]
  have he := log_le_sub_one_of_pos (div_pos hb hz0)
  rw [log_div hb.ne' hz0.ne'] at he
  have he' : FourLogAffine.ell z ≤ (beta-z)/z := by
    convert he using 1
    field_simp
  have hs : slopeFloor ≤ z/(lam-z) := by
    unfold slopeFloor
    apply (div_le_div_iff₀ hla hlz).mpr
    have hl0 : 0 ≤ lam := by linarith only [hlb,hb]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hz.1) hl0]
  have h1 := mul_le_mul_of_nonneg_left he' lower_constants.2.1.le
  have h2 := mul_le_mul_of_nonneg_right hs (div_nonneg (sub_nonneg.mpr hz.2) hz0.le)
  have hi : (z/(lam-z))*((beta-z)/z) = (beta-z)/(lam-z) := by field_simp
  rw [hi] at h2
  change crossFloor ≤ _ at hl
  linarith only [hl,ht',h1,h2]

theorem exp_cubic_lower {s : ℝ} (hs : 0 ≤ s) :
    1+s+s^2/2+s^3/6 ≤ exp s := by
  have h1 (x : ℝ) (_hx : x ∈ Icc 0 s) : 0 ≤ exp x-1-x := by
    linarith only [add_one_le_exp x]
  have h2 (x : ℝ) (hx : x ∈ Icc 0 s) : 0 ≤ exp x-1-x-x^2/2 := by
    apply WuTarget.E10FourMajor.anchored_nonneg
      (f := fun x => exp x-1-x-x^2/2) hx (by simp) (fun y _ => ?_) h1
    convert (((hasDerivAt_exp y).sub_const 1).sub (hasDerivAt_id y)).sub
      (((hasDerivAt_id y).pow 2).div_const 2) using 1 <;> first | rfl | (dsimp; ring)
  have h3 : 0 ≤ exp s-1-s-s^2/2-s^3/6 := by
    apply WuTarget.E10FourMajor.anchored_nonneg
      (f := fun x => exp x-1-x-x^2/2-x^3/6) ⟨hs,le_rfl⟩ (by simp)
      (fun y _ => ?_) h2
    convert ((((hasDerivAt_exp y).sub_const 1).sub (hasDerivAt_id y)).sub
      (((hasDerivAt_id y).pow 2).div_const 2)).sub
      (((hasDerivAt_id y).pow 3).div_const 6) using 1 <;>
        first | rfl | (dsimp; ring)
  linarith only [h3]

theorem reciprocal_lower {y : ℝ} (hy : y ∈ Icc alpha beta) :
    (∑ i : Fin 4, lowerCoeff i*(FourLogAffine.ell y)^i.val)/beta ≤ 1/y := by
  have hy0 := geometry.2.2.2.1.trans_le hy.1
  have hb := hy0.trans_le hy.2
  have he : exp (FourLogAffine.ell y) = beta/y := by
    rw [FourLogAffine.ell,exp_sub,exp_log hb,exp_log hy0]
  have hl := exp_cubic_lower (FourLogAffine.ell_nonneg hy.1 hy.2)
  rw [he] at hl
  have hd := div_le_div_of_nonneg_right hl hb.le
  have hid : beta/y/beta = 1/y := by field_simp
  rw [hid] at hd
  simp only [Fin.sum_univ_succ,lowerCoeff,Fin.val_succ,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.coe_ofNat_eq_mod]
  norm_num only [pow_zero,pow_one]
  convert hd using 1 <;> first | rfl | ring

theorem kernel_lower {c x y z t : ℝ}
    (hc : ∀ u : ℝ, (3 : ℝ) ≤ u → c ≤ LiLiuPrereqBuchstab.buchstab u)
    (hx : alpha ≤ x) (hy : alpha ≤ y) (hz : alpha ≤ z) (ht : alpha ≤ t)
    (hp : (3 : ℝ) ≤ parameter x y z t) :
    c/(x*y^2*z*t) ≤ regularKernel x y z t := by
  have ha := geometry.2.2.2.1
  have hx0 := ha.trans_le hx
  have hy0 := ha.trans_le hy
  have hz0 := ha.trans_le hz
  have ht0 := ha.trans_le ht
  simp only [regularKernel,clip,max_eq_right hx,max_eq_right hy,max_eq_right hz,
    max_eq_right ht,max_eq_right (show (2 : ℝ) ≤ parameter x y z t by linarith)]
  exact div_le_div_of_nonneg_right (hc _ hp) (by positivity)

theorem integral_ge_two_tails {f : ℝ → ℝ} {a b C D : ℝ}
    (hf : Continuous f) (ha : 0 < a) (hab : a ≤ b) (n m : ℕ)
    (hl : ∀ x ∈ Icc a b,
      C*(log b-log x)^n/x+D*(log b-log x)^m/x ≤ f x) :
    C*(log b-log a)^(n+1)/(n+1)+D*(log b-log a)^(m+1)/(m+1) ≤
      ∫ x in a..b, f x := by
  rw [← FourLogAffine.integral_two_tails ha hab n m]
  exact intervalIntegral.integral_mono_on hab
    ((FourLogAffine.tail_integrable ha hab n).add (FourLogAffine.tail_integrable ha hab m))
    (hf.intervalIntegrable a b) hl

theorem inner10_lower {c x y z : ℝ}
    (hc : ∀ u : ℝ, (3 : ℝ) ≤ u → c ≤ LiLiuPrereqBuchstab.buchstab u)
    (hx : alpha ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hz : z ≤ beta) :
    c/(x*y^2*z)*FourLogAffine.ell z ≤ regularInner10 x y z := by
  have haz := hx.trans (hxy.trans hyz)
  have hi := integral_ge_two_tails (f := fun t => regularKernel x y z t)
    (C := c/(x*y^2*z)) (D := 0)
    (regularKernel_continuous.comp (f := fun t : ℝ => (x,y,z,t)) (by fun_prop))
    (geometry.2.2.2.1.trans_le haz) hz 0 0 (fun t ht => by
      have hp := ten_fine ⟨hx,hxy,hyz,ht.1,ht.2⟩
      simpa only [pow_zero,mul_one,zero_mul,zero_div,add_zero,div_div,mul_assoc] using
        kernel_lower hc hx (hx.trans hxy) haz (haz.trans ht.1) (by linarith only [hp]))
  simpa only [regularInner10,FourLogAffine.ell,Nat.cast_zero,zero_add,
    pow_one,div_one,zero_mul,zero_div,add_zero] using hi

theorem inner11_lower {c x y z : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ u : ℝ, (3 : ℝ) ≤ u → c ≤ LiLiuPrereqBuchstab.buchstab u)
    (hx : alpha ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hz : z ≤ beta) :
    c/(x*y^2*z)*(crossFloor+slopeFloor*FourLogAffine.ell z) ≤
      regularInner11 x y z := by
  have haz := hx.trans (hxy.trans hyz)
  have hz0 := geometry.2.2.2.1.trans_le haz
  have hb := hz0.trans_le hz
  have ho : beta ≤ lam-z := by linarith only [hz,geometry.2.2.2.2.2]
  have hi := integral_ge_two_tails (f := fun t => regularKernel x y z t)
    (C := c/(x*y^2*z)) (D := 0)
    (regularKernel_continuous.comp (f := fun t : ℝ => (x,y,z,t)) (by fun_prop))
    hb ho 0 0 (fun t ht => by
      simpa only [pow_zero,mul_one,zero_mul,zero_div,add_zero,div_div,mul_assoc] using
        kernel_lower hc hx (hx.trans hxy) haz (haz.trans (hz.trans ht.1))
          (eleven_three ⟨hx,hxy,hyz,hz,ht.1,ht.2⟩))
  norm_num only [Nat.cast_zero,zero_add,pow_one,div_one,zero_mul,zero_div,add_zero] at hi
  have hx0 := geometry.2.2.2.1.trans_le hx
  have hy0 := hx0.trans_le hxy
  exact (mul_le_mul_of_nonneg_left (cross_lower ⟨haz,hz⟩)
    (by positivity : 0 ≤ c/(x*y^2*z))).trans hi

#check @cross_lower
#check @reciprocal_lower
#check @inner10_lower
#check @inner11_lower
#print axioms cross_lower
#print axioms reciprocal_lower
#print axioms inner10_lower
#print axioms inner11_lower
end WuSource.SrcFour
