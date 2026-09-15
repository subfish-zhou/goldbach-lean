import E05SixthMajorInner

noncomputable section
open Real Set MeasureTheory
open Wu2008DoubleSieve
open Wu2008DoubleSieve.PositiveSixthFTC
open Wu2008DoubleSieve.DynamicSixthEnvelope
open Wu2008DoubleSieve.SharpLogRecurrence
open Wu2008DoubleSieve.SharpMassBalance
open Wu2008DoubleSieve.ClassicalLossBottleneck
open scoped Interval

namespace WuTarget.E05SixthMajor

theorem strengthened_denominator {x y : ℝ} (hx : x ∈ Icc a b)
    (hy : y ∈ Icc b (lam-x)) :
    (1+10*(y-b))*(x*y*(1/2-x-y)^6) ≤ E05Sixth.denominatorCap := by
  have hg := Phase25.mask_geometry hx hy
  have hc : 1/2-x-b ≤ z0 := by unfold z0; linarith [hx.1]
  have hfixed : z0*(1+10*b) ≤ 6*b ∧ 20*z0-7-70*b ≤ 0 := by
    norm_num [z0,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  have hd (t : ℝ) :
      HasDerivAt (fun t : ℝ => (1+10*(t-b))*t*(1/2-x-t)^6)
        ((1/2-x-t)^5*
          ((1/2-x-b)*(1+10*b)-6*b+
            (t-b)*(20*(1/2-x-b)-7-70*b)-80*(t-b)^2)) t := by
    convert (((((hasDerivAt_id t).sub_const b).const_mul 10).const_add 1).mul
      (hasDerivAt_id t)).mul
        (((hasDerivAt_const t (1/2-x)).sub (hasDerivAt_id t)).pow 6) using 1 <;>
      first | rfl | (dsimp; ring)
  have hm : AntitoneOn (fun t : ℝ => (1+10*(t-b))*t*(1/2-x-t)^6)
      (Icc b (lam-x)) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (by fun_prop) (fun t _ => (hd t).hasDerivWithinAt)
      (fun t ht => by
        have ht' : t ∈ Icc b (lam-x) := interior_subset ht
        have hgeom := Phase25.mask_geometry hx ht'
        have hconst : (1/2-x-b)*(1+10*b)-6*b ≤ 0 := by
          have hp := mul_le_mul_of_nonneg_right hc
            (show 0 ≤ 1+10*b by linarith [geometry.2.2.1])
          linarith only [hp,hfixed.1]
        have hlin : 20*(1/2-x-b)-7-70*b ≤ 0 := by linarith only [hc,hfixed.2]
        have hprod := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht'.1) hlin
        apply mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hgeom.2.2.2.1.le 5)
        nlinarith only [hconst,hprod,sq_nonneg (t-b)])
  have hbmem : b ∈ Icc b (lam-x) := ⟨le_rfl,(moving_geometry hx).1⟩
  have hpoint := mul_le_mul_of_nonneg_left (hm hbmem hy hy.1) hg.1.le
  have hbase := E05Sixth.denominator_bound hx hbmem
  norm_num only [sub_self,mul_zero,add_zero,one_mul] at hpoint
  nlinarith only [hpoint,hbase]

theorem eighth_denominator {x y : ℝ} (hx : x ∈ Icc a b)
    (hy : y ∈ Icc b (lam-x)) :
    x*y*(1/2-x-y)^8 ≤ E05Sixth.denominatorCap*z0^2 := by
  have hg := Phase25.mask_geometry hx hy
  have hz : 1/2-x-y ≤ z0 := by unfold z0; linarith [hx.1,hy.1]
  have hpow := pow_le_pow_left₀ hg.2.2.2.1.le hz 2
  have hp := mul_le_mul (E05Sixth.denominator_bound hx hy) hpow
    (sq_nonneg _) E05Sixth.denominatorCap_pos.le
  calc
    _ = (x*y*(1/2-x-y)^6)*(1/2-x-y)^2 := by ring
    _ ≤ _ := hp

def densityCorrection (x y : ℝ) : ℝ :=
  (2/5)*(lam-x-y)^5*(1+10*(y-b))/E05Sixth.denominatorCap+
    (2/7)*(lam-x-y)^7/(E05Sixth.denominatorCap*z0^2)

theorem correction_le_terms {x y : ℝ} (hx : x ∈ Icc a b)
    (hy : y ∈ Icc b (lam-x)) :
    densityCorrection x y ≤
      (2/5)*(lam-x-y)^5/(x*y*(1/2-x-y)^6)+
        (2/7)*(lam-x-y)^7/(x*y*(1/2-x-y)^8) := by
  have hg := Phase25.mask_geometry hx hy
  have hw : 0 ≤ lam-x-y := by linarith [hy.2]
  have hrat : (1+10*(y-b))/E05Sixth.denominatorCap ≤
      1/(x*y*(1/2-x-y)^6) := by
    apply (div_le_div_iff₀ E05Sixth.denominatorCap_pos
      (mul_pos (mul_pos hg.1 hg.2.1) (pow_pos hg.2.2.2.1 6))).2
    simpa only [one_mul] using strengthened_denominator hx hy
  have h5 := mul_le_mul_of_nonneg_left hrat
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2/5) (pow_nonneg hw 5))
  have h7 := div_le_div_of_nonneg_left
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2/7) (pow_nonneg hw 7))
    (mul_pos (mul_pos hg.1 hg.2.1) (pow_pos hg.2.2.2.1 8)) (eighth_denominator hx hy)
  unfold densityCorrection
  convert add_le_add h5 h7 using 1 <;> ring

theorem seventh_kernel_identity {x y : ℝ} (hx : x ∈ Icc a b)
    (hy : y ∈ Icc b (lam-x)) :
    seventhLogTerm (truncatedSixthLowerS 0 x y-1)/(x*y*(1/2-x-y)) =
      (2/7)*(lam-x-y)^7/(x*y*(1/2-x-y)^8) := by
  have hg := Phase25.mask_geometry hx hy
  have hp := truncatedSixthLower_parameters
  have hz' : 1-x*2-y*2 ≠ 0 := by linarith [hg.2.2.2.1]
  unfold seventhLogTerm truncatedSixthLowerS truncatedSixthLowerC lam
  simp only [sub_zero]
  field_simp [hp.1.ne',hg.1.ne',hg.2.1.ne',hg.2.2.2.1.ne',hz']
  ring

theorem density_correction_paid {x y : ℝ} (hx : x ∈ Icc a b)
    (hy : y ∈ Icc b (lam-x)) :
    Phase25.exactKernel x y+densityCorrection x y ≤ sixthLogRegular x y := by
  have hg := Phase25.mask_geometry hx hy
  have hu : 2 ≤ truncatedSixthLowerS 0 x y := by
    apply (le_div_iff₀ truncatedSixthLower_parameters.1).2
    change 2*truncatedSixthLowerAlpha ≤ 1/2-0-x-y
    simpa only [sub_zero] using hg.2.2.2.2
  have hl := div_le_div_of_nonneg_right (log_seventh_lower (by linarith : 1 ≤
    truncatedSixthLowerS 0 x y-1)) (mul_pos (mul_pos hg.1 hg.2.1) hg.2.2.2.1).le
  rw [add_div,← E05Sixth.fifth_kernel_identity hx hy,seventh_kernel_identity hx hy,
    ← sixth_log_retained hx hy] at hl
  linarith only [hl,correction_le_terms hx hy]

def densityInner (x : ℝ) : ℝ :=
  E05Sixth.correctionInner x+
    (2/21)*(lam-x-b)^7/E05Sixth.denominatorCap+
    (1/28)*(lam-x-b)^8/(E05Sixth.denominatorCap*z0^2)

def fifthExtraCredit : ℝ :=
  ((lam-a-b)^8-(lam-2*b)^8)/(21*E05Sixth.denominatorCap)
def seventhCredit : ℝ :=
  ((lam-a-b)^9-(lam-2*b)^9)/(63*E05Sixth.denominatorCap*z0^2)

theorem density_inner_ftc (x : ℝ) :
    (∫ y in b..(lam-x), densityCorrection x y) = densityInner x := by
  have hd (y : ℝ) (_hy : y ∈ uIcc b (lam-x)) :
      HasDerivAt (fun y : ℝ =>
        -(1/15)*(lam-x-y)^6/E05Sixth.denominatorCap-
        (2/3)*(lam-x-b)*(lam-x-y)^6/E05Sixth.denominatorCap+
        (4/7)*(lam-x-y)^7/E05Sixth.denominatorCap-
        (1/28)*(lam-x-y)^8/(E05Sixth.denominatorCap*z0^2))
        (densityCorrection x y) y := by
    have hw := (hasDerivAt_const y (lam-x)).sub (hasDerivAt_id y)
    convert (((((hw.pow 6).const_mul (-(1/15))).div_const E05Sixth.denominatorCap).sub
      (((hw.pow 6).const_mul ((2/3)*(lam-x-b))).div_const E05Sixth.denominatorCap)).add
      (((hw.pow 7).const_mul (4/7)).div_const E05Sixth.denominatorCap)).sub
      (((hw.pow 8).const_mul (1/28)).div_const (E05Sixth.denominatorCap*z0^2)) using 1 <;>
      first | rfl | (dsimp [densityCorrection]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by unfold densityCorrection; fun_prop :
      Continuous (densityCorrection x)).intervalIntegrable b (lam-x))]
  unfold densityInner E05Sixth.correctionInner
  simp only [sub_self,zero_pow (by decide : (6:ℕ) ≠ 0),
    zero_pow (by decide : (7:ℕ) ≠ 0),zero_pow (by decide : (8:ℕ) ≠ 0),
    mul_zero,zero_div,zero_add,zero_sub]
  ring

theorem density_outer_ftc :
    (4*∫ x in a..b, densityInner x) =
      E05Sixth.sixthCredit+fifthExtraCredit+seventhCredit := by
  have hd (x : ℝ) (_hx : x ∈ uIcc a b) :
      HasDerivAt (fun x : ℝ =>
        -(lam-x-b)^7/(105*E05Sixth.denominatorCap)-
          (lam-x-b)^8/(84*E05Sixth.denominatorCap)-
          (lam-x-b)^9/(252*E05Sixth.denominatorCap*z0^2))
        (densityInner x) x := by
    have hw := ((hasDerivAt_const x lam).sub (hasDerivAt_id x)).sub_const b
    convert ((((hw.pow 7).neg.div_const (105*E05Sixth.denominatorCap)).sub
      ((hw.pow 8).div_const (84*E05Sixth.denominatorCap))).sub
      ((hw.pow 9).div_const (252*E05Sixth.denominatorCap*z0^2))) using 1 <;>
      first | rfl | (dsimp [densityInner,E05Sixth.correctionInner]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by unfold densityInner E05Sixth.correctionInner; fun_prop :
      Continuous densityInner).intervalIntegrable a b)]
  unfold E05Sixth.sixthCredit fifthExtraCredit seventhCredit
  have he : lam-b-b = lam-2*b := by ring
  rw [he]
  ring

end WuTarget.E05SixthMajor
