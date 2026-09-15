import E10FourMajorData

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open FourRoughClosedMass ClassicalLogFourBounds

namespace WuTarget.E10FourMajor

theorem anchored_nonneg {f g : ℝ → ℝ} {L s : ℝ} (hs : s ∈ Icc 0 L)
    (hf : f 0 = 0) (hd : ∀ x ∈ Icc 0 L, HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Icc 0 L, 0 ≤ g x) : 0 ≤ f s := by
  have hm : MonotoneOn f (Icc 0 L) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 L)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx => hg x (interior_subset hx))
  have h := hm ⟨le_refl 0,hs.1.trans hs.2⟩ hs hs.1
  rwa [hf] at h

theorem exp_cubic_remainder {B L s : ℝ} (hs : s ∈ Icc 0 L)
    (hB : exp L ≤ B) :
    exp s ≤ 1+s+s^2/2+s^3/6+B*s^4/24 := by
  have h0 (x : ℝ) (hx : x ∈ Icc 0 L) : 0 ≤ B-exp x :=
    sub_nonneg.mpr ((exp_le_exp.mpr hx.2).trans hB)
  have h1 (x : ℝ) (hx : x ∈ Icc 0 L) : 0 ≤ 1+B*x-exp x := by
    apply anchored_nonneg (f := fun x => 1+B*x-exp x) hx (by simp)
      (fun y _ => ?_) h0
    convert ((hasDerivAt_const y (1 : ℝ)).add
      ((hasDerivAt_id y).const_mul B)).sub (hasDerivAt_exp y) using 1 <;>
      first | rfl | (dsimp; ring)
  have h2 (x : ℝ) (hx : x ∈ Icc 0 L) : 0 ≤ 1+x+B*x^2/2-exp x := by
    apply anchored_nonneg (f := fun x => 1+x+B*x^2/2-exp x) hx (by simp)
      (fun y _ => ?_) h1
    convert (((hasDerivAt_const y (1 : ℝ)).add (hasDerivAt_id y)).add
      (((hasDerivAt_id y).pow 2).const_mul B |>.div_const 2)).sub
        (hasDerivAt_exp y) using 1 <;> first | rfl | (dsimp; ring)
  have h3 (x : ℝ) (hx : x ∈ Icc 0 L) : 0 ≤ 1+x+x^2/2+B*x^3/6-exp x := by
    apply anchored_nonneg (f := fun x => 1+x+x^2/2+B*x^3/6-exp x) hx (by simp)
      (fun y _ => ?_) h2
    convert ((((hasDerivAt_const y (1 : ℝ)).add (hasDerivAt_id y)).add
      (((hasDerivAt_id y).pow 2).div_const 2)).add
      (((hasDerivAt_id y).pow 3).const_mul B |>.div_const 6)).sub
        (hasDerivAt_exp y) using 1 <;> first | rfl | (dsimp; ring)
  have h4 : 0 ≤ 1+s+s^2/2+s^3/6+B*s^4/24-exp s := by
    apply anchored_nonneg (f := fun x => 1+x+x^2/2+x^3/6+B*x^4/24-exp x) hs (by simp)
      (fun y _ => ?_) h3
    convert (((((hasDerivAt_const y (1 : ℝ)).add (hasDerivAt_id y)).add
      (((hasDerivAt_id y).pow 2).div_const 2)).add
      (((hasDerivAt_id y).pow 3).div_const 6)).add
      (((hasDerivAt_id y).pow 4).const_mul B |>.div_const 24)).sub
        (hasDerivAt_exp y) using 1 <;> first | rfl | (dsimp; ring)
  linarith only [h4]

def reciprocalCap (y : ℝ) : ℝ :=
  ∑ i : Fin 5, recipCoeff i*(FourLogAffine.ell y)^i.val

theorem reciprocal_upper {y : ℝ} (hy : y ∈ Icc alpha beta) :
    1/y ≤ reciprocalCap y := by
  have ha := fixed_geometry_major.1
  have hb := fixed_geometry_major.2.2.2.2.2.1
  have hy0 := ha.trans_le hy.1
  have hs : FourLogAffine.ell y ∈ Icc 0 tailLog := by
    refine ⟨FourLogAffine.ell_nonneg hy.1 hy.2,?_⟩
    unfold FourLogAffine.ell tailLog
    linarith only [log_le_log ha hy.1]
  have heL : exp tailLog = beta/alpha := by
    rw [tailLog,exp_sub,exp_log hb,exp_log ha]
  have hey : exp (FourLogAffine.ell y) = beta/y := by
    rw [FourLogAffine.ell,exp_sub,exp_log hb,exp_log hy0]
  have ht := exp_cubic_remainder hs heL.le
  rw [hey] at ht
  have hp := div_le_div_of_nonneg_right ht hb.le
  have hlhs : beta/y/beta = 1/y := by field_simp
  rw [hlhs] at hp
  unfold reciprocalCap
  simp only [Fin.sum_univ_succ,recipCoeff,Fin.val_succ,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.coe_ofNat_eq_mod]
  norm_num only [pow_zero,pow_one]
  convert hp using 1 <;> first | rfl | (field_simp; ring)

theorem cross_tangent {z : ℝ} (hz : z ∈ Icc alpha beta) :
    log (lam-z)-log beta ≤ crossCap+slope*FourLogAffine.ell z := by
  have hb := fixed_geometry_major.2.2.2.2.2.1
  have hz0 := fixed_geometry_major.1.trans_le hz.1
  have hbase := fixed_geometry_major.2.2.2.2.2.2.1
  have hden := fixed_geometry_major.2.2.2.2.2.2.2
  have hlz : 0 < lam-z := by
    linarith only [fixed_geometry_major.2.2.2.2.1,hz.2,hb]
  have ht := log_le_sub_one_of_pos (div_pos hlz hden)
  rw [log_div hlz.ne' hden.ne'] at ht
  have ht' : log (lam-z)-log (lam-z0) ≤ (z0-z)/(lam-z0) := by
    convert ht using 1
    field_simp
    ring
  have hzlog := log_le_sub_one_of_pos (div_pos hz0 hbase)
  rw [log_div hz0.ne' hbase.ne'] at hzlog
  have hm := mul_le_mul_of_nonneg_left hzlog slope_pos.le
  have hid : slope*(z/z0-1) = (z-z0)/(lam-z0) := by
    unfold slope
    field_simp
  rw [hid] at hm
  have htangent :
      log (lam-z)-log beta ≤
        log ((lam-z0)/beta)-slope*log (beta/z0)+slope*FourLogAffine.ell z := by
    rw [log_div hden.ne' hb.ne',log_div hb.ne' hbase.ne']
    unfold FourLogAffine.ell
    ring_nf at ht' hm ⊢
    linarith only [ht',hm]
  have hbc : (1 : ℝ) ≤ (lam-z0)/beta := by
    apply (le_div_iff₀ hb).mpr
    linarith only [fixed_geometry_major.2.2.2.1,fixed_geometry_major.2.2.2.2.1]
  have hzb : (1 : ℝ) ≤ beta/z0 :=
    (le_div_iff₀ hbase).mpr (by simpa using fixed_geometry_major.2.2.2.1)
  have hu := SharpLogRecurrence.log_upper hbc
  have hl := mul_le_mul_of_nonneg_left (SharpLogRecurrence.log_lower hzb) slope_pos.le
  unfold crossCap
  linarith only [htangent,hu,hl]

end WuTarget.E10FourMajor
