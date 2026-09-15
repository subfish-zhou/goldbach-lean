import WSrcFourEnclosureMassPayment

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve FourRoughClosedMass

namespace WuSource.SrcFourEnclosure

def tailGeom : ℝ := 8*(∫ x in SrcFour.outerCut..beta, outerMass x)

theorem tail_inverse {x : ℝ} (hx : SrcFour.outerCut ≤ x) :
    0 ≤ x⁻¹ ∧ x⁻¹ ≤ 9 := by
  have hd := SrcFour.outerCut_pos
  have hx0 := hd.trans_le hx
  refine ⟨inv_nonneg.mpr hx0.le,?_⟩
  rw [← one_div,div_le_iff₀ hx0]
  have h : (1 : ℝ) ≤ 9*SrcFour.outerCut := by
    norm_num [SrcFour.outerCut,lam,beta,truncatedSixthLowerAlpha,
      truncatedSixthLowerBeta,truncatedSixthLowerLambda]
  linarith only [h,hx]

theorem density_upper (z : ℝ) : density z ≤ 21 := by
  have h := (D_bounds (clamp_mem z)).1
  have he : density z = D (clamp z) := by unfold density D; ring
  rw [he]
  exact (le_abs_self _).trans h

theorem G_upper {y : ℝ} (hy : y ≤ beta) : G y ≤ 21*(beta-y) := by
  have h := intervalIntegral.integral_mono_on hy
    (density_continuous.intervalIntegrable (μ := volume) y beta)
    (continuous_const.intervalIntegrable (μ := volume) y beta)
    (fun z _ => density_upper z)
  simpa only [G,intervalIntegral.integral_const,smul_eq_mul,mul_comm] using h

theorem tail_linear_integral (a b C : ℝ) :
    (∫ x in a..b, C*(b-x)) = C*(b-a)^2/2 := by
  have hd (x : ℝ) : HasDerivAt (fun z : ℝ => -C*(b-z)^2/2) (C*(b-x)) x := by
    convert ((((hasDerivAt_id x).const_sub b).pow 2).const_mul (-C)).div_const 2
      using 1 <;> first | rfl | (dsimp; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((by fun_prop : Continuous (fun x : ℝ => C*(b-x))).intervalIntegrable a b)]
  ring

theorem tail_square_integral (a b C : ℝ) :
    (∫ x in a..b, C*(b-x)^2) = C*(b-a)^3/3 := by
  have hd (x : ℝ) : HasDerivAt (fun z : ℝ => -C*(b-z)^3/3) (C*(b-x)^2) x := by
    convert ((((hasDerivAt_id x).const_sub b).pow 3).const_mul (-C)).div_const 3
      using 1 <;> first | rfl | (dsimp; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((by fun_prop : Continuous (fun x : ℝ => C*(b-x)^2)).intervalIntegrable a b)]
  ring

theorem H_tail_upper {x : ℝ} (hx : x ∈ Icc SrcFour.outerCut beta) :
    H x ≤ (1701/2)*(beta-x)^2 := by
  have had : alpha ≤ SrcFour.outerCut :=
    SrcFour.geometry.1.le.trans SrcFour.geometry.2.1.le
  have h := intervalIntegral.integral_mono_on hx.2
    (H_integrand_continuous.intervalIntegrable (μ := volume) x beta)
    ((by fun_prop : Continuous (fun y : ℝ => 1701*(beta-y))).intervalIntegrable x beta)
    (fun y hy => by
      have hdy := hx.1.trans hy.1
      rw [clamp_eq ⟨had.trans hdy,hy.2⟩,div_eq_mul_inv,← inv_pow]
      have hinv := tail_inverse hdy
      have hs := pow_le_pow_left₀ hinv.1 hinv.2 2
      calc
        _ ≤ (21*(beta-y))*(9 : ℝ)^2 :=
          mul_le_mul (G_upper hy.2) hs (sq_nonneg _)
            (mul_nonneg (by norm_num) (sub_nonneg.mpr hy.2))
        _ = _ := by ring)
  rw [tail_linear_integral] at h
  unfold H
  linarith only [h]

theorem outerMass_tail_upper {x : ℝ} (hx : x ∈ Icc SrcFour.outerCut beta) :
    outerMass x ≤ (15309/2)*(beta-x)^2 := by
  have had : alpha ≤ SrcFour.outerCut :=
    SrcFour.geometry.1.le.trans SrcFour.geometry.2.1.le
  rw [outerMass,clamp_eq ⟨had.trans hx.1,hx.2⟩,div_eq_mul_inv]
  calc
    _ ≤ ((1701/2)*(beta-x)^2)*9 :=
      mul_le_mul (H_tail_upper hx) (tail_inverse hx.1).2
        (tail_inverse hx.1).1 (by positivity)
    _ = _ := by ring

theorem tailGeom_upper : tailGeom < (1/480 : ℝ) := by
  have h := intervalIntegral.integral_mono_on SrcFour.geometry.2.2.1.le
    (outerMass_continuous.intervalIntegrable (μ := volume) SrcFour.outerCut beta)
    ((by fun_prop : Continuous (fun x : ℝ =>
      (15309/2)*(beta-x)^2)).intervalIntegrable SrcFour.outerCut beta)
    (fun x hx => outerMass_tail_upper hx)
  rw [tail_square_integral] at h
  have hn : (8 : ℝ)*((15309/2)*(beta-SrcFour.outerCut)^3/3) < 1/480 := by
    norm_num [SrcFour.outerCut,lam,beta,truncatedSixthLowerAlpha,
      truncatedSixthLowerBeta,truncatedSixthLowerLambda]
  unfold tailGeom
  linarith only [h,hn]

#check @tailGeom_upper
#print axioms tailGeom_upper
end WuSource.SrcFourEnclosure
