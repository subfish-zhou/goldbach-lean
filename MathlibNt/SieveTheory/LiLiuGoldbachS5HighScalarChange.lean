import MathlibNt.SieveTheory.LiLiuGoldbachS5HighScalarAnalytic
open MeasureTheory Set
open scoped Interval
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def highU (x : ℝ) : ℝ := 1 - (2/3)/(1-x)

theorem highU_maps {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (7/27)) :
    highU x ∈ Icc (1/10 : ℝ) (1/3) := by
  have hp : 0 < 1-x := by linarith [hx.2]
  dsimp [highU]
  constructor
  · have h : (2/3 : ℝ)/(1-x) ≤ 9/10 := (div_le_iff₀ hp).2 (by linarith [hx.2])
    linarith
  · have h : (2/3 : ℝ) ≤ (2/3)/(1-x) := (le_div_iff₀ hp).2 (by linarith [hx.1])
    linarith

theorem highF_continuous : ContinuousOn highF (Icc (0 : ℝ) (7/27)) := by
  have hd : ∀ x ∈ Icc (0 : ℝ) (7/27), 1-x ≠ 0 := by
    intro x hx; linarith [hx.2]
  apply ContinuousOn.mul
    (((continuousOn_const.add continuousOn_id).div
      (continuousOn_const.sub continuousOn_id) hd).log ?_)
    (continuousOn_const.div (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)) ?_)
  · intro x hx
    change (1+x)/(1-x) ≠ 0
    exact div_ne_zero (by linarith [hx.1]) (hd x hx)
  · intro x hx
    change 1-3*x ≠ 0
    linarith [hx.2]

theorem high_change_integral :
    goldbachB9HighMainIntegral = ∫ x in (0 : ℝ)..(7/27), highF x := by
  let f : ℝ → ℝ := fun u => Real.log (2-3*u)/(u*(1-u))
  have hd : ∀ x ∈ uIcc (0 : ℝ) (7/27),
      HasDerivAt highU (-(2/3)/(1-x)^2) x := by
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 7/27)] at hx
    have hp : 1-x ≠ 0 := by linarith [hx.2]
    change HasDerivAt (fun x : ℝ => 1-(2/3)/(1-x)) _ x
    convert! ((((hasDerivAt_id x).const_sub 1).inv hp).const_mul (2/3)).const_sub 1 using 1
    norm_num [id, one_div, div_eq_mul_inv]
  have hj : ContinuousOn (fun x : ℝ => -(2/3)/(1-x)^2) (uIcc (0 : ℝ) (7/27)) := by
    apply continuousOn_const.div ((continuousOn_const.sub continuousOn_id).pow 2)
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 7/27)] at hx
    exact pow_ne_zero 2 (by change 1-x ≠ 0; linarith [hx.2])
  have hf : ContinuousOn f (Icc (1/10 : ℝ) (1/3)) := by
    apply ContinuousOn.div
      ((continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).log ?_)
      (continuousOn_id.mul (continuousOn_const.sub continuousOn_id)) ?_
    · intro u hu
      change 2-3*u ≠ 0
      linarith [hu.2]
    · intro u hu
      change u*(1-u) ≠ 0
      exact mul_ne_zero (by linarith [hu.1]) (by linarith [hu.2])
  have hc : ContinuousOn f (highU '' uIcc (0 : ℝ) (7/27)) := by
    apply hf.mono
    rintro u ⟨x, hx, rfl⟩
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 7/27)] at hx
    exact highU_maps hx
  have h := intervalIntegral.integral_comp_mul_deriv' hd hj hc
  have he : (∫ x in (0 : ℝ)..(7/27), f (highU x) * (-(2/3)/(1-x)^2)) =
      ∫ x in (0 : ℝ)..(7/27), -highF x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 7/27)] at hx
    have hp : 1-x ≠ 0 := by linarith [hx.2]
    have hq : 1-3*x ≠ 0 := by linarith [hx.2]
    have hqr : 1-x*3 ≠ 0 := by linarith [hx.2]
    have heq : 2-3*highU x = (1+x)/(1-x) := by
      dsimp [highU]
      field_simp
      ring
    dsimp only [f, highF]
    rw [heq]
    dsimp [highU]
    generalize Real.log ((1+x)/(1-x)) = l
    field_simp [hp, hq, hqr]
    ring_nf
    field_simp [hqr]
    ring
  change (∫ x in (0 : ℝ)..(7/27), f (highU x) * (-(2/3)/(1-x)^2)) = _ at h
  rw [he, intervalIntegral.integral_neg] at h
  norm_num [highU] at h
  have hs : goldbachB9HighMainIntegral =
      ∫ u in (1/10 : ℝ)..(1/3), f u :=
    goldbachB9SubintervalIntegral_eq_single (by norm_num) (by norm_num) le_rfl
  rw [hs]
  rw [intervalIntegral.integral_symm (a := (1/10 : ℝ)) (b := 1/3)] at h
  exact neg_inj.mp h.symm

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig