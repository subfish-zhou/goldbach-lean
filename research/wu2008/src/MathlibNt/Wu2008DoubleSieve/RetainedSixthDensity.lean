import MathlibNt.Wu2008DoubleSieve.FixedCoefficientHLowerEnclosure

namespace Wu2008DoubleSieve.RetainedSixthDensity
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence
open FixedCoefficientScalarEnclosure FixedCoefficientUpperEnclosure
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open scoped Interval

noncomputable def lam : ℝ := 1/2-2*a
noncomputable def m : ℝ := lam-b
noncomputable def zmax : ℝ := 1/2-a-b
noncomputable def error : ℝ := (zmax/a-4)^3/36
noncomputable def chord (l r t : ℝ) : ℝ := (l+r-t)/(l*r)

 theorem reciprocal_chord {l r t : ℝ} (hl : 0 < l) (ht : l ≤ t) (hr : t ≤ r) :
    1/t ≤ chord l r t := by
  have ht0 := hl.trans_le ht
  have hr0 := ht0.trans_le hr
  apply (div_le_iff₀ ht0).2
  unfold chord
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (mul_pos hl hr0)).2
  have h := mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hr)
  nlinarith

 theorem upperLog_gap {q : ℝ} (hq : 1 ≤ q) :
    (q-1)*(q+1)/(2*q)-upperLog q = (q-1)^3/(3*q*(q+1)) := by
  have hq0 : q ≠ 0 := by linarith
  have hq1 : q+1 ≠ 0 := by linarith
  unfold upperLog
  field_simp
  ring

 theorem lower_log_error {u : ℝ} (hu : 2 ≤ u) (hum : u ≤ zmax/a) :
    wuLowerCoefficient u ≤ log (u-1)+error := by
  have hm4 : 4 ≤ zmax/a := by norm_num [zmax,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  have hm5 : zmax/a ≤ 5 := by norm_num [zmax,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  have he : 0 ≤ error := by unfold error; positivity
  by_cases hu4 : u ≤ 4
  · have hh : wuLowerCoefficient u = log (u-1) := jr1965f_normalized_firstInterval hu hu4
    rw [hh]
    linarith
  · have hu4' : 4 ≤ u := le_of_lt (lt_of_not_ge hu4)
    have hh := lower_quartic_upper hu4' (hum.trans hm5)
    have hp := pow_le_pow_left₀ (show 0 ≤ u-4 by linarith) (show u-4 ≤ zmax/a-4 by linarith) 3
    unfold quartic error at *
    nlinarith [sq_nonneg ((u-4)^2)]

 theorem moving_geometry {x : ℝ} (hx : x ∈ Icc a b) : b ≤ lam-x ∧ lam-x ≤ s :=
  DynamicSixthEnvelope.moving_geometry hx

 theorem retained_region {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc b (lam-x)) :
    truncatedSixthLowerRegion 0 x y := by
  refine ⟨hx.1,hx.2,hy.1,hy.2.trans (moving_geometry hx).2,?_⟩
  dsimp [truncatedSixthLowerC]
  have hh : y ≤ 1/2-2*a-x := hy.2
  linarith

 theorem tail_zero {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc (lam-x) s) :
    truncatedSixthZeroDeltaRegular 0 (x,y) = 0 := by
  have hby : b ≤ y := (moving_geometry hx).1.trans hy.1
  rw [truncatedSixthZeroDelta_regular_eq (by norm_num) hx ⟨hby,hy.2⟩]
  split_ifs with hr
  · have he : truncatedSixthLowerS 0 x y = 2 := by
      apply (div_eq_iff truncatedSixthLower_parameters.1.ne').2
      have hh := hr.2.2.2.2
      dsimp [truncatedSixthLowerC] at hh ⊢
      have hy1 : 1/2-2*a-x ≤ y := hy.1
      linarith
    have hz : wuLowerCoefficient 2 = log (2-1) :=
      jr1965f_normalized_firstInterval (by norm_num) (by norm_num)
    rw [he,hz]
    norm_num
  · rfl

noncomputable def principal (x y : ℝ) : ℝ :=
  (lam-x-y)*(x+y-b)/(2*a^2*m)+error/(2*a)
noncomputable def correction (x y : ℝ) : ℝ :=
  (lam-x-y)^3/(3*a*m*zmax^2)

 theorem normalized_upper {z : ℝ} (hz : 2*a ≤ z) (hzm : z ≤ zmax) :
    wuLowerCoefficient (z/a)/z ≤
      (z-2*a)*(m+2*a-z)/(2*a^2*m)+error/(2*a) - (z-2*a)^3/(3*a*m*zmax^2) := by
  have ha := truncatedSixthLower_parameters.1
  have hm : 0 < m := by norm_num [m,lam,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  have hz0 : 0 < z := by linarith
  have hzma : zmax-a = m := by dsimp [zmax,m,lam]; ring
  have hza : a ≤ z-a := by linarith
  have hzam : z-a ≤ m := by linarith
  have hza0 := ha.trans_le hza
  have hq : 1 ≤ z/a-1 := by apply (le_sub_iff_add_le).2; apply (le_div_iff₀ ha).2; linarith
  have hl := lower_log_error ((le_div_iff₀ ha).2 hz) ((div_le_div_iff_of_pos_right ha).2 hzm)
  have hR := log_upper hq
  have hrec := reciprocal_chord ha hza hzam
  have hn : 0 ≤ z-2*a := by linarith
  have he : 0 ≤ error := by norm_num [error,zmax,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  have hmain := mul_le_mul_of_nonneg_left hrec (div_nonneg hn (by positivity : 0 ≤ 2*a))
  have hErr := div_le_div_of_nonneg_left he (by positivity : 0 < 2*a) hz
  have hden : (z-a)*z^2 ≤ m*zmax^2 := mul_le_mul hzam
    (pow_le_pow_left₀ hz0.le hzm 2) (sq_nonneg z) hm.le
  have hc := div_le_div_of_nonneg_left (pow_nonneg hn 3)
    (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 3) ha) (mul_pos hza0 (sq_pos_of_pos hz0)))
    (mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ 3*a))
  have hid : upperLog (z/a-1)/z =
      ((z-2*a)/(2*a))*(1/(z-a)) - (z-2*a)^3/(3*a*((z-a)*z^2)) := by
    have hq0 : z/a-1 ≠ 0 := by linarith
    have hq1 : z/a-1+1 ≠ 0 := by linarith
    have hh := upperLog_gap hq
    have hzdiv : z/a ≠ 0 := div_ne_zero hz0.ne' ha.ne'
    unfold upperLog
    field_simp [ha.ne',hz0.ne',hza0.ne',hq0,hq1,hzdiv]
    ring
  have hdiv := div_le_div_of_nonneg_right (hl.trans (add_le_add hR (le_refl error))) hz0.le
  rw [add_div,hid] at hdiv
  have hmainEq : ((z-2*a)/(2*a))*chord a m (z-a) =
      (z-2*a)*(m+2*a-z)/(2*a^2*m) := by unfold chord; ring
  rw [hmainEq] at hmain
  have hcEq : (z-2*a)^3/(3*a*(m*zmax^2)) = (z-2*a)^3/(3*a*m*zmax^2) := by ring
  rw [hcEq] at hc
  linarith

noncomputable def polynomial (x y : ℝ) : ℝ :=
  principal x y*chord a b x*chord b s y-correction x y/(b*s)

 theorem retained_density_upper {x y : ℝ} (hx : x ∈ Icc a b)
    (hy : y ∈ Icc b (lam-x)) :
    truncatedSixthZeroDeltaRegular 0 (x,y) ≤ polynomial x y := by
  have ha := truncatedSixthLower_parameters.1
  have hb := ha.trans truncatedSixthLower_parameters.2.1
  have hs := hb.trans truncatedSixthLower_parameters.2.2.1
  have hx0 := ha.trans_le hx.1
  have hy0 := hb.trans_le hy.1
  have hys := hy.2.trans (moving_geometry hx).2
  have hr := retained_region hx hy
  have hz : 2*a ≤ 1/2-x-y := by have hh := hy.2; dsimp [lam] at hh; linarith
  have hzm : 1/2-x-y ≤ zmax := by dsimp [zmax]; linarith [hx.1,hy.1]
  have hh := normalized_upper hz hzm
  have heq : (1/2-x-y-2*a)*(m+2*a-(1/2-x-y))/(2*a^2*m)+error/(2*a) -
      (1/2-x-y-2*a)^3/(3*a*m*zmax^2) = principal x y-correction x y := by
    dsimp [principal,correction,m,lam]; ring
  rw [heq] at hh
  have hhdiv := div_le_div_of_nonneg_right hh (mul_pos hx0 hy0).le
  have hn : 0 ≤ principal x y := by
    have hm : 0 < m := by norm_num [m,lam,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
    have ht : 0 ≤ lam-x-y := by linarith [hy.2]
    have hw : 0 ≤ x+y-b := by linarith [hy.1]
    have he : 0 ≤ error := by norm_num [error,zmax,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
    unfold principal
    positivity
  have hc : 0 ≤ correction x y := by
    have ht : 0 ≤ lam-x-y := by linarith [hy.2]
    have hm : 0 < m := by norm_num [m,lam,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
    unfold correction
    positivity
  have hcx := reciprocal_chord ha hx.1 hx.2
  have hcy := reciprocal_chord hb hy.1 hys
  have hxy := mul_le_mul hcx hcy (by positivity : 0 ≤ 1/y)
    ((by positivity : 0 ≤ 1/x).trans hcx)
  have hpr := mul_le_mul_of_nonneg_left hxy hn
  have hco := div_le_div_of_nonneg_left hc (mul_pos hx0 hy0)
    (mul_le_mul hx.2 hys hy0.le hb.le)
  rw [truncatedSixthZeroDelta_regular_eq (by norm_num) hx ⟨hy.1,hys⟩,if_pos hr]
  simp only [truncatedSixthLowerS,truncatedSixthLowerC,sub_zero]
  change wuLowerCoefficient ((1/2-x-y)/a)/(x*y*(1/2-x-y)) ≤ polynomial x y
  have hid : wuLowerCoefficient ((1/2-x-y)/a)/(x*y*(1/2-x-y)) =
    (wuLowerCoefficient ((1/2-x-y)/a)/(1/2-x-y))/(x*y) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
  rw [hid]
  apply hhdiv.trans
  unfold polynomial
  rw [sub_div]
  have he : principal x y*(1/x*(1/y)) = principal x y/(x*y) := by ring
  rw [he] at hpr
  nlinarith only [hpr,hco]

end Wu2008DoubleSieve.RetainedSixthDensity
