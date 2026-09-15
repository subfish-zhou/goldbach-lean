import MathlibNt.Wu2008DoubleSieve.RetainedSixthDensity

namespace Wu2008DoubleSieve.RefinedRetainedDensity
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence
open FixedCoefficientUpperEnclosure
open RetainedSixthDensity (lam m zmax error correction moving_geometry retained_region tail_zero)
open scoped Interval

/-- The exact chord residual, bounded once by its right denominator endpoint. -/
noncomputable def reciprocalUpper (l r t : ℝ) : ℝ :=
  RetainedSixthDensity.chord l r t-(t-l)*(r-t)/(l*r^2)
noncomputable def reciprocalLower (r t : ℝ) : ℝ := (2*r-t)/r^2

 theorem reciprocal_upper {l r t : ℝ} (hl : 0 < l) (ht : l ≤ t) (hr : t ≤ r) :
    1/t ≤ reciprocalUpper l r t := by
  have ht0 := hl.trans_le ht
  have hr0 := ht0.trans_le hr
  have hid : reciprocalUpper l r t*t-1 = (t-l)*(r-t)^2/(l*r^2) := by
    unfold reciprocalUpper RetainedSixthDensity.chord
    field_simp
    ring
  have hn : 0 ≤ (t-l)*(r-t)^2/(l*r^2) := by positivity
  apply (div_le_iff₀ ht0).2
  linarith

 theorem reciprocal_lower {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    reciprocalLower r t ≤ 1/t := by
  have hid : 1-reciprocalLower r t*t = (r-t)^2/r^2 := by
    unfold reciprocalLower
    field_simp
    ring
  have hn : 0 ≤ (r-t)^2/r^2 := by positivity
  apply (le_div_iff₀ ht).2
  linarith

noncomputable def principal (x y : ℝ) : ℝ :=
  (lam-x-y)/(2*a)*reciprocalUpper a m (1/2-a-x-y)+error/(2*a)
noncomputable def polynomial (x y : ℝ) : ℝ :=
  principal x y*reciprocalUpper a b x*reciprocalUpper b s y-
    correction x y*reciprocalLower b x*reciprocalLower s y

 theorem normalized_upper {z : ℝ} (hz : 2*a ≤ z) (hzm : z ≤ zmax) :
    wuLowerCoefficient (z/a)/z ≤
      ((z-2*a)/(2*a))*reciprocalUpper a m (z-a)+error/(2*a) - (z-2*a)^3/(3*a*m*zmax^2) := by
  have ha := truncatedSixthLower_parameters.1
  have hm : 0 < m := by norm_num [m,lam,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  have hz0 : 0 < z := by linarith
  have hzma : zmax-a = m := by dsimp [zmax,m,lam]; ring
  have hza : a ≤ z-a := by linarith
  have hzam : z-a ≤ m := by linarith
  have hza0 := ha.trans_le hza
  have hq : 1 ≤ z/a-1 := by apply (le_sub_iff_add_le).2; apply (le_div_iff₀ ha).2; linarith
  have hl := RetainedSixthDensity.lower_log_error ((le_div_iff₀ ha).2 hz)
    ((div_le_div_iff_of_pos_right ha).2 hzm)
  have hR := log_upper hq
  have hrec := reciprocal_upper ha hza hzam
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
    have hzdiv : z/a ≠ 0 := div_ne_zero hz0.ne' ha.ne'
    unfold upperLog
    field_simp [ha.ne',hz0.ne',hza0.ne',hq0,hq1,hzdiv]
    ring
  have hdiv := div_le_div_of_nonneg_right (hl.trans (add_le_add hR (le_refl error))) hz0.le
  rw [add_div,hid] at hdiv
  have hcEq : (z-2*a)^3/(3*a*(m*zmax^2)) = (z-2*a)^3/(3*a*m*zmax^2) := by ring
  rw [hcEq] at hc
  linarith

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
  have heq : ((1/2-x-y-2*a)/(2*a))*reciprocalUpper a m (1/2-x-y-a)+error/(2*a) -
      (1/2-x-y-2*a)^3/(3*a*m*zmax^2) = principal x y-correction x y := by
    dsimp [principal,correction,m,lam,reciprocalUpper,RetainedSixthDensity.chord]; ring
  rw [heq] at hh
  have hhdiv := div_le_div_of_nonneg_right hh (mul_pos hx0 hy0).le
  have hn : 0 ≤ principal x y := by
    have ht : 0 ≤ lam-x-y := by linarith [hy.2]
    have hw : a ≤ 1/2-a-x-y := by linarith
    have hwm : 1/2-a-x-y ≤ m := by dsimp [m,lam,zmax] at *; linarith
    have hww := reciprocal_upper ha hw hwm
    have hw0 : 0 < 1/2-a-x-y := ha.trans_le hw
    have hrn : 0 ≤ reciprocalUpper a m (1/2-a-x-y) := (by positivity : 0 ≤ 1/(1/2-a-x-y)).trans hww
    have he : 0 ≤ error := by norm_num [error,zmax,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
    unfold principal
    positivity
  have hc : 0 ≤ correction x y := by
    have ht : 0 ≤ lam-x-y := by linarith [hy.2]
    have hm : 0 < m := by norm_num [m,lam,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
    unfold correction
    positivity
  have hcx := reciprocal_upper ha hx.1 hx.2
  have hcy := reciprocal_upper hb hy.1 hys
  have hxy := mul_le_mul hcx hcy (by positivity : 0 ≤ 1/y)
    ((by positivity : 0 ≤ 1/x).trans hcx)
  have hpr := mul_le_mul_of_nonneg_left hxy hn
  have hlnx : 0 ≤ reciprocalLower b x := by
    unfold reciprocalLower
    exact div_nonneg (by linarith [hx.2]) (sq_nonneg b)
  have hlny : 0 ≤ reciprocalLower s y := by
    unfold reciprocalLower
    exact div_nonneg (by linarith) (sq_nonneg s)
  have hlxy := mul_le_mul (reciprocal_lower hb hx0) (reciprocal_lower hs hy0) hlny
    (by positivity : 0 ≤ 1/x)
  have hco := mul_le_mul_of_nonneg_left hlxy hc
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
  have he (v : ℝ) : v*(1/x*(1/y)) = v/(x*y) := by ring
  rw [he] at hpr hco
  nlinarith only [hpr,hco]

end Wu2008DoubleSieve.RefinedRetainedDensity
