import MathlibNt.Wu2008DoubleSieve.RefinedRetainedFTC

namespace Wu2008DoubleSieve.NaturalSplitDensity
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence
open FixedCoefficientUpperEnclosure RefinedRetainedDensity
open RetainedSixthDensity (lam m zmax error moving_geometry retained_region tail_zero)
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open scoped Interval

noncomputable def cut (x : ℝ) : ℝ := s-x
noncomputable def lowPrincipal (x y : ℝ) : ℝ :=
  (lam-x-y)/(2*a)*reciprocalUpper a (2*a) (1/2-x-y-a)
noncomputable def highPrincipal (x y : ℝ) : ℝ :=
  (lam-x-y)/(2*a)*reciprocalUpper (2*a) m (1/2-x-y-a)+error/(3*a)
noncomputable def lowCorrection (x y : ℝ) : ℝ :=
  (lam-x-y)^3/(3*a*(2*a)*(3*a)^2)
noncomputable def highCorrection (x y : ℝ) : ℝ :=
  (lam-x-y)^3/(3*a*m*zmax^2)
noncomputable def low (x y : ℝ) : ℝ :=
  lowPrincipal x y*reciprocalUpper a b x*reciprocalUpper (s-b) s y-
    lowCorrection x y*reciprocalLower b x*reciprocalLower s y
noncomputable def high (x y : ℝ) : ℝ :=
  highPrincipal x y*reciprocalUpper a b x*reciprocalUpper b (s-a) y-
    highCorrection x y*reciprocalLower b x*reciprocalLower (s-a) y

theorem cut_geometry {x : ℝ} (hx : x ∈ Icc a b) : b ≤ cut x ∧ cut x ≤ lam-x := by
  have hb : 2*b ≤ s := by norm_num [a,b,s,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerSigma]
  have ha := truncatedSixthLower_parameters.1
  constructor
  · change b ≤ s-x
    linarith [hx.2]
  · dsimp [cut,lam,s,truncatedSixthLowerSigma]
    linarith

theorem low_geometry {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc (cut x) (lam-x)) :
    y ∈ Icc b (lam-x) ∧ y ∈ Icc (s-b) s ∧ 2*a ≤ 1/2-x-y ∧ 1/2-x-y ≤ 3*a := by
  have hc := cut_geometry hx
  have hm := moving_geometry hx
  have hyl : s-x ≤ y := hy.1
  have hyu : y ≤ 1/2-2*a-x := hy.2
  refine ⟨⟨hc.1.trans hy.1,hy.2⟩,⟨?_,hy.2.trans hm.2⟩,?_,?_⟩
  · linarith [hx.2]
  · linarith
  · dsimp [s,truncatedSixthLowerSigma] at hyl; linarith

theorem high_geometry {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc b (cut x)) :
    y ∈ Icc b (lam-x) ∧ y ≤ s-a ∧ 3*a ≤ 1/2-x-y ∧ 1/2-x-y ≤ zmax := by
  have hc := cut_geometry hx
  have hyu : y ≤ s-x := hy.2
  refine ⟨⟨hy.1,hy.2.trans hc.2⟩,?_,?_,?_⟩
  · linarith [hx.1]
  · dsimp [s,truncatedSixthLowerSigma] at hyu; linarith
  · dsimp [zmax]; linarith [hx.1,hy.1]

/-- A signed normalized bound, before either reciprocal density is estimated. -/
theorem normalized {z l r Z e d : ℝ} (hz : 2*a ≤ z) (hl : 0 < l)
    (hzl : l ≤ z-a) (hzr : z-a ≤ r) (hzZ : z ≤ Z)
    (he : 0 ≤ e) (hd : 0 < d) (hdz : d ≤ z)
    (hlog : wuLowerCoefficient (z/a) ≤ log (z/a-1)+e) :
    wuLowerCoefficient (z/a)/z ≤
      (z-2*a)/(2*a)*reciprocalUpper l r (z-a)+e/d-
        (z-2*a)^3/(3*a*r*Z^2) := by
  have ha := truncatedSixthLower_parameters.1
  have hz0 : 0 < z := by linarith
  have hza0 := hl.trans_le hzl
  have hr0 := hza0.trans_le hzr
  have hq : 1 ≤ z/a-1 := by
    apply (le_sub_iff_add_le).2
    apply (le_div_iff₀ ha).2
    linarith
  have hrec := reciprocal_upper hl hzl hzr
  have hn : 0 ≤ z-2*a := by linarith
  have hmain := mul_le_mul_of_nonneg_left hrec (div_nonneg hn (by positivity : 0 ≤ 2*a))
  have herr := div_le_div_of_nonneg_left he hd hdz
  have hden : (z-a)*z^2 ≤ r*Z^2 := mul_le_mul hzr
    (pow_le_pow_left₀ hz0.le hzZ 2) (sq_nonneg z) hr0.le
  have hc := div_le_div_of_nonneg_left (pow_nonneg hn 3)
    (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 3) ha) (mul_pos hza0 (sq_pos_of_pos hz0)))
    (mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ 3*a))
  have hid : upperLog (z/a-1)/z =
      ((z-2*a)/(2*a))*(1/(z-a))-(z-2*a)^3/(3*a*((z-a)*z^2)) := by
    have hq0 : z/a-1 ≠ 0 := by linarith
    have hq1 : z/a-1+1 ≠ 0 := by linarith
    have hzdiv : z/a ≠ 0 := div_ne_zero hz0.ne' ha.ne'
    unfold upperLog
    field_simp [ha.ne',hz0.ne',hza0.ne',hq0,hq1,hzdiv]
    ring
  have hdiv := div_le_div_of_nonneg_right
    (hlog.trans (add_le_add (log_upper hq) (le_refl e))) hz0.le
  rw [add_div,hid] at hdiv
  have hcEq : (z-2*a)^3/(3*a*(r*Z^2)) = (z-2*a)^3/(3*a*r*Z^2) := by ring
  rw [hcEq] at hc
  linarith

/-- Both lower reciprocal factors are nonnegative before multiplying the correction. -/
theorem density_transport {x y L R P C : ℝ} (hx : x ∈ Icc a b)
    (hy : y ∈ Icc b (lam-x)) (hL : 0 < L) (hLy : L ≤ y) (hyR : y ≤ R)
    (hP : 0 ≤ P) (hC : 0 ≤ C)
    (hn : wuLowerCoefficient ((1/2-x-y)/a)/(1/2-x-y) ≤ P-C) :
    truncatedSixthZeroDeltaRegular 0 (x,y) ≤
      P*reciprocalUpper a b x*reciprocalUpper L R y-
        C*reciprocalLower b x*reciprocalLower R y := by
  have ha := truncatedSixthLower_parameters.1
  have hb := ha.trans truncatedSixthLower_parameters.2.1
  have hx0 := ha.trans_le hx.1
  have hy0 := hb.trans_le hy.1
  have hR := hy0.trans_le hyR
  have hys := hy.2.trans (moving_geometry hx).2
  have hhdiv := div_le_div_of_nonneg_right hn (mul_pos hx0 hy0).le
  have hcx := reciprocal_upper ha hx.1 hx.2
  have hcy := reciprocal_upper hL hLy hyR
  have hxy := mul_le_mul hcx hcy (by positivity : 0 ≤ 1/y)
    ((by positivity : 0 ≤ 1/x).trans hcx)
  have hpr := mul_le_mul_of_nonneg_left hxy hP
  have hlnx : 0 ≤ reciprocalLower b x := by
    unfold reciprocalLower
    exact div_nonneg (by linarith [hx.2]) (sq_nonneg b)
  have hlny : 0 ≤ reciprocalLower R y := by
    unfold reciprocalLower
    exact div_nonneg (by linarith) (sq_nonneg R)
  have hlnprod : 0 ≤ reciprocalLower b x*reciprocalLower R y := mul_nonneg hlnx hlny
  have hlxy := mul_le_mul (reciprocal_lower hb hx0) (reciprocal_lower hR hy0) hlny
    (by positivity : 0 ≤ 1/x)
  have hco := mul_le_mul_of_nonneg_left hlxy hC
  have hco0 := mul_nonneg hC hlnprod
  rw [truncatedSixthZeroDelta_regular_eq (by norm_num) hx ⟨hy.1,hys⟩,if_pos (retained_region hx hy)]
  simp only [truncatedSixthLowerS,truncatedSixthLowerC,sub_zero]
  change wuLowerCoefficient ((1/2-x-y)/a)/(x*y*(1/2-x-y)) ≤ _
  have hid : wuLowerCoefficient ((1/2-x-y)/a)/(x*y*(1/2-x-y)) =
      (wuLowerCoefficient ((1/2-x-y)/a)/(1/2-x-y))/(x*y) := by
    simp only [div_eq_mul_inv,mul_inv_rev]; ring
  rw [hid]
  apply hhdiv.trans
  rw [sub_div]
  have he (v : ℝ) : v*(1/x*(1/y)) = v/(x*y) := by ring
  rw [he] at hpr hco
  have hco_nonneg : 0 ≤ C/(x*y) := hco0.trans hco
  nlinarith only [hpr,hco,hco_nonneg]

theorem low_upper {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc (cut x) (lam-x)) :
    truncatedSixthZeroDeltaRegular 0 (x,y) ≤ low x y := by
  have hg := low_geometry hx hy
  have ha := truncatedSixthLower_parameters.1
  have hl : 0 < s-b := by norm_num [s,b,truncatedSixthLowerSigma,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  have hz0 : 0 < 1/2-x-y-a := by linarith [hg.2.2.1]
  have hrec := reciprocal_upper ha (show a ≤ 1/2-x-y-a by linarith [hg.2.2.1])
    (show 1/2-x-y-a ≤ 2*a by linarith [hg.2.2.2])
  have hru : 0 ≤ reciprocalUpper a (2*a) (1/2-x-y-a) := (by positivity : 0 ≤ 1/(1/2-x-y-a)).trans hrec
  have ht : 0 ≤ lam-x-y := by have h := hy.2; linarith
  have hP : 0 ≤ lowPrincipal x y := by unfold lowPrincipal; positivity
  have hC : 0 ≤ lowCorrection x y := by unfold lowCorrection; positivity
  have hu2 : 2 ≤ (1/2-x-y)/a := (le_div_iff₀ ha).2 hg.2.2.1
  have hu4 : (1/2-x-y)/a ≤ 4 := (div_le_iff₀ ha).2 (by linarith [hg.2.2.2])
  have hlog : wuLowerCoefficient ((1/2-x-y)/a) ≤ log ((1/2-x-y)/a-1)+(0 : ℝ) := by
    have heq : wuLowerCoefficient ((1/2-x-y)/a) = log ((1/2-x-y)/a-1) :=
      jr1965f_normalized_firstInterval hu2 hu4
    rw [heq,add_zero]
  have hn := normalized hg.2.2.1 ha
    (show a ≤ 1/2-x-y-a by linarith [hg.2.2.1])
    (show 1/2-x-y-a ≤ 2*a by linarith [hg.2.2.2]) hg.2.2.2
    (by norm_num : (0 : ℝ) ≤ 0) (by positivity : 0 < 2*a) hg.2.2.1 hlog
  have hne : (1/2-x-y-2*a)/(2*a)*reciprocalUpper a (2*a) (1/2-x-y-a)+0/(2*a)-
      (1/2-x-y-2*a)^3/(3*a*(2*a)*(3*a)^2) = lowPrincipal x y-lowCorrection x y := by
    unfold lowPrincipal lowCorrection lam; ring
  rw [hne] at hn
  exact density_transport hx hg.1 hl hg.2.1.1 hg.2.1.2 hP hC hn

theorem high_upper {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc b (cut x)) :
    truncatedSixthZeroDeltaRegular 0 (x,y) ≤ high x y := by
  have hg := high_geometry hx hy
  have ha := truncatedSixthLower_parameters.1
  have hb := ha.trans truncatedSixthLower_parameters.2.1
  have hm : 0 < m := by norm_num [m,lam,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  have he : 0 ≤ error := by norm_num [error,zmax,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  have hz : 2*a ≤ 1/2-x-y := by linarith [hg.2.2.1]
  have hza : 2*a ≤ 1/2-x-y-a := by linarith [hg.2.2.1]
  have hzam : 1/2-x-y-a ≤ m := by dsimp [m,lam,zmax] at *; linarith [hg.2.2.2]
  have hz0 : 0 < 1/2-x-y-a := by linarith
  have hrec := reciprocal_upper (by positivity : 0 < 2*a) hza hzam
  have hru : 0 ≤ reciprocalUpper (2*a) m (1/2-x-y-a) := (by positivity : 0 ≤ 1/(1/2-x-y-a)).trans hrec
  have ht : 0 ≤ lam-x-y := by have h := hg.1.2; linarith
  have hP : 0 ≤ highPrincipal x y := by unfold highPrincipal; positivity
  have hC : 0 ≤ highCorrection x y := by unfold highCorrection; positivity
  have hlog := RetainedSixthDensity.lower_log_error ((le_div_iff₀ ha).2 hz)
    ((div_le_div_iff_of_pos_right ha).2 hg.2.2.2)
  have hn := normalized hz (by positivity : 0 < 2*a) hza hzam hg.2.2.2 he
    (by positivity : 0 < 3*a) hg.2.2.1 hlog
  have hne : (1/2-x-y-2*a)/(2*a)*reciprocalUpper (2*a) m (1/2-x-y-a)+error/(3*a)-
      (1/2-x-y-2*a)^3/(3*a*m*zmax^2) = highPrincipal x y-highCorrection x y := by
    unfold highPrincipal highCorrection lam; ring
  rw [hne] at hn
  exact density_transport hx hg.1 hb hy.1 hg.2.1 hP hC hn

end Wu2008DoubleSieve.NaturalSplitDensity
