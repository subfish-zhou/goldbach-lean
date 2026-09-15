import MathlibNt.Wu2008DoubleSieve.ClassicalAnalyticLeaves
import MathlibNt.Wu2008DoubleSieve.FourSeventhsBuchstab

namespace Wu2008DoubleSieve.ClassicalFourBounds
open Real Set MeasureTheory FourRoughClosedMass
open scoped Interval

/-- A symbolic polynomial FTC, valid for every natural exponent. -/
theorem integral_power_tail (C a b : ℝ) (n : ℕ) :
    (∫ x in a..b, C*(b-x)^n) = C*(b-a)^(n+1)/(n+1) := by
  have hd (x : ℝ) : HasDerivAt (fun x => -C*(b-x)^(n+1)/(n+1))
      (C*(b-x)^n) x := by
    have h := ((((hasDerivAt_const x b).sub (hasDerivAt_id x)).pow (n+1)).const_mul (-C)).div_const (n+1)
    have hn : (n : ℝ)+1 ≠ 0 := by positivity
    convert h using 1 <;> first | rfl | (simp; field_simp)
  have hi : IntervalIntegrable (fun x : ℝ => C*(b-x)^n) volume a b :=
    (by fun_prop : Continuous (fun x : ℝ => C*(b-x)^n)).intervalIntegrable a b
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hi
  rw [he]
  simp only [sub_self, zero_pow (Nat.succ_ne_zero n), mul_zero, zero_div, zero_sub]
  ring

theorem integral_le_power {f : ℝ → ℝ} {a b C : ℝ} (hf : Continuous f) (hab : a ≤ b)
    (n : ℕ) (hb : ∀ x ∈ Icc a b, f x ≤ C*(b-x)^n) :
    (∫ x in a..b, f x) ≤ C*(b-a)^(n+1)/(n+1) := by
  rw [← integral_power_tail]
  exact intervalIntegral.integral_mono_on hab (hf.intervalIntegrable a b)
    ((by fun_prop : Continuous (fun x : ℝ => C*(b-x)^n)).intervalIntegrable a b) hb

noncomputable def cap : ℝ := 4/(7*alpha^5)
noncomputable def longCap : ℝ := cap*(lam-alpha-beta)

theorem cap_pos : 0 < cap := by
  unfold cap
  exact div_pos (by norm_num) (mul_pos (by norm_num) (pow_pos fixed_geometry.2.1 _))

/-- The already-proved global 4/7 envelope is used only on its valid domain. -/
theorem regular_le_cap (x y z t : ℝ) : regularKernel x y z t ≤ cap := by
  have hb := SecondFunctionalFourSevenths.buchstab_le_four_sevenths
    (show (7/4 : ℝ) ≤ max 2 (parameter (clip x) (clip y) (clip z) (clip t)) from
      le_trans (by norm_num) (le_max_left _ _))
  have hden : alpha^5 ≤ clip x * clip y^2 * clip z * clip t := by
    have h2 : alpha^2 ≤ clip y^2 := pow_le_pow_left₀ fixed_geometry.2.1.le (le_max_left _ _) 2
    have h := mul_le_mul (mul_le_mul (mul_le_mul (le_max_left alpha x) h2
      (sq_nonneg alpha) (clip_pos x).le) (le_max_left alpha z)
      fixed_geometry.2.1.le (mul_nonneg (clip_pos x).le (sq_nonneg _))) (le_max_left alpha t)
      fixed_geometry.2.1.le
      (mul_nonneg (mul_nonneg (clip_pos x).le (sq_nonneg _)) (clip_pos z).le)
    change alpha^5 ≤ clip x * clip y^2 * clip z * clip t
    calc
      alpha^5 = alpha * alpha^2 * alpha * alpha := by ring
      _ ≤ _ := h
  have hd : 0 < clip x * clip y^2 * clip z * clip t :=
    mul_pos (mul_pos (mul_pos (clip_pos x) (sq_pos_of_pos (clip_pos y))) (clip_pos z)) (clip_pos t)
  calc
    _ ≤ (4/7)/(clip x * clip y^2 * clip z * clip t) :=
      div_le_div_of_nonneg_right hb hd.le
    _ ≤ (4/7)/alpha^5 := div_le_div_of_nonneg_left (by norm_num)
      (pow_pos fixed_geometry.2.1 _) hden
    _ = cap := by unfold cap; ring

theorem inner10_upper {x y z : ℝ} (hz : z ≤ beta) : regularInner10 x y z ≤ cap*(beta-z) := by
  have h := integral_le_power (f := fun t => regularKernel x y z t)
    (regularKernel_continuous.comp (f := fun t : ℝ => (x,y,z,t)) (by fun_prop)) hz 0 (by intro t _ht; simpa using regular_le_cap x y z t)
  simpa [regularInner10] using h

theorem middle10_upper {x y : ℝ} (hy : y ≤ beta) :
    regularMiddle10 x y ≤ cap/2*(beta-y)^2 := by
  have h := integral_le_power (f := fun z => regularInner10 x y z)
    (regularInner10_continuous.comp (f := fun z : ℝ => (x,y,z)) (by fun_prop)) hy 1 (by
      intro z hz; simpa using inner10_upper (x := x) (y := y) hz.2)
  change regularMiddle10 x y ≤ _ at h
  convert h using 1
  ring

theorem outer10_upper {x : ℝ} (hx : x ≤ beta) :
    regularOuter10 x ≤ cap/6*(beta-x)^3 := by
  have h := integral_le_power (f := fun y => regularMiddle10 x y)
    (regularMiddle10_continuous.comp (f := fun y : ℝ => (x,y)) (by fun_prop)) hx 2 (by
      intro y hy; exact middle10_upper hy.2)
  change regularOuter10 x ≤ _ at h
  convert h using 1
  ring

theorem I10_upper : I10 ≤ cap/24*(beta-alpha)^4 := by
  rw [I10_eq_regular]
  have h := integral_le_power regularOuter10_continuous fixed_geometry.2.2.1 3
    (by intro x hx; exact outer10_upper hx.2)
  convert h using 1
  ring

theorem inner11_upper {x y z : ℝ} (ha : alpha ≤ z) (hz : z ≤ beta) :
    regularInner11 x y z ≤ longCap := by
  have horder : beta ≤ lam-z := by linarith [fixed_geometry.2.2.2.2.2.2.1]
  have h := integral_le_power (f := fun t => regularKernel x y z t)
    (regularKernel_continuous.comp (f := fun t : ℝ => (x,y,z,t)) (by fun_prop)) horder 0
    (by intro t _ht; simpa using regular_le_cap x y z t)
  change regularInner11 x y z ≤ _ at h
  norm_num only [pow_zero, Nat.cast_zero, zero_add, div_one, pow_one] at h
  unfold longCap
  nlinarith [cap_pos]

theorem middle11_upper {x y : ℝ} (ha : alpha ≤ y) (hy : y ≤ beta) :
    regularMiddle11 x y ≤ longCap*(beta-y) := by
  have h := integral_le_power (f := fun z => regularInner11 x y z)
    (regularInner11_continuous.comp (f := fun z : ℝ => (x,y,z)) (by fun_prop)) hy 0 (by
      intro z hz; simpa using inner11_upper (x := x) (y := y) (ha.trans hz.1) hz.2)
  simpa [regularMiddle11] using h

theorem outer11_upper {x : ℝ} (ha : alpha ≤ x) (hx : x ≤ beta) :
    regularOuter11 x ≤ longCap/2*(beta-x)^2 := by
  have h := integral_le_power (f := fun y => regularMiddle11 x y)
    (regularMiddle11_continuous.comp (f := fun y : ℝ => (x,y)) (by fun_prop)) hx 1 (by
      intro y hy; simpa using middle11_upper (x := x) (ha.trans hy.1) hy.2)
  change regularOuter11 x ≤ _ at h
  convert h using 1
  ring

theorem I11_upper : I11 ≤ longCap/6*(beta-alpha)^3 := by
  rw [I11_eq_regular]
  have h := integral_le_power regularOuter11_continuous fixed_geometry.2.2.1 2
    (by intro x hx; exact outer11_upper hx.1 hx.2)
  convert h using 1
  ring

/-- A deliberately coarse, fully rational joint bound with both original weights intact. -/
theorem four_weighted_lt_six : 8*I10 + 8*I11 < 6 := by
  have h10 := I10_upper
  have h11 := I11_upper
  norm_num [cap, longCap, alpha, beta, lam, truncatedSixthLowerAlpha,
    truncatedSixthLowerBeta, truncatedSixthLowerLambda] at h10 h11
  linarith

end Wu2008DoubleSieve.ClassicalFourBounds
