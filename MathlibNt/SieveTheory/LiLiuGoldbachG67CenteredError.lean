import MathlibNt.SieveTheory.LiLiuGoldbachG67CenteredPolynomial

open Set MeasureTheory Finset
open scoped Interval
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section
namespace G67CenteredEnvelope
set_option maxHeartbeats 4000000

/-- A two-sided error bound, valid also on the negative half of the centered domain. -/
theorem L_error {x : ℝ} (hx : x ∈ Icc (-3/5 : ℝ) (3/5)) :
    |S3Correction.L x - Real.log (1+x)| ≤ 1/10000000 := by
  let F : ℝ → ℝ := fun y => S3Correction.L y - Real.log (1+y)
  have hd : ∀ y ∈ Icc (-3/5 : ℝ) (3/5),
      HasDerivAt F (y^33/(1+y)) y := by
    intro y hy
    have hn : 1+y ≠ 0 := by linarith [hy.1]
    have hl : HasDerivAt (fun z : ℝ => Real.log (1+z)) (1/(1+y)) y := by
      convert (Real.hasDerivAt_log hn).comp y ((hasDerivAt_id y).const_add 1) using 1 <;>
        first | rfl | simp only [mul_one, one_div]
    convert! (S3Correction.L_deriv y).sub hl using 1
    have hr := S3Correction.L_residual y
    symm
    apply (eq_div_iff hn).2
    field_simp
    nlinarith only [hr]
  have hb : ∀ y ∈ Icc (-3/5 : ℝ) (3/5),
      ‖y^33/(1+y)‖ ≤ (5/2 : ℝ)*(3/5)^33 := by
    intro y hy
    have ha : |y| ≤ (3/5 : ℝ) := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
    have hp := pow_le_pow_left₀ (abs_nonneg y) ha 33
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos (by linarith [hy.1] : 0 < 1+y)]
    apply (div_le_iff₀ (by linarith [hy.1] : 0 < 1+y)).2
    have hmul := mul_le_mul_of_nonneg_left (show (2/5 : ℝ) ≤ 1+y by linarith [hy.1])
      (show 0 ≤ (5/2 : ℝ)*(3/5)^33 by positivity)
    nlinarith only [hp, hmul]
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y hy => (hd y hy).hasDerivWithinAt) hb (convex_Icc _ _)
    (show (0 : ℝ) ∈ Icc (-3/5 : ℝ) (3/5) by constructor <;> norm_num) hx
  have hz : F 0 = 0 := by simp [F, S3Correction.L_zero]
  rw [hz, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at h
  have ha : |x| ≤ (3/5 : ℝ) := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
  have hm := mul_le_mul_of_nonneg_left ha
    (show 0 ≤ (5/2 : ℝ)*(3/5)^33 by positivity)
  have hn : (5/2 : ℝ)*(3/5)^33*(3/5) ≤ 1/10000000 := by norm_num
  exact h.trans (hm.trans hn)

/-- Uniform control of the frozen 32-term constant-log bounds without expanding their sum. -/
theorem constant_log_error {r : ℝ} (hr : r ∈ Icc (1 : ℝ) 4) :
    |G9Analytic.logLower r - Real.log r| ≤ 1/10000000000 ∧
    |G9Analytic.logUpper r - Real.log r| ≤ 1/10000000000 := by
  have h := G9Analytic.log_bounds hr.1
  have hz : 0 ≤ (r-1)/(r+1) := div_nonneg (by linarith [hr.1]) (by linarith [hr.1])
  have hu : (r-1)/(r+1) ≤ (3/5 : ℝ) :=
    (div_le_iff₀ (by linarith [hr.1] : 0 < r+1)).2 (by linarith [hr.2])
  have hp := pow_le_pow_left₀ hz hu 65
  have hs := pow_le_pow_left₀ hz hu 2
  have hd : 0 < 1-((r-1)/(r+1))^2 := by norm_num at hs; linarith
  have he : G9Analytic.logUpper r - G9Analytic.logLower r ≤ 1/10000000000 := by
    unfold G9Analytic.logUpper
    rw [add_sub_cancel_left]
    apply (div_le_iff₀ hd).2
    norm_num at hp hs ⊢
    nlinarith only [hp, hs]
  constructor <;> apply abs_sub_le_iff.mpr <;> constructor <;> linarith [h.1, h.2]

/-- The geometric reciprocal approximation is controlled on the whole containing interval. -/
theorem reciprocal_error {s : ℝ} (hs : s ∈ Icc (3/20 : ℝ) (7/20)) :
    |G67Centered.reciprocalPolynomial s - 1/(s*(1/2-s))| ≤ 1/10000000000 ∧
    |1/(s*(1/2-s))| ≤ 20 := by
  let z : ℝ := (4*s-1)^2
  have hz : 0 ≤ z := sq_nonneg _
  have hzu : z ≤ (4/25 : ℝ) := by dsimp [z]; nlinarith [hs.1, hs.2]
  have hd : 0 < 1-z := by linarith
  have hp : 0 < s*(1/2-s) := mul_pos (by linarith [hs.1]) (by linarith [hs.2])
  have hid : (1-z) = 16*(s*(1/2-s)) := by dsimp [z]; ring
  have hr : 1/(s*(1/2-s)) = 16/(1-z) := by rw [hid]; field_simp
  have hg := geom_sum_mul_neg z 16
  have he : G67Centered.reciprocalPolynomial s - 16/(1-z) = -16*z^16/(1-z) := by
    unfold G67Centered.reciprocalPolynomial
    change 16*(∑ k ∈ range 16, z^k) - 16/(1-z) = -16*z^16/(1-z)
    apply (eq_div_iff hd.ne').2
    field_simp
    nlinarith only [hg]
  rw [hr, he]
  constructor
  · rw [abs_div, abs_mul, abs_of_nonneg (pow_nonneg hz 16), abs_of_pos hd]
    norm_num
    apply (div_le_iff₀ hd).2
    have hpow := pow_le_pow_left₀ hz hzu 16
    norm_num at hpow
    nlinarith only [hpow, hzu]
  · rw [abs_of_pos (div_pos (by norm_num) hd)]
    apply (div_le_iff₀ hd).2
    linarith

/-- Absolute product errors do not assume that any polynomial approximation is nonnegative. -/
theorem product_error {p w r P W R : ℝ}
    (hp : |p-P| ≤ 11/100000000) (hw : |w-W| ≤ 22/100000000)
    (hr : |r-R| ≤ 1/10000000000)
    (hP : |P| ≤ 3) (hW : |W| ≤ 3) (hR : |R| ≤ 20) :
    p*w*r - 1/40000 ≤ P*W*R := by
  have hp' : |p| ≤ 3+11/100000000 := by
    calc |p| = |(p-P)+P| := by congr 1; ring
         _ ≤ |p-P|+|P| := abs_add_le _ _
         _ ≤ _ := by linarith [add_le_add hp hP]
  have hw' : |w| ≤ 3+22/100000000 := by
    calc |w| = |(w-W)+W| := by congr 1; ring
         _ ≤ |w-W|+|W| := abs_add_le _ _
         _ ≤ _ := by linarith [add_le_add hw hW]
  have h1 := mul_le_mul hp hW (abs_nonneg W) (by norm_num : (0 : ℝ) ≤ 11/100000000)
  have h2 := mul_le_mul hp' hw (abs_nonneg (w-W)) (by norm_num : (0 : ℝ) ≤ 3+11/100000000)
  have h3 := mul_le_mul (mul_le_mul hp' hw' (abs_nonneg w) (by norm_num)) hr
    (abs_nonneg (r-R)) (by positivity)
  have he : p*w*r-P*W*R = ((p-P)*W+p*(w-W))*R + p*w*(r-R) := by ring
  have ht : |p*w*r-P*W*R| ≤
      (11/100000000*3+(3+11/100000000)*(22/100000000))*20 +
      ((3+11/100000000)*(3+22/100000000))*(1/10000000000) := by
    rw [he]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul, abs_mul]
    apply add_le_add _ h3
    apply mul_le_mul _ hR (abs_nonneg R) (by positivity)
    exact (abs_add_le _ _).trans (by simpa only [abs_mul] using add_le_add h1 h2)
  have ht' := (le_abs_self (p*w*r-P*W*R)).trans ht
  norm_num at ht'
  linarith

end G67CenteredEnvelope
