import MathlibNt.SieveTheory.LiLiuGoldbachG67CenteredError
open Set hiding center
open MeasureTheory
open scoped Interval
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open G67Centered
noncomputable section
namespace G67CenteredEnvelope
set_option maxHeartbeats 4000000

/-- Positivity certificates shared by the centered logarithmic bounds. -/
theorem g67CenteredEnvelope_constants_pos :
    0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < center := by
  norm_num [a, b, c, center]

theorem shifted_error {t s : ℝ} (h : s-t ∈ Icc a c) :
    |shiftedLogPolynomial t s - Real.log ((s-t)/center)| ≤ 1/10000000 := by
  have hx : (s-t)/center-1 ∈ Icc (-3/5 : ℝ) (3/5) := by
    norm_num [a, c, center, div_le_iff₀, le_div_iff₀] at h ⊢
    constructor <;> linarith [h.1,h.2]
  have he : (1 : ℝ)+((s-t)/center-1) = (s-t)/center := by ring
  simpa only [shiftedLogPolynomial, he] using L_error hx

theorem profile_error {s : ℝ} (hs : s ∈ Icc (2*a) cutoff) :
    |profilePolynomial s - Real.log (((1/2-s)-a)/a)| ≤ 11/100000000 := by
  have hx : (((1/2-s)-a)/a)/(37/16)-1 ∈ Icc (-3/5 : ℝ) (3/5) := by
    norm_num [a, cutoff] at hs ⊢
    constructor <;> linarith [hs.1,hs.2]
  have hl := L_error hx
  have hc := (constant_log_error (show (37/16 : ℝ) ∈ Icc 1 4 by constructor <;> norm_num)).1
  have hp : 0 < ((1/2-s)-a)/a := by norm_num [a,cutoff] at hs ⊢; linarith [hs.2]
  have he : Real.log (1+((((1/2-s)-a)/a)/(37/16)-1)) =
      Real.log (((1/2-s)-a)/a) - Real.log (37/16) := by
    rw [show (1 : ℝ)+((((1/2-s)-a)/a)/(37/16)-1) = (((1/2-s)-a)/a)/(37/16) by ring]
    exact Real.log_div hp.ne' (by norm_num)
  rw [he] at hl
  rw [abs_sub_le_iff] at hl hc ⊢
  unfold profilePolynomial
  constructor <;> linarith [hl.1,hl.2,hc.1,hc.2]

theorem log_product_center {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log (x*y/(a*b)) = Real.log (center^2/(a*b)) +
      Real.log (x/center)+Real.log (y/center) := by
  obtain ⟨ha, hb, _, hc⟩ := g67CenteredEnvelope_constants_pos
  simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow]
  ring


def squareEarlyArgument (s : ℝ) : ℝ := (s-a)*(s-a)/(a*a)

theorem squareEarly_bounds {s : ℝ} (hs : s ∈ Icc (2*a) (a+b)) :
    |squareEarly s - Real.log (squareEarlyArgument s)| ≤ 22/100000000 ∧
    |Real.log (squareEarlyArgument s)| ≤ 2 := by
  have ha : s-a ∈ Icc a c := by
    norm_num [a,b,c,cutoff] at hs ⊢
    constructor <;> linarith [hs.1,hs.2]
  have pa : 0 < s-a := lt_of_lt_of_le (by norm_num [a]) ha.1
  have ea := shifted_error ha
  obtain ⟨apos, bpos, cpos, mpos⟩ := g67CenteredEnvelope_constants_pos
  have e0 := (constant_log_error (show (center/a : ℝ) ∈ Icc 1 4 by norm_num [center,a,b,c])).1
  have he : Real.log (squareEarlyArgument s) = 2*Real.log (center/a)+2*Real.log ((s-a)/center) := by
    unfold squareEarlyArgument
    simp (disch := positivity) only [Real.log_div, Real.log_mul]
    ring
  constructor
  · rw [he]
    unfold squareEarly
    rw [abs_sub_le_iff] at ea e0 ⊢
    constructor <;> linarith
  · have hr : squareEarlyArgument s ∈ Icc (1 : ℝ) 3 := by
      unfold squareEarlyArgument
      constructor
      · apply (le_div_iff₀ (by positivity)).2
        norm_num [a,b,c,cutoff] at hs ⊢
        nlinarith [hs.1,hs.2]
      · apply (div_le_iff₀ (by positivity)).2
        norm_num [a,b,c,cutoff] at hs ⊢
        nlinarith [hs.1,hs.2]
    rw [abs_of_nonneg (Real.log_nonneg hr.1)]
    exact (Real.log_le_sub_one_of_pos (by linarith [hr.1])).trans (by linarith [hr.2])

def squareLateArgument (s : ℝ) : ℝ := (b*b)/((s-b)*(s-b))

theorem squareLate_bounds {s : ℝ} (hs : s ∈ Icc (a+b) (2*b)) :
    |squareLate s - Real.log (squareLateArgument s)| ≤ 22/100000000 ∧
    |Real.log (squareLateArgument s)| ≤ 2 := by
  have hb : s-b ∈ Icc a c := by
    norm_num [a,b,c,cutoff] at hs ⊢
    constructor <;> linarith [hs.1,hs.2]
  have pb : 0 < s-b := lt_of_lt_of_le (by norm_num [a]) hb.1
  have eb := shifted_error hb
  obtain ⟨apos, bpos, cpos, mpos⟩ := g67CenteredEnvelope_constants_pos
  have e0 := (constant_log_error (show (2*b/center : ℝ) ∈ Icc 1 4 by norm_num [center,a,b,c])).1
  have e1 := (constant_log_error (show (2 : ℝ) ∈ Icc 1 4 by norm_num [center,a,b,c])).2
  have he : Real.log (squareLateArgument s) = 2*(Real.log (2*b/center)-Real.log 2)-2*Real.log ((s-b)/center) := by
    unfold squareLateArgument
    simp (disch := positivity) only [Real.log_div, Real.log_mul]
    ring
  constructor
  · rw [he]
    unfold squareLate
    rw [abs_sub_le_iff] at eb e0 e1 ⊢
    constructor <;> linarith
  · have hr : squareLateArgument s ∈ Icc (1 : ℝ) 3 := by
      unfold squareLateArgument
      constructor
      · apply (le_div_iff₀ (by positivity)).2
        norm_num [a,b,c,cutoff] at hs ⊢
        nlinarith [hs.1,hs.2]
      · apply (div_le_iff₀ (by positivity)).2
        norm_num [a,b,c,cutoff] at hs ⊢
        nlinarith [hs.1,hs.2]
    rw [abs_of_nonneg (Real.log_nonneg hr.1)]
    exact (Real.log_le_sub_one_of_pos (by linarith [hr.1])).trans (by linarith [hr.2])

def rectangleEarlyArgument (s : ℝ) : ℝ := (s-b)*(s-a)/(a*b)

theorem rectangleEarly_bounds {s : ℝ} (hs : s ∈ Icc (a+b) (2*b)) :
    |rectangleEarly s - Real.log (rectangleEarlyArgument s)| ≤ 22/100000000 ∧
    |Real.log (rectangleEarlyArgument s)| ≤ 2 := by
  have ha : s-a ∈ Icc a c := by
    norm_num [a,b,c,cutoff] at hs ⊢
    constructor <;> linarith [hs.1,hs.2]
  have pa : 0 < s-a := lt_of_lt_of_le (by norm_num [a]) ha.1
  have ea := shifted_error ha
  have hb : s-b ∈ Icc a c := by
    norm_num [a,b,c,cutoff] at hs ⊢
    constructor <;> linarith [hs.1,hs.2]
  have pb : 0 < s-b := lt_of_lt_of_le (by norm_num [a]) hb.1
  have eb := shifted_error hb
  obtain ⟨apos, bpos, cpos, mpos⟩ := g67CenteredEnvelope_constants_pos
  have e0 := (constant_log_error (show (center^2/(a*b) : ℝ) ∈ Icc 1 4 by norm_num [center,a,b,c])).1
  have he : Real.log (rectangleEarlyArgument s) = Real.log (center^2/(a*b))+Real.log ((s-b)/center)+Real.log ((s-a)/center) := by
    unfold rectangleEarlyArgument
    simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow]
    ring
  constructor
  · rw [he]
    unfold rectangleEarly
    rw [abs_sub_le_iff] at ea eb e0 ⊢
    constructor <;> linarith
  · have hr : rectangleEarlyArgument s ∈ Icc (1 : ℝ) 3 := by
      unfold rectangleEarlyArgument
      constructor
      · apply (le_div_iff₀ (by positivity)).2
        norm_num [a,b,c,cutoff] at hs ⊢
        nlinarith [hs.1,hs.2]
      · apply (div_le_iff₀ (by positivity)).2
        norm_num [a,b,c,cutoff] at hs ⊢
        nlinarith [hs.1,hs.2]
    rw [abs_of_nonneg (Real.log_nonneg hr.1)]
    exact (Real.log_le_sub_one_of_pos (by linarith [hr.1])).trans (by linarith [hr.2])

def rectangleMiddleArgument (s : ℝ) : ℝ := b*(s-a)/(a*(s-b))

theorem rectangleMiddle_bounds {s : ℝ} (hs : s ∈ Icc (2*b) (a+c)) :
    |rectangleMiddle s - Real.log (rectangleMiddleArgument s)| ≤ 22/100000000 ∧
    |Real.log (rectangleMiddleArgument s)| ≤ 2 := by
  have ha : s-a ∈ Icc a c := by
    norm_num [a,b,c,cutoff] at hs ⊢
    constructor <;> linarith [hs.1,hs.2]
  have pa : 0 < s-a := lt_of_lt_of_le (by norm_num [a]) ha.1
  have ea := shifted_error ha
  have hb : s-b ∈ Icc a c := by
    norm_num [a,b,c,cutoff] at hs ⊢
    constructor <;> linarith [hs.1,hs.2]
  have pb : 0 < s-b := lt_of_lt_of_le (by norm_num [a]) hb.1
  have eb := shifted_error hb
  obtain ⟨apos, bpos, cpos, mpos⟩ := g67CenteredEnvelope_constants_pos
  have e0 := (constant_log_error (show (b/a : ℝ) ∈ Icc 1 4 by norm_num [center,a,b,c])).1
  have he : Real.log (rectangleMiddleArgument s) = Real.log (b/a)+Real.log ((s-a)/center)-Real.log ((s-b)/center) := by
    unfold rectangleMiddleArgument
    simp (disch := positivity) only [Real.log_div, Real.log_mul]
    ring
  constructor
  · rw [he]
    unfold rectangleMiddle
    rw [abs_sub_le_iff] at ea eb e0 ⊢
    constructor <;> linarith
  · have hr : rectangleMiddleArgument s ∈ Icc (1 : ℝ) 3 := by
      unfold rectangleMiddleArgument
      constructor
      · apply (le_div_iff₀ (by positivity)).2
        norm_num [a,b,c,cutoff] at hs ⊢
        nlinarith [hs.1,hs.2]
      · apply (div_le_iff₀ (by positivity)).2
        norm_num [a,b,c,cutoff] at hs ⊢
        nlinarith [hs.1,hs.2]
    rw [abs_of_nonneg (Real.log_nonneg hr.1)]
    exact (Real.log_le_sub_one_of_pos (by linarith [hr.1])).trans (by linarith [hr.2])

def rectangleLateArgument (s : ℝ) : ℝ := b*c/((s-c)*(s-b))

theorem rectangleLate_bounds {s : ℝ} (hs : s ∈ Icc (a+c) (cutoff)) :
    |rectangleLate s - Real.log (rectangleLateArgument s)| ≤ 22/100000000 ∧
    |Real.log (rectangleLateArgument s)| ≤ 2 := by
  have hb : s-b ∈ Icc a c := by
    norm_num [a,b,c,cutoff] at hs ⊢
    constructor <;> linarith [hs.1,hs.2]
  have pb : 0 < s-b := lt_of_lt_of_le (by norm_num [a]) hb.1
  have eb := shifted_error hb
  have hc : s-c ∈ Icc a c := by
    norm_num [a,b,c,cutoff] at hs ⊢
    constructor <;> linarith [hs.1,hs.2]
  have pc : 0 < s-c := lt_of_lt_of_le (by norm_num [a]) hc.1
  have ec := shifted_error hc
  obtain ⟨apos, bpos, cpos, mpos⟩ := g67CenteredEnvelope_constants_pos
  have e0 := (constant_log_error (show (b*c/center^2 : ℝ) ∈ Icc 1 4 by norm_num [center,a,b,c])).1
  have he : Real.log (rectangleLateArgument s) = Real.log (b*c/center^2)-Real.log ((s-c)/center)-Real.log ((s-b)/center) := by
    unfold rectangleLateArgument
    simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow]
    ring
  constructor
  · rw [he]
    unfold rectangleLate
    rw [abs_sub_le_iff] at eb ec e0 ⊢
    constructor <;> linarith
  · have hr : rectangleLateArgument s ∈ Icc (1 : ℝ) 3 := by
      unfold rectangleLateArgument
      constructor
      · apply (le_div_iff₀ (by positivity)).2
        norm_num [a,b,c,cutoff] at hs ⊢
        nlinarith [hs.1,hs.2]
      · apply (div_le_iff₀ (by positivity)).2
        norm_num [a,b,c,cutoff] at hs ⊢
        nlinarith [hs.1,hs.2]
    rw [abs_of_nonneg (Real.log_nonneg hr.1)]
    exact (Real.log_le_sub_one_of_pos (by linarith [hr.1])).trans (by linarith [hr.2])


/-- The max in the actual profile is removed only on the certified full active interval. -/
theorem density_bridge {s : ℝ} (hs : s ∈ Icc (2*a) cutoff)
    {w : ℝ → ℝ} {W : ℝ}
    (hw : |w s-W| ≤ 22/100000000) (hW : |W| ≤ 3) :
    densityPolynomial w s - 1/40000 ≤ G67SumCoordinate.profile s*(W/s) := by
  have hgeom : s ∈ Icc (3/20 : ℝ) (7/20) := by
    norm_num [a,cutoff] at hs ⊢
    constructor <;> linarith [hs.1,hs.2]
  have harg : ((1/2-s)-a)/a ∈ Icc (1 : ℝ) 4 := by
    norm_num [a,cutoff] at hs ⊢
    constructor <;> linarith [hs.1,hs.2]
  have hP : |Real.log (((1/2-s)-a)/a)| ≤ 3 := by
    rw [abs_of_nonneg (Real.log_nonneg harg.1)]
    exact (Real.log_le_sub_one_of_pos (by linarith [harg.1])).trans (by linarith [harg.2])
  have h := product_error (profile_error hs) hw (reciprocal_error hgeom).1
    hP hW (reciprocal_error hgeom).2
  have hden : 0 < (1/2 : ℝ)-s := by linarith [hgeom.2]
  have hlog : 0 ≤ Real.log (((1/2-s)-a)/a)/(1/2-s) :=
    div_nonneg (Real.log_nonneg harg.1) hden.le
  unfold densityPolynomial
  have he : G67SumCoordinate.profile s = Real.log (((1/2-s)-a)/a)/(1/2-s) := by
    exact max_eq_right hlog
  rw [he]
  convert h using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

 theorem continuous_densityPolynomial {w : ℝ → ℝ} (hw : Continuous w) :
    Continuous (densityPolynomial w) := by
  have hL : Continuous S3Correction.L :=
    continuous_iff_continuousAt.mpr (fun x => (S3Correction.L_deriv x).continuousAt)
  unfold densityPolynomial profilePolynomial reciprocalPolynomial
  fun_prop

/-- Integrate a signed pointwise density loss; no polynomial sign hypothesis is used. -/
theorem integrate_loss {l u : ℝ} {f g : ℝ → ℝ} (hlu : l ≤ u)
    (hf : Continuous f) (hg : ContinuousOn g (Icc l u))
    (h : ∀ s ∈ Icc l u, f s-1/40000 ≤ g s) :
    (∫ s in l..u, f s) - (u-l)/40000 ≤ ∫ s in l..u, g s := by
  have hi := hf.intervalIntegrable (μ := volume) l u
  have hc : IntervalIntegrable (fun _ : ℝ => (1/40000 : ℝ)) volume l u :=
    intervalIntegrable_const
  have hm := intervalIntegral.integral_mono_on hlu (hi.sub hc)
    (hg.intervalIntegrable_of_Icc hlu) h
  rw [intervalIntegral.integral_sub hi hc, intervalIntegral.integral_const] at hm
  simpa only [smul_eq_mul, mul_one_div] using hm

end G67CenteredEnvelope
