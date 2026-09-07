import MathlibNt.SieveTheory.LiLiuGoldbachB9HighFirstIntegral
import MathlibNt.SieveTheory.LiLiuGoldbachB9SplitIntegralReduction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
open MeasureTheory Set
open scoped Interval
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

/- Fixed before endpoint evaluation: n=10 logarithmic terms and m=96 geometric
terms. Entire-interval bounds use x≤1/3 and 3x≤7/9; no sampled values. -/
def highL (x : ℝ) : ℝ :=
  2 * ∑ k ∈ Finset.range 10, x^(2*k+1)/(2*k+1) + 9/4*x^21
def highG (x : ℝ) : ℝ :=
  3 * ((∑ k ∈ Finset.range 96, (3*x)^k) + 9/2*(3*x)^96)
def highF (x : ℝ) : ℝ := Real.log ((1+x)/(1-x)) * (3/(1-3*x))

theorem highL_bounds {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (7/27)) :
    Real.log ((1+x)/(1-x)) ≤ highL x ∧
    highL x ≤ Real.log ((1+x)/(1-x)) + 1/1000000000 := by
  have hxu : x ≤ (1/3 : ℝ) := by linarith [hx.2]
  have hx2 : x^2 ≤ (1/9 : ℝ) := by
    nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hxu)]
  have hp : 0 < 1-x^2 := by linarith
  have hb : x^21/(1-x^2) ≤ 9/8*x^21 := by
    apply (div_le_iff₀ hp).2
    nlinarith [mul_nonneg (pow_nonneg hx.1 21) (show 0 ≤ 1/9-x^2 by linarith)]
  have hu := Real.log_div_le_sum_range_add hx.1 (by linarith) 10
  have hl := Real.sum_range_le_log_div hx.1 (by linarith) 10
  have hpow : x^21 ≤ (1/3 : ℝ)^21 := pow_le_pow_left₀ hx.1 hxu 21
  have he : 9/4*x^21 ≤ (1/1000000000 : ℝ) := by
    calc
      _ ≤ 9/4*(1/3 : ℝ)^21 := mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ ≤ _ := by norm_num
  constructor <;> dsimp [highL] <;> linarith

theorem highG_identity (x : ℝ) :
    highG x*(1-3*x) = 3 + (3/2)*(3*x)^96*(7-27*x) := by
  have h := geom_sum_mul_neg (3*x) 96
  dsimp [highG]
  nlinarith [h]

theorem highG_bounds {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (7/27)) :
    3/(1-3*x) ≤ highG x ∧
    highG x ≤ 3/(1-3*x) + 1/100000000 := by
  have hp : 0 < 1-3*x := by linarith [hx.2]
  have hi := highG_identity x
  have hr : 0 ≤ (3*x)^96 := pow_nonneg (by linarith [hx.1]) _
  have hu : (3*x)^96 ≤ (7/9 : ℝ)^96 :=
    pow_le_pow_left₀ (by linarith [hx.1]) (by linarith [hx.2]) _
  have he : (27/2)*(3*x)^96 ≤ (1/100000000 : ℝ) := by
    calc
      _ ≤ (27/2)*(7/9 : ℝ)^96 := mul_le_mul_of_nonneg_left hu (by norm_num)
      _ ≤ _ := by norm_num
  constructor
  · apply (div_le_iff₀ hp).2
    nlinarith [mul_nonneg hr (show 0 ≤ 7-27*x by linarith [hx.2])]
  · have hb : highG x ≤ 3/(1-3*x) + (27/2)*(3*x)^96 := by
      have hc : 3/(1-3*x)*(1-3*x) = 3 := div_mul_cancel₀ _ hp.ne'
      have hh : highG x - (27/2)*(3*x)^96 ≤ 3/(1-3*x) := by
        apply (le_div_iff₀ hp).2
        nlinarith
      linarith
    linarith

theorem highF_enclosure {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (7/27)) :
    highF x ≤ highL x*highG x ∧
    highL x*highG x ≤ highF x + 1/10000000 := by
  have hp : 0 < 1-x := by linarith [hx.2]
  have hq : 0 < 1-3*x := by linarith [hx.2]
  have hratio : 1 ≤ (1+x)/(1-x) := (le_div_iff₀ hp).2 (by linarith [hx.1])
  have hratiou : (1+x)/(1-x) ≤ 2 := (div_le_iff₀ hp).2 (by linarith [hx.2])
  have hl0 : 0 ≤ Real.log ((1+x)/(1-x)) := Real.log_nonneg hratio
  have hl1 : Real.log ((1+x)/(1-x)) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (1+x)/(1-x) by linarith)
    linarith
  have hd0 : 0 ≤ 3/(1-3*x) := div_nonneg (by norm_num) hq.le
  have hd1 : 3/(1-3*x) ≤ (27/2 : ℝ) := (div_le_iff₀ hq).2 (by linarith [hx.2])
  obtain ⟨hLl,hLu⟩ := highL_bounds hx
  obtain ⟨hGl,hGu⟩ := highG_bounds hx
  have hL0 : 0 ≤ highL x := hl0.trans hLl
  have hG0 : 0 ≤ highG x := hd0.trans hGl
  have hG14 : highG x ≤ 14 := by linarith
  constructor
  · exact mul_le_mul hLl hGl hd0 hL0
  · have ha := mul_le_mul_of_nonneg_right
      (show highL x - Real.log ((1+x)/(1-x)) ≤ 1/1000000000 by linarith) hG0
    have hb := mul_le_mul_of_nonneg_left
      (show highG x - 3/(1-3*x) ≤ 1/100000000 by linarith) hl0
    dsimp [highF]
    nlinarith

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig