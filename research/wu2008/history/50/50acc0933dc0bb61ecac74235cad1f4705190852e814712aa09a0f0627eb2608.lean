import ExactSixthOuter
import ClassicalLossBottleneck

noncomputable section
open Real Set MeasureTheory
open Wu2008DoubleSieve
open Wu2008DoubleSieve.PositiveSixthFTC
open Wu2008DoubleSieve.DynamicSixthEnvelope
open Wu2008DoubleSieve.SharpLogRecurrence
open scoped Interval

namespace WuTarget.E05Sixth

def fifthLogTerm (t : ℝ) : ℝ := (2/5)*((t-1)/(t+1))^5

theorem fifth_gap_derivative {t : ℝ} (ht : 1 ≤ t) :
    HasDerivAt (fun t => log t-lowerLog t-fifthLogTerm t)
      ((t-1)^6/(t*(t+1)^6)) t := by
  have ht0 : t ≠ 0 := by linarith
  have ht1 : t+1 ≠ 0 := by linarith
  have hq := ((hasDerivAt_id t).sub_const 1).div
    ((hasDerivAt_id t).add_const 1) ht1
  have h := (lower_gap_derivative ht).sub ((hq.pow 5).const_mul (2/5))
  convert h using 1 <;> first | rfl | (dsimp; field_simp; ring)

theorem log_fifth_lower {t : ℝ} (ht : 1 ≤ t) :
    lowerLog t+fifthLogTerm t ≤ log t := by
  have h := anchored_nonnegative (fun x hx => fifth_gap_derivative hx)
    (fun x hx => div_nonneg (pow_nonneg (by linarith) _) (by positivity)) ht
  norm_num [lowerLog,fifthLogTerm] at h
  linarith only [h]

theorem weighted_power_decreasing {c l u : ℝ}
    (hlu : l ≤ u) (huc : u ≤ c) (hc : c ≤ 7*l) :
    u*(c-u)^6 ≤ l*(c-l)^6 := by
  have hd (t : ℝ) :
      HasDerivAt (fun t : ℝ => t*(c-t)^6) ((c-t)^5*(c-7*t)) t := by
    convert (hasDerivAt_id t).mul
      (((hasDerivAt_const t c).sub (hasDerivAt_id t)).pow 6) using 1 <;>
      first | rfl | (dsimp; ring)
  have hm : AntitoneOn (fun t : ℝ => t*(c-t)^6) (Icc l c) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc l c)
      (by fun_prop)
      (fun x _ => (hd x).hasDerivWithinAt)
      (fun x hx => by
        have hx' : x ∈ Icc l c := interior_subset hx
        exact mul_nonpos_of_nonneg_of_nonpos
          (pow_nonneg (sub_nonneg.mpr hx'.2) 5) (by linarith [hx'.1]))
  exact hm ⟨le_rfl,hlu.trans huc⟩ ⟨hlu,huc⟩ hlu

def denominatorCap : ℝ := a*b*(1/2-a-b)^6
def correctionKernel (x y : ℝ) : ℝ := (2/5)*(lam-x-y)^5/denominatorCap
def correctionInner (x : ℝ) : ℝ := (lam-x-b)^6/(15*denominatorCap)
def sixthCredit : ℝ :=
  (4/(105*denominatorCap))*((lam-a-b)^7-(lam-2*b)^7)

theorem denominatorCap_pos : 0 < denominatorCap := by
  norm_num [denominatorCap,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

theorem denominator_bound {x y : ℝ} (hx : x ∈ Icc a b)
    (hy : y ∈ Icc b (lam-x)) :
    x*y*(1/2-x-y)^6 ≤ denominatorCap := by
  have hg := Phase25.mask_geometry hx hy
  have hya : 1/2-x ≤ 7*b := by
    have hl := hx.1
    norm_num [a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta] at hl ⊢
    linarith
  have hxa : 1/2-b ≤ 7*a := by
    norm_num [a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  have hyc : y ≤ 1/2-x := by linarith [hg.2.2.2.1]
  have hxc : x ≤ 1/2-b := by linarith [hy.1,hg.2.2.2.1]
  have h1 := mul_le_mul_of_nonneg_left
    (weighted_power_decreasing hy.1 hyc hya) hg.1.le
  have h2 := mul_le_mul_of_nonneg_left
    (weighted_power_decreasing hx.1 hxc hxa) geometry.2.2.1.le
  have he (t : ℝ) : (1/2 : ℝ)-b-t = 1/2-t-b := by ring
  simp only [he] at h2
  unfold denominatorCap
  nlinarith only [h1,h2]

end WuTarget.E05Sixth
