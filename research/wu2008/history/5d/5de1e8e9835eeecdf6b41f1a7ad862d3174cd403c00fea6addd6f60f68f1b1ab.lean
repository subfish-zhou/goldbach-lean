import E05SixthRoot

noncomputable section
open Real Set MeasureTheory
open Wu2008DoubleSieve
open Wu2008DoubleSieve.PositiveSixthFTC
open Wu2008DoubleSieve.DynamicSixthEnvelope
open Wu2008DoubleSieve.SharpLogRecurrence
open Wu2008DoubleSieve.SharpMassBalance
open scoped Interval

namespace WuTarget.E05Major

def seventhLogTerm (t : ℝ) : ℝ := (2/7)*((t-1)/(t+1))^7

theorem seventh_gap_derivative {t : ℝ} (ht : 1 ≤ t) :
    HasDerivAt (fun t => log t-lowerLog t-E05Sixth.fifthLogTerm t-seventhLogTerm t)
      ((t-1)^8/(t*(t+1)^8)) t := by
  have ht0 : t ≠ 0 := by linarith
  have ht1 : t+1 ≠ 0 := by linarith
  have hq := ((hasDerivAt_id t).sub_const 1).div
    ((hasDerivAt_id t).add_const 1) ht1
  have h := (E05Sixth.fifth_gap_derivative ht).sub ((hq.pow 7).const_mul (2/7))
  convert h using 1 <;> first | rfl | (dsimp; field_simp; ring)

theorem log_seventh_lower {t : ℝ} (ht : 1 ≤ t) :
    lowerLog t+E05Sixth.fifthLogTerm t+seventhLogTerm t ≤ log t := by
  have h := anchored_nonnegative (fun x hx => seventh_gap_derivative hx)
    (fun x hx => div_nonneg (pow_nonneg (by linarith) _) (by positivity)) ht
  norm_num [lowerLog,E05Sixth.fifthLogTerm,seventhLogTerm] at h ⊢
  linarith only [h]

theorem fifth_product_max {c u : ℝ} (hu : 0 ≤ u) (huc : u ≤ c) :
    u*(c-u)^5 ≤ (c/6)*(5*c/6)^5 := by
  have hd (t : ℝ) :
      HasDerivAt (fun t : ℝ => t*(c-t)^5) ((c-t)^4*(c-6*t)) t := by
    convert (hasDerivAt_id t).mul
      (((hasDerivAt_const t c).sub (hasDerivAt_id t)).pow 5) using 1 <;>
      first | rfl | (dsimp; ring)
  have h0c : 0 ≤ c := hu.trans huc
  have he : c-c/6 = 5*c/6 := by ring
  by_cases h : u ≤ c/6
  · have hm : MonotoneOn (fun t : ℝ => t*(c-t)^5) (Icc 0 (c/6)) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
        (by fun_prop) (fun x _ => (hd x).hasDerivWithinAt)
        (fun x hx => by
          have hx' : x ∈ Icc 0 (c/6) := interior_subset hx
          exact mul_nonneg (pow_nonneg (by linarith [hx'.2]) 4) (by linarith [hx'.2]))
    simpa only [he] using hm ⟨hu,h⟩ ⟨by positivity,le_rfl⟩ h
  · have hm : AntitoneOn (fun t : ℝ => t*(c-t)^5) (Icc (c/6) c) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
        (by fun_prop) (fun x _ => (hd x).hasDerivWithinAt)
        (fun x hx => by
          have hx' : x ∈ Icc (c/6) c := interior_subset hx
          exact mul_nonpos_of_nonneg_of_nonpos
            (pow_nonneg (by linarith [hx'.2]) 4) (by linarith [hx'.1]))
    simpa only [he] using hm ⟨le_rfl,by linarith⟩ ⟨le_of_not_ge h,huc⟩
      (le_of_not_ge h)

def z0 : ℝ := 1/2-a-b
def innerDenom1 : ℝ := ((1/2-b+2*a)/6)*(5*(1/2-b+2*a)/6)^5
def innerDenom2 : ℝ := ((1/2-2*a+b)/6)*(5*(1/2-2*a+b)/6)^5

theorem fixed_positive : 0 < z0 ∧ 0 < innerDenom1 ∧ 0 < innerDenom2 := by
  norm_num [z0,innerDenom1,innerDenom2,a,b,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

theorem S_derivative {c h : ℝ} (hc : c ≠ 0) :
    HasDerivAt (fun c : ℝ => Phase25.S c h)
      ((-(8/3)*c^3+8*h*c^2-6*h^2*c+(8/3)*h^3)/c^5) c := by
  have hi := hasDerivAt_id c
  have hh := ((((hasDerivAt_const c (8/3)).div hi hc).sub
    ((hasDerivAt_const c (4*h)).div (hi.pow 2) (pow_ne_zero 2 hc))).add
    ((hasDerivAt_const c (2*h^2)).div (hi.pow 3) (pow_ne_zero 3 hc))).sub
    ((hasDerivAt_const c ((2/3)*h^3)).div (hi.pow 4) (pow_ne_zero 4 hc))
  convert hh using 1 <;> first | rfl | (dsimp; field_simp; ring)

theorem S_antitone {h : ℝ} (hh : 0 < h) :
    AntitoneOn (fun c : ℝ => Phase25.S c h) (Ici (5*h/2)) := by
  have hn {c : ℝ} (hc : 5*h/2 ≤ c) :
      (-(8/3)*c^3+8*h*c^2-6*h^2*c+(8/3)*h^3)/c^5 ≤ 0 := by
    have hd : 0 ≤ c-5*h/2 := sub_nonneg.mpr hc
    have he : -(8/3)*c^3+8*h*c^2-6*h^2*c+(8/3)*h^3 =
        -(8/3)*(c-5*h/2)^3-12*h*(c-5*h/2)^2-
          16*h^2*(c-5*h/2)-4*h^3 := by ring
    rw [he]
    apply div_nonpos_of_nonpos_of_nonneg _ (pow_nonneg (by linarith) 5)
    have h1 := mul_nonneg (show (0:ℝ) ≤ 8/3 by norm_num) (pow_nonneg hd 3)
    have h2 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 12 by norm_num) hh.le) (sq_nonneg _)
    have h3 := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 16 by norm_num) (sq_nonneg h)) hd
    have h4 := mul_nonneg (show (0:ℝ) ≤ 4 by norm_num) (pow_nonneg hh.le 3)
    linarith only [h1,h2,h3,h4]
  exact antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici _)
    (fun x hx => (S_derivative (h := h) (by linarith : x ≠ 0)).continuousAt.continuousWithinAt)
    (fun x hx => (S_derivative (h := h)
      (by have hx' : 5*h/2 ≤ x := interior_subset hx; linarith)).hasDerivWithinAt)
    (fun x hx => hn (interior_subset hx))

theorem S_lower {x : ℝ} (hx : x ∈ Icc a b) :
    (69/20:ℝ) ≤ Phase25.S (1/2-x) (2*a) := by
  have hc : 5*(2*a)/2 ≤ 1/2-x := by
    have hu := hx.2
    norm_num [a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta] at hu ⊢
    linarith
  have hm := S_antitone (mul_pos (by norm_num : (0:ℝ) < 2) geometry.1)
    hc (show 5*(2*a)/2 ≤ 1/2-a by linarith [hx.1]) (by linarith [hx.1])
  have hl : (69/20:ℝ) ≤ Phase25.S (1/2-a) (2*a) := by
    norm_num [Phase25.S,a,truncatedSixthLowerAlpha]
  exact hl.trans hm

end WuTarget.E05Major
