import Phase10LogCount

namespace Wu2008DoubleSieve.Phase11
open Real Set MeasureTheory HighSixPhase9
noncomputable section

def k3 : ℝ := 125/32292
def k4 : ℝ := 625/3616704

theorem k3_identity : k3 = (25/468)*(5/23)/3 := by norm_num [k3]
theorem k4_identity : k4 = k3*(5/28)/4 := by norm_num [k3,k4]

/-- A genuine polynomial FTC; no continuity is assumed for the improvement limit. -/
theorem square_reverse_integral (a b k : ℝ) :
    (∫ u in a..b, k*(b-u)^2) = k/3*(b-a)^3 := by
  have hd : ∀ u : ℝ, HasDerivAt (fun x : ℝ => -(k/3)*(b-x)^3)
      (k*(b-u)^2) u := by
    intro u
    have hh := (((hasDerivAt_const u b).sub (hasDerivAt_id u)).pow 3).const_mul (-(k/3))
    convert hh using 1 <;> first | rfl | (norm_num; ring)
  have hi : IntervalIntegrable (fun u : ℝ => k*(b-u)^2) volume a b :=
    (continuous_const.mul ((continuous_const.sub continuous_id).pow 2)).intervalIntegrable a b
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) hi
  calc
    _ = -(k/3)*(b-b)^3-(-(k/3)*(b-a)^3) := hf
    _ = _ := by ring

/-- A genuine polynomial FTC; no continuity is assumed for the improvement limit. -/
theorem cube_reverse_integral (a b k : ℝ) :
    (∫ u in a..b, k*(b-u)^3) = k/4*(b-a)^4 := by
  have hd : ∀ u : ℝ, HasDerivAt (fun x : ℝ => -(k/4)*(b-x)^4)
      (k*(b-u)^3) u := by
    intro u
    have hh := (((hasDerivAt_const u b).sub (hasDerivAt_id u)).pow 4).const_mul (-(k/4))
    convert hh using 1 <;> first | rfl | (norm_num; ring)
  have hi : IntervalIntegrable (fun u : ℝ => k*(b-u)^3) volume a b :=
    (continuous_const.mul ((continuous_const.sub continuous_id).pow 3)).intervalIntegrable a b
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) hi
  calc
    _ = -(k/4)*(b-b)^4-(-(k/4)*(b-a)^4) := hf
    _ = _ := by ring

/-- The next literal cross transports the whole previous envelope to a new domain. -/
theorem h_cubic {δ s : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hs : s ∈ Icc (4 : ℝ) (28/5)) :
    amplitude δ*k3*(28/5-s)^3 ≤ wuImprovementLimit false δ s := by
  have hc := wuImprovementLimit_lower_cross (s := s) (t := (28/5 : ℝ))
    hδ (by linarith) (by linarith [hs.1]) hs.2 (by norm_num)
  norm_num only at hc
  have hn := wuImprovementLimit_nonneg false hδ (by linarith : δ < 1/2)
    (s := (28/5 : ℝ)) (by norm_num) (by norm_num)
  have hm : (∫ u in (s-1)..(23/5 : ℝ), (amplitude δ*(25/468)*(1/(23/5)))*(23/5-u)^2) ≤
      ∫ u in (s-1)..(23/5 : ℝ), wuImprovementLimit true δ u/u := by
    apply intervalIntegral.integral_mono_on (by linarith [hs.2])
      ((continuous_const.mul ((continuous_const.sub continuous_id).pow 2)).intervalIntegrable _ _)
      (wuImprovementLimit_div_intervalIntegrable true hδ (by linarith)
        (by linarith [hs.1]) (by linarith [hs.2]) (by norm_num))
    intro u hu
    have hl := H_quadratic hδ hδhi ⟨by linarith [hs.1,hu.1],hu.2⟩
    have hp : 0 ≤ amplitude δ*(25/468)*(23/5-u)^2 :=
      mul_nonneg (mul_nonneg (amplitude_nonneg hδ hδhi) (by norm_num [k3]))
        (pow_nonneg (by linarith [hu.2]) _)
    have hh := mul_le_mul_of_nonneg_left hu.2 hp
    apply (le_div_iff₀ (by linarith [hs.1,hu.1])).2
    dsimp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, id_eq]
    nlinarith only [hl,hh]
  rw [square_reverse_integral] at hm
  dsimp [k3,k4] at *
  nlinarith only [hc,hn,hm]

/-- The next literal cross transports the whole previous envelope to a new domain. -/
theorem H_quartic {δ s : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hs : s ∈ Icc (5 : ℝ) (33/5)) :
    amplitude δ*k4*(33/5-s)^4 ≤ wuImprovementLimit true δ s := by
  have hc := wuImprovementLimit_upper_cross (s := s) (t := (33/5 : ℝ))
    hδ (by linarith) (by linarith [hs.1]) hs.2 (by norm_num)
  norm_num only at hc
  have hn := wuImprovementLimit_nonneg true hδ (by linarith : δ < 1/2)
    (s := (33/5 : ℝ)) (by norm_num) (by norm_num)
  have hm : (∫ u in (s-1)..(28/5 : ℝ), (amplitude δ*k3*(1/(28/5)))*(28/5-u)^3) ≤
      ∫ u in (s-1)..(28/5 : ℝ), wuImprovementLimit false δ u/u := by
    apply intervalIntegral.integral_mono_on (by linarith [hs.2])
      ((continuous_const.mul ((continuous_const.sub continuous_id).pow 3)).intervalIntegrable _ _)
      (wuImprovementLimit_div_intervalIntegrable false hδ (by linarith)
        (by linarith [hs.1]) (by linarith [hs.2]) (by norm_num))
    intro u hu
    have hl := h_cubic hδ hδhi ⟨by linarith [hs.1,hu.1],hu.2⟩
    have hp : 0 ≤ amplitude δ*k3*(28/5-u)^3 :=
      mul_nonneg (mul_nonneg (amplitude_nonneg hδ hδhi) (by norm_num [k3]))
        (pow_nonneg (by linarith [hu.2]) _)
    have hh := mul_le_mul_of_nonneg_left hu.2 hp
    apply (le_div_iff₀ (by linarith [hs.1,hu.1])).2
    dsimp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, id_eq]
    nlinarith only [hl,hh]
  rw [cube_reverse_integral] at hm
  dsimp [k3,k4] at *
  nlinarith only [hc,hn,hm]

end
end Wu2008DoubleSieve.Phase11
