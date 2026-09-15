import MiddleWindowGain

namespace Wu2008DoubleSieve.Phase13
open Real Set MeasureTheory HighSixPhase9
noncomputable section

def κh : ℝ := 128/8073
def κH : ℝ := 64/56511

theorem κh_identity : κh = Phase11.k3*(8/5)^3 := by norm_num [κh,Phase11.k3]
theorem κH_identity : κH = Phase11.k4*(8/5)^4 := by norm_num [κH,Phase11.k4]
theorem κh_pos : 0 < κh := by norm_num [κh]
theorem κH_pos : 0 < κH := by norm_num [κH]

/-- The cubic gives the positive endpoint at four on the actual lower limit. -/
theorem h_four_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    amplitude δ*κh ≤ wuImprovementLimit false δ 4 := by
  have hh := Phase11.h_cubic hδ hδhi (s := 4) ⟨by norm_num,by norm_num⟩
  norm_num [Phase11.k3,κh] at *
  linarith only [hh]

/-- One original cross, not a global monotonicity assumption for h. -/
theorem h_terminal_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    amplitude δ*κh ≤ wuImprovementLimit false δ (18/5) := by
  have hc := wuImprovementLimit_lower_cross (s := (18/5 : ℝ)) (t := 4)
    hδ (by linarith) (by norm_num) (by norm_num) (by norm_num)
  norm_num only at hc
  have hi : 0 ≤ ∫ v in (13/5 : ℝ)..3, wuImprovementLimit true δ v/v := by
    have hm : (∫ v in (13/5 : ℝ)..3, (0 : ℝ)) ≤
        ∫ v in (13/5 : ℝ)..3, wuImprovementLimit true δ v/v := by
      apply intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const
        (wuImprovementLimit_div_intervalIntegrable true hδ (by linarith)
          (by norm_num) (by norm_num) (by norm_num))
      intro v hv
      exact div_nonneg (wuImprovementLimit_nonneg true hδ (by linarith)
        (by linarith [hv.1]) (by linarith [hv.2])) (by linarith [hv.1])
    simpa only [intervalIntegral.integral_zero] using hm
  linarith only [hc,hi,h_four_lower hδ hδhi]

/-- The true H antitone domain transports the quartic anchor at five. -/
theorem H_terminal_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    amplitude δ*κH ≤ wuImprovementLimit true δ (23/5) := by
  have hh := Phase12.H_quartic_antitone hδ hδhi (s := (23/5 : ℝ)) (r := 5)
    (by norm_num) (by norm_num) ⟨by norm_num,by norm_num⟩
  norm_num [Phase11.k4,κH] at *
  linarith only [hh]

/-- The original integral comparison is rebuilt with its positive terminal retained. -/
theorem h_retained_linear {δ u : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hu : u ∈ Icc (2 : ℝ) (18/5)) :
    amplitude δ*(κh+(5/13)*(18/5-u)) ≤ wuImprovementLimit false δ u := by
  have hc := wuImprovementLimit_lower_cross (s := u) (t := (18/5 : ℝ))
    hδ (by linarith) hu.1 hu.2 (by norm_num)
  norm_num only at hc
  have hn := h_terminal_lower hδ hδhi
  have hm : (∫ v in (u-1)..(13/5 : ℝ), (amplitude δ)*(5/13)) ≤
      ∫ v in (u-1)..(13/5 : ℝ), wuImprovementLimit true δ v/v := by
    apply intervalIntegral.integral_mono_on (by linarith [hu.2]) intervalIntegrable_const
      (wuImprovementLimit_div_intervalIntegrable true hδ (by linarith)
        (by linarith [hu.1]) (by linarith [hu.2]) (by norm_num))
    intro v hv
    have hs : amplitude δ ≤ wuImprovementLimit true δ v :=
      wuImprovementLimit_upper_antitone hδ (by linarith)
        ⟨by linarith [hu.1,hv.1],by linarith [hv.2]⟩
        ⟨by norm_num,by norm_num⟩ hv.2
    apply (le_div_iff₀ (by linarith [hu.1,hv.1])).2
    have hh := mul_le_mul_of_nonneg_left hv.2 (amplitude_nonneg hδ hδhi)
    nlinarith only [hs,hh]
  rw [intervalIntegral.integral_const,smul_eq_mul] at hm
  linarith only [hc,hn,hm]

/-- Integrate the single strengthened affine envelope and retain the upper terminal. -/
theorem H_retained_quadratic {δ s : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hs : s ∈ Icc (3 : ℝ) (23/5)) :
    amplitude δ*(κH+(25/468)*(23/5-s)^2+κh*(5/18)*(23/5-s)) ≤
      wuImprovementLimit true δ s := by
  have hc := wuImprovementLimit_upper_cross (s := s) (t := (23/5 : ℝ))
    hδ (by linarith) (by linarith [hs.1]) hs.2 (by norm_num)
  norm_num only at hc
  have hn := H_terminal_lower hδ hδhi
  have hia : IntervalIntegrable
      (fun u : ℝ => (amplitude δ*(5/13)*(5/18))*(18/5-u)) volume (s-1) (18/5) :=
    (continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable _ _
  have hm : (∫ u in (s-1)..(18/5 : ℝ),
      amplitude δ*κh*(5/18)+(amplitude δ*(5/13)*(5/18))*(18/5-u)) ≤
      ∫ u in (s-1)..(18/5 : ℝ), wuImprovementLimit false δ u/u := by
    apply intervalIntegral.integral_mono_on (by linarith [hs.2])
      (intervalIntegrable_const.add hia)
      (wuImprovementLimit_div_intervalIntegrable false hδ (by linarith)
        (by linarith [hs.1]) (by linarith [hs.2]) (by norm_num))
    intro u hu
    have hl := h_retained_linear hδ hδhi ⟨by linarith [hs.1,hu.1],hu.2⟩
    have hp : 0 ≤ amplitude δ*(κh+(5/13)*(18/5-u)) :=
      mul_nonneg (amplitude_nonneg hδ hδhi)
        (add_nonneg κh_pos.le (mul_nonneg (by norm_num) (by linarith [hu.2])))
    have hh := mul_le_mul_of_nonneg_left hu.2 hp
    apply (le_div_iff₀ (by linarith [hs.1,hu.1])).2
    nlinarith only [hl,hh]
  rw [intervalIntegral.integral_add intervalIntegrable_const hia,
    intervalIntegral.integral_const,smul_eq_mul,linear_integral] at hm
  nlinarith only [hc,hn,hm]

end
end Wu2008DoubleSieve.Phase13
