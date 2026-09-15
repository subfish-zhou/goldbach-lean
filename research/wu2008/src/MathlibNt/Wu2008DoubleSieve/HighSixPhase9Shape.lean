import MathlibNt.Wu2008DoubleSieve.HighSixPhase7Feedback

namespace Wu2008DoubleSieve.HighSixPhase9
open Real Set MeasureTheory
noncomputable def amplitude (δ : ℝ) : ℝ := wuImprovementLimit true δ (13/5)

theorem amplitude_nonneg {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    0 ≤ amplitude δ :=
  wuImprovementLimit_nonneg true hδ (by linarith) (by norm_num) (by norm_num)
noncomputable section

/-- The first cross preserves the entire affine lower envelope. -/
theorem h_linear {δ u : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hu : u ∈ Icc (2 : ℝ) (18/5)) :
    (amplitude δ)*(5/13)*(18/5-u) ≤ wuImprovementLimit false δ u := by
  have hc := wuImprovementLimit_lower_cross (s := u) (t := (18/5 : ℝ))
    hδ (by linarith) hu.1 hu.2 (by norm_num)
  norm_num only at hc
  have hn := wuImprovementLimit_nonneg false hδ (by linarith : δ < 1/2)
    (s := (18/5 : ℝ)) (by norm_num) (by norm_num)
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

/-- A polynomial primitive evaluates the affine comparison, not H itself. -/
theorem linear_integral (a b k : ℝ) :
    (∫ u in a..b, k*(b-u)) = k/2*(b-a)^2 := by
  have hd : ∀ u : ℝ, HasDerivAt (fun x : ℝ => -(k/2)*(b-x)^2) (k*(b-u)) u := by
    intro u
    have hh := (((hasDerivAt_const u b).sub (hasDerivAt_id u)).pow 2).const_mul (-(k/2))
    convert hh using 1 <;> first | rfl | (norm_num; ring)
  have hi : IntervalIntegrable (fun u : ℝ => k*(b-u)) volume a b :=
    (continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable a b
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hd u) hi
  calc
    _ = -(k/2)*(b-b)^2-(-(k/2)*(b-a)^2) := hf
    _ = _ := by ring

/-- The second literal cross yields the full quadratic envelope. -/
theorem H_quadratic {δ s : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hs : s ∈ Icc (3 : ℝ) (23/5)) :
    (amplitude δ)*(25/468)*(23/5-s)^2 ≤ wuImprovementLimit true δ s := by
  have hc := wuImprovementLimit_upper_cross (s := s) (t := (23/5 : ℝ))
    hδ (by linarith) (by linarith [hs.1]) hs.2 (by norm_num)
  norm_num only at hc
  have hn := wuImprovementLimit_nonneg true hδ (by linarith : δ < 1/2)
    (s := (23/5 : ℝ)) (by norm_num) (by norm_num)
  have hm : (∫ u in (s-1)..(18/5 : ℝ), ((amplitude δ)*(5/13)*(5/18))*(18/5-u)) ≤
      ∫ u in (s-1)..(18/5 : ℝ), wuImprovementLimit false δ u/u := by
    apply intervalIntegral.integral_mono_on (by linarith [hs.2])
      ((continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable _ _)
      (wuImprovementLimit_div_intervalIntegrable false hδ (by linarith)
        (by linarith [hs.1]) (by linarith [hs.2]) (by norm_num))
    intro u hu
    have hl := h_linear hδ hδhi ⟨by linarith [hs.1,hu.1],hu.2⟩
    have hp : 0 ≤ (amplitude δ)*(5/13)*(18/5-u) :=
      mul_nonneg (mul_nonneg (amplitude_nonneg hδ hδhi) (by norm_num)) (by linarith [hu.2])
    have hh := mul_le_mul_of_nonneg_left hu.2 hp
    apply (le_div_iff₀ (by linarith [hs.1,hu.1])).2
    dsimp only [Pi.mul_apply, Pi.sub_apply, id_eq]
    nlinarith only [hl,hh]
  rw [linear_integral] at hm
  nlinarith only [hc,hn,hm]

end
end Wu2008DoubleSieve.HighSixPhase9
