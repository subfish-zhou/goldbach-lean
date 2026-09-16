import Wu18938Campaign.M3.Confirmed.LogMoments

noncomputable section

namespace Wu18938Campaign.M3.Confirmed.LogMoments

open Real Set MeasureTheory

def coordinate (d e t : ℝ) : ℝ := (d-e*t)/(1-t)

theorem coordinate_derivative {d e t : ℝ} (ht : t < 1) :
    HasDerivAt (coordinate d e) ((d-e)/(1-t)^2) t := by
  have h := (((hasDerivAt_id t).const_mul e).const_sub d).div
    ((hasDerivAt_id t).const_sub 1) (by linarith : 1-t ≠ 0)
  convert h using 1 <;> first | rfl | (dsimp; field_simp; ring)

theorem coordinate_antitone {d e l r : ℝ}
    (hde : d < e) (hlr : l ≤ r) (hr : r < 1) :
    coordinate d e r ≤ coordinate d e l := by
  unfold coordinate
  apply (div_le_div_iff₀ (by linarith : 0 < 1-r) (by linarith : 0 < 1-l)).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hde.le) (sub_nonneg.mpr hlr)]

theorem coordinate_lt {d e t : ℝ} (hde : d < e) (ht : 0 < t) (ht1 : t < 1) :
    coordinate d e t < d := by
  unfold coordinate
  apply (div_lt_iff₀ (by linarith : 0 < 1-t)).mpr
  nlinarith [mul_pos (sub_pos.mpr hde) ht]

def transformedKernel (d e t : ℝ) : ℝ :=
  log ((1+coordinate d e t)/(1-coordinate d e t))/(t*(1-t))

theorem transformed_integral_upper (n : ℕ) {d e l r : ℝ}
    (hl : 0 < l) (hlr : l ≤ r) (hr : r < 1) (hde : d < e)
    (hzr : 0 ≤ coordinate d e r) (hzl : coordinate d e l < 1) :
    (∫ t in l..r, transformedKernel d e t) ≤
      primitive n d (coordinate d e l) (coordinate d e l) -
        primitive n d (coordinate d e l) (coordinate d e r) := by
  let b := coordinate d e l
  have hg (t : ℝ) (ht : t ∈ Icc l r) :
      0 < t ∧ t < 1 ∧ 0 ≤ coordinate d e t ∧ coordinate d e t ≤ b ∧
        coordinate d e t < d := by
    have ht0 := hl.trans_le ht.1
    have ht1 := ht.2.trans_lt hr
    exact ⟨ht0,ht1,hzr.trans (coordinate_antitone hde ht.2 hr),
      coordinate_antitone hde ht.1 ht1,coordinate_lt hde ht0 ht1⟩
  have hc : ContinuousOn (coordinate d e) (Icc l r) := by
    intro t ht
    exact (coordinate_derivative (hg t ht).2.1).continuousAt.continuousWithinAt
  have hi : IntervalIntegrable (transformedKernel d e) volume l r := by
    apply ContinuousOn.intervalIntegrable_of_Icc hlr
    unfold transformedKernel
    apply ContinuousOn.div
    · apply ContinuousOn.log
      · exact (continuousOn_const.add hc).div (continuousOn_const.sub hc)
          (fun t ht => by have h := hg t ht; dsimp [b] at h; linarith)
      · intro t ht
        have h := hg t ht
        exact (div_pos (by linarith : 0 < 1+coordinate d e t)
          (by dsimp [b] at h; linarith : 0 < 1-coordinate d e t)).ne'
    · fun_prop
    · intro t ht
      exact (mul_pos (hg t ht).1 (by linarith [(hg t ht).2.1])).ne'
  have hpoly : Continuous (polynomial n b) := by
    unfold polynomial
    fun_prop
  have hpi : IntervalIntegrable
      (fun t => polynomial n b (coordinate d e t)/(t*(1-t))) volume l r := by
    apply ContinuousOn.intervalIntegrable_of_Icc hlr
    exact (hpoly.comp_continuousOn hc).div (by fun_prop)
      (fun t ht => (mul_pos (hg t ht).1 (by linarith [(hg t ht).2.1])).ne')
  have hd (t : ℝ) (ht : t ∈ Set.uIcc l r) :
      HasDerivAt (fun t => -primitive n d b (coordinate d e t))
        (polynomial n b (coordinate d e t)/(t*(1-t))) t := by
    rw [uIcc_of_le hlr] at ht
    have h := hg t ht
    have hder := ((primitive_derivative n (b := b) h.2.2.2.2).comp t
      (coordinate_derivative h.2.1)).neg
    convert! hder using 1
    · have htne := h.1.ne'
      have h1ne : 1-t ≠ 0 := by linarith [h.2.1]
      have hdene : e-d ≠ 0 := sub_pos.mpr hde |>.ne'
      have hden : d-coordinate d e t = (e-d)*t/(1-t) := by
        unfold coordinate
        field_simp
        ring
      rw [hden]
      field_simp [htne,h1ne,hdene]
      ring
  have hm := intervalIntegral.integral_mono_on hlr hi hpi (fun t ht =>
    div_le_div_of_nonneg_right
      (polynomial_upper n (hg t ht).2.2.1 (hg t ht).2.2.2.1 hzl)
      (mul_pos (hg t ht).1 (by linarith [(hg t ht).2.1])).le)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hpi] at hm
  simpa only [neg_sub_neg] using hm

end Wu18938Campaign.M3.Confirmed.LogMoments
