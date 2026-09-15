import MathlibNt.Wu2008DoubleSieve.PositiveKernelElementary

namespace Wu2008DoubleSieve
open Set MeasureTheory Real
open scoped Interval

/-- Strict payment of the actual negative-anchor density, including its endpoint slack. -/
theorem positiveKernel_anchor_payment {h : ℝ} (hh : 0 < h) (hh1 : h < 1) :
    (∫ z in (0 : ℝ)..h, log ((3-z)/(3-2*z))/(2-z)) <
      h^2 * (1/36 + 1/(3*(3-2*h)*(2-h))) := by
  let D : ℝ := (3-2*h)*(2-h)
  let g : ℝ → ℝ := fun z => z*((1-z/h)/6 + (z/h)/D)
  let P : ℝ → ℝ := fun z => z^2/12 + z^3/(3*h)*(1/D-1/6)
  have hD : 0 < D := mul_pos (by linarith) (by linarith)
  have pos (z : ℝ) (hz : z ∈ Icc 0 h) :
      0 < 3-z ∧ 0 < 3-2*z ∧ 0 < 2-z := by
    exact ⟨by linarith [hz.2], by linarith [hz.2], by linarith [hz.2]⟩
  have cf : ContinuousOn (fun z : ℝ => log ((3-z)/(3-2*z))/(2-z)) (Icc 0 h) := by
    apply ContinuousOn.div
    · apply ContinuousOn.log
      · exact (continuousOn_const.sub continuousOn_id).div
          (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
          (fun z hz => (pos z hz).2.1.ne')
      · exact fun z hz => (div_pos (pos z hz).1 (pos z hz).2.1).ne'
    · exact continuousOn_const.sub continuousOn_id
    · exact fun z hz => (pos z hz).2.2.ne'
  have cg : Continuous g := by dsimp [g]; fun_prop
  have bound (z : ℝ) (hz : z ∈ Icc 0 h) :
      log ((3-z)/(3-2*z))/(2-z) ≤ g z := by
    have hl := Real.log_le_sub_one_of_pos (div_pos (pos z hz).1 (pos z hz).2.1)
    have he : ((3-z)/(3-2*z)-1)/(2-z) = z/((3-2*z)*(2-z)) := by
      field_simp [(pos z hz).2.1.ne', (pos z hz).2.2.ne',
        (show 3-z*2 ≠ 0 by linarith [hz.2])]
      ring
    calc
      _ ≤ ((3-z)/(3-2*z)-1)/(2-z) := div_le_div_of_nonneg_right hl (pos z hz).2.2.le
      _ = z * (1/((3-2*z)*(2-z))) := by rw [he]; ring
      _ ≤ g z := by
        exact mul_le_mul_of_nonneg_left (positiveKernel_chord hh hh1 hz) hz.1
  have strict : log ((3-h)/(3-2*h))/(2-h) < g h := by
    have hp := pos h (right_mem_Icc.mpr hh.le)
    have hne : (3-h)/(3-2*h) ≠ 1 := by
      intro he
      have := (div_eq_one_iff_eq hp.2.1.ne').mp he
      linarith
    have hl := Real.log_lt_sub_one_of_pos (div_pos hp.1 hp.2.1) hne
    have he : ((3-h)/(3-2*h)-1)/(2-h) = g h := by
      dsimp [g, D]
      field_simp [hh.ne', hp.2.1.ne', hp.2.2.ne', show 3-h*2 ≠ 0 by linarith]
      ring
    rw [← he]
    exact div_lt_div_of_pos_right hl hp.2.2
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    hh cf cg.continuousOn (fun z hz => bound z ⟨hz.1.le, hz.2⟩)
    ⟨h, right_mem_Icc.mpr hh.le, strict⟩
  have hd (z : ℝ) : HasDerivAt P (g z) z := by
    convert! ((((hasDerivAt_id z).pow 2).div_const 12).add
      ((((hasDerivAt_id z).pow 3).div_const (3*h)).mul_const (1/D-1/6))) using 1
    dsimp [P, g]
    field_simp
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun z _ => hd z) (cg.intervalIntegrable 0 h)
  have hv : P h - P 0 = h^2 * (1/36 + 1/(3*(3-2*h)*(2-h))) := by
    dsimp [P, D]
    field_simp [hh.ne', show 3-h*2 ≠ 0 by linarith, show 2-h ≠ 0 by linarith]
    ring
  rwa [he, hv] at hi

end Wu2008DoubleSieve
