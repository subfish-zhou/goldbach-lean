import MathlibNt.Wu2008DoubleSieve.PositiveClassicalCoefficient

namespace Wu2008DoubleSieve.VariableUpperEnvelope
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence
open scoped Interval
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

/-- A variable cubic majorant, obtained from the original recurrence on [3,4]. -/
noncomputable def cubic (u : ℝ) : ℝ := 1+(u-3)^2/4-(u-3)^3/12

 theorem log_chord_upper {z : ℝ} (hz : 0 ≤ z) :
    log (1+z) ≤ z*(2+z)/(2*(1+z)) := by
  have h := SecondFunctionalFourSevenths.log_chord_bound
    (a := (1 : ℝ)) (b := 1+z) (by norm_num) (by linarith)
  norm_num only [log_one, sub_zero] at h
  calc
    log (1+z) = log ((1+z)/1) := by rw [div_one]
    _ ≤ (1+z-1)*(1+1/(1+z))/2 := h
    _ = z*(2+z)/(2*(1+z)) := by field_simp; ring

 theorem recurrence_density_upper {v : ℝ} (hv : 2 ≤ v) (hv3 : v ≤ 3) :
    wuLowerCoefficient v/v ≤ (v-2)/2-(v-2)^2/4 := by
  have hv0 : 0 < v := by linarith
  have hv1 : 0 < v-1 := by linarith
  have hl := log_chord_upper (z := v-2) (by linarith)
  have he : wuLowerCoefficient v = log (v-1) :=
    jr1965f_normalized_firstInterval hv (by linarith)
  rw [he]
  have hr : 1+(v-2) = v-1 := by ring
  rw [hr] at hl
  apply (div_le_iff₀ hv0).2
  apply hl.trans
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hv1)).2
  have hp := mul_nonneg (sq_nonneg (v-2)) (show 0 ≤ 3-v by linarith)
  nlinarith [mul_nonneg hv0.le hp]

 theorem upper_cubic {u : ℝ} (hu : 3 ≤ u) (hu4 : u ≤ 4) :
    wuUpperCoefficient u ≤ cubic u := by
  have hr := wuUpperCoefficient_sub_eq_integral (by norm_num : (2 : ℝ) ≤ 3) hu
  have he : wuUpperCoefficient 3 = 1 := jr1965F_normalized_initial (by norm_num) le_rfl
  have hab : 2 ≤ u-1 := by linarith
  have hc : Continuous (fun v : ℝ => (v-2)/2-(v-2)^2/4) := by fun_prop
  have hi := intervalIntegral.integral_mono_on hab
    (wuLowerCoefficient_div_intervalIntegrable (by norm_num) hab)
    (hc.intervalIntegrable 2 (u-1))
    (fun v hv => recurrence_density_upper hv.1 (by linarith [hv.2]))
  have hd (v : ℝ) (_hv : v ∈ uIcc 2 (u-1)) :
      HasDerivAt (fun v : ℝ => (v-2)^2/4-(v-2)^3/12)
        ((v-2)/2-(v-2)^2/4) v := by
    convert ((((hasDerivAt_id v).sub_const 2).pow 2).div_const 4).sub
      ((((hasDerivAt_id v).sub_const 2).pow 3).div_const 12) using 1 <;>
      first | rfl | (dsimp; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (hc.intervalIntegrable 2 (u-1))] at hi
  norm_num only [show (3 : ℝ)-1=2 by norm_num, he] at hr
  norm_num at hi
  dsimp [cubic]
  nlinarith

/-- Both sides concern the original normalized upper function, not a surrogate. -/
 theorem upper_two_sided {u : ℝ} (hu : 3 ≤ u) (hu4 : u ≤ 4) :
    1+(u-3)^2/9 ≤ wuUpperCoefficient u ∧ wuUpperCoefficient u ≤ cubic u :=
  ⟨SharpSingleBalance.upper_quadratic hu hu4, upper_cubic hu hu4⟩

end Wu2008DoubleSieve.VariableUpperEnvelope
