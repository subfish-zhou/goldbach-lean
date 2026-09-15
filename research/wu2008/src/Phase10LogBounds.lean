import Phase10AffineKernel

namespace Wu2008DoubleSieve.Phase10
open Real Set MeasureTheory
noncomputable section

/-- The unchanged window lies to the right of one half. -/
theorem window_denominator_upper {u : ℝ} (hu : u ∈ Icc (8/13 : ℝ) (129/179)) :
    u*(1-u) ≤ (40/169 : ℝ) := by
  have hp : 0 ≤ (u-8/13)*(u-5/13) := mul_nonneg
    (by linarith [hu.1]) (by linarith [hu.1])
  nlinarith only [hp]

/-- A strictly stronger universal kernel comparison, not a logarithm approximation. -/
theorem L_lower : (169/160 : ℝ)*(76979/393263) ≤ L := by
  have hf := HighSixPhase9.affine_integral (169/160 : ℝ)
  have hg := literal_affine_integral (1 : ℝ)
  norm_num only [one_mul] at hg
  rw [← hf, ← hg]
  have hi : IntervalIntegrable
      (fun u : ℝ => ((5/13)*(18/5-(179/50)*u))/(u*(1-u))) volume (8/13) (129/179) := by
    have he : (fun u : ℝ => ((5/13)*(18/5-(179/50)*u))/(u*(1-u))) =
        (fun u : ℝ => ((18/13)-(179/130)*u)/(u*(1-u))) := by
      funext u
      congr 1
      ring
    rw [he]
    exact weighted_affine_integrable (by norm_num) (by norm_num) (by norm_num) _ _
  apply intervalIntegral.integral_mono_on (by norm_num)
    (by apply Continuous.intervalIntegrable; fun_prop) hi
  intro u hu
  have hd := window_denominator_upper hu
  have hp : 0 ≤ (5/13 : ℝ)*(18/5-(179/50)*u) :=
    mul_nonneg (by norm_num) (by linarith [hu.2])
  have hh := mul_le_mul_of_nonneg_left hd hp
  apply (le_div_iff₀ (mul_pos (by linarith [hu.1]) (by linarith [hu.2]))).2
  nlinarith only [hh]

theorem L_strict : (76979/393263 : ℝ) < L := by
  linarith only [L_lower]

def rhoLog : ℝ := (289/5200)+L/2

/-- Only the universal log inequality is used for the upper contraction bound. -/
theorem rhoLog_upper : rhoLog ≤ (424659/2420080 : ℝ) := by
  have h1 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1677/1432)
  have h2 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 179/130)
  unfold rhoLog L
  linarith only [h1,h2]

theorem rhoLog_bounds : 0 < rhoLog ∧ rhoLog < 1 := by
  constructor
  · unfold rhoLog
    linarith only [L_lower]
  · linarith only [rhoLog_upper]

end
end Wu2008DoubleSieve.Phase10
