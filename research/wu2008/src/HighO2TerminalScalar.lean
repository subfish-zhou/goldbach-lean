import HighO2TerminalLocal
import MathlibNt.Wu2008DoubleSieve.Omega2CanonicalIntegral

namespace HighO2Terminal
open Real Wu2008DoubleSieve
open scoped Interval
noncomputable section

/-- This global extension changes no value in the original domain. -/
theorem logCoefficient_monotone (ε : ℝ) : Monotone (logCoefficient ε) := by
  intro x y hxy
  dsimp [logCoefficient]
  apply sub_le_sub_right
  exact log_le_log (by have := le_max_left (2 : ℝ) x; linarith)
    (sub_le_sub_right (max_le_max_left 2 hxy) 1)

theorem logCoefficient_bounded {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ∀ u ∈ Set.Icc (1 : ℝ) 10, |logCoefficient ε u| ≤ 11 := by
  intro u hu
  have hmlo : 2 ≤ max 2 u := le_max_left _ _
  have hmhi : max 2 u ≤ 10 := max_le (by norm_num) hu.2
  have hlog0 : 0 ≤ log (max 2 u-1) := log_nonneg (by linarith)
  have hloghi := log_le_sub_one_of_pos (show 0 < max 2 u-1 by linarith)
  dsimp [logCoefficient]
  rw [abs_le]
  constructor <;> linarith

/-- Universal kernel mass on the original moving domain; no numerical
quadrature, new split point, or asymptotic kernel replacement is used. -/
theorem kernel_integral_le {s t : ℝ}
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : 3 ≤ t) (ht5 : t ≤ 5) :
    (∫ u in (1-1/s)..(1-1/t), (1 : ℝ)/(u*(1-u))) ≤ 10 := by
  have hab : 1-1/s ≤ 1-1/t :=
    sub_le_sub_left (one_div_le_one_div_of_le (by linarith) hst) 1
  have hint := omega2_integral_intervalIntegrable
    (f := fun _ => (1 : ℝ)) (fun _ _ _ _ _ => le_rfl) hs hst ht ht5
  have hm : (∫ u in (1-1/s)..(1-1/t), (1 : ℝ)/(u*(1-u))) ≤
      ∫ _u in (1-1/s)..(1-1/t), (10 : ℝ) := by
    apply intervalIntegral.integral_mono_on hab hint intervalIntegrable_const
    intro u hu
    have hh := omega2_integral_domain hs hst ht ht5 (by rwa [Set.uIcc_of_le hab])
    have hden : 1/10 ≤ u*(1-u) := by
      have := mul_le_mul hh.1 (show (1 : ℝ)/5 ≤ 1-u by linarith [hh.2.1])
        (by norm_num : (0 : ℝ) ≤ 1/5) (by linarith [hh.1] : 0 ≤ u)
      nlinarith
    exact (div_le_iff₀ (show 0 < u*(1-u) by linarith)).mpr (by linarith)
  rw [intervalIntegral.integral_const] at hm
  simp only [smul_eq_mul] at hm
  have hsi : 1/s ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hs
  have hti : 0 ≤ 1/t := by positivity
  linarith

/-- Removing the local density slack returns the exact printed log kernel.
All integrations are certified before subtracting the functions. -/
theorem log_integral_slack {ε s t : ℝ} (hε : 0 ≤ ε)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : 3 ≤ t) (ht5 : t ≤ 5) (hc : 2 ≤ t-t/s) :
    (∫ u in (1-1/s)..(1-1/t), log (t*u-1)/(u*(1-u))) - 40*ε ≤
      ∫ u in (1-1/s)..(1-1/t), logCoefficient ε (t*u)/(u*(1-u)) := by
  have hf := omega2_integral_intervalIntegrable ((logCoefficient_monotone 0).monotoneOn _) hs hst ht ht5
  have hk := omega2_integral_intervalIntegrable
    (f := fun _ => (1 : ℝ)) (fun _ _ _ _ _ => le_rfl) hs hst ht ht5
  have heq : (∫ u in (1-1/s)..(1-1/t), logCoefficient ε (t*u)/(u*(1-u))) =
      (∫ u in (1-1/s)..(1-1/t), logCoefficient 0 (t*u)/(u*(1-u))) -
      4*ε*(∫ u in (1-1/s)..(1-1/t), (1 : ℝ)/(u*(1-u))) := by
    rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_sub hf (hk.const_mul (4*ε))]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp [logCoefficient]
    ring
  have hlog : (∫ u in (1-1/s)..(1-1/t), logCoefficient 0 (t*u)/(u*(1-u))) =
      ∫ u in (1-1/s)..(1-1/t), log (t*u-1)/(u*(1-u)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hp := omega2_canonical_parameter_mem hs hst ht5 hc hu
    simp only [logCoefficient,max_eq_right hp.1,mul_zero,sub_zero]
  rw [heq,hlog]
  nlinarith [mul_le_mul_of_nonneg_left (kernel_integral_le hs hst ht ht5) (show 0 ≤ 4*ε by positivity)]

end
end HighO2Terminal
