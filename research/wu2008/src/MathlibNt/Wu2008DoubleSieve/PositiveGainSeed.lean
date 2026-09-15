import MathlibNt.Wu2008DoubleSieve.PositiveGainEnvelope
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Wu2008DoubleSieve
open Real Set MeasureTheory
open scoped Interval

private theorem positiveGain_loss_le :
    (∫ v in (2 : ℝ)..(21/10), log (v-1)/v) ≤ 1/400 := by
  have hc : ContinuousOn (fun v : ℝ => log (v-1)/v) (Icc 2 (21/10)) := by
    apply ContinuousOn.div
    · apply ContinuousOn.log (by fun_prop)
      intro v hv
      linarith [hv.1]
    · fun_prop
    · intro v hv
      linarith [hv.1]
  calc
    _ ≤ ∫ v in (2 : ℝ)..(21/10), (v-2)/2 := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (hc.intervalIntegrable_of_Icc (by norm_num))
        ((by fun_prop : Continuous (fun v : ℝ => (v-2)/2)).intervalIntegrable _ _)
      intro v hv
      have hp : 0 < v := by linarith [hv.1]
      exact (div_le_div_of_nonneg_right
        (show log (v-1) ≤ v-2 by
          have := log_le_sub_one_of_pos (show 0 < v-1 by linarith [hv.1])
          linarith) hp.le).trans
        (div_le_div_of_nonneg_left (by linarith [hv.1]) (by norm_num) hv.1)
    _ = _ := by
      rw [intervalIntegral.integral_div,
        intervalIntegral.integral_sub (f := fun v : ℝ => v) (g := fun _ : ℝ => (2 : ℝ))
          (continuous_id.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _)]
      norm_num [integral_id]

private theorem positiveGain_log_minorant {u : ℝ} (hu : u ∈ Icc (19/29 : ℝ) (21/31)) :
    (841/209 : ℝ)*((31/10)*u-2) ≤ log ((31/10)*u-1)/(u*(1-u)) := by
  let z := (31/10 : ℝ)*u-1
  have hz1 : 1 ≤ z := by dsimp [z]; linarith [hu.1]
  have hzhi : z ≤ 11/10 := by dsimp [z]; linarith [hu.2]
  have hz0 : 0 < z := by linarith
  have hlog : (10/11 : ℝ)*(z-1) ≤ log z := by
    have hh := one_sub_inv_le_log_of_pos hz0
    have he : 1-z⁻¹ = (z-1)/z := by field_simp
    rw [he] at hh
    apply le_trans ?_ hh
    apply (le_div_iff₀ hz0).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hz1) (sub_nonneg.mpr hzhi)]
  have hd0 : 0 < u*(1-u) := by
    apply mul_pos <;> linarith [hu.1, hu.2]
  have hd : u*(1-u) ≤ 190/841 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu.1)
      (show 0 ≤ u+19/29-1 by linarith [hu.1])]
  apply (le_div_iff₀ hd0).mpr
  calc
    _ ≤ ((841/209 : ℝ)*((31/10)*u-2))*(190/841) :=
      mul_le_mul_of_nonneg_left hd (by dsimp [z] at hz1; nlinarith)
    _ = (10/11 : ℝ)*(z-1) := by dsimp [z]; ring
    _ ≤ _ := hlog

private theorem positiveGain_gain_ge :
    (1/341 : ℝ) ≤ (1/2)*(∫ u in (19/29 : ℝ)..(21/31),
      log ((31/10)*u-1)/(u*(1-u))) := by
  have hc : ContinuousOn (fun u : ℝ => log ((31/10)*u-1)/(u*(1-u)))
      (Icc (19/29) (21/31)) := by
    apply ContinuousOn.div
    · apply ContinuousOn.log (by fun_prop)
      intro u hu
      linarith [hu.1]
    · fun_prop
    · intro u hu
      apply ne_of_gt
      apply mul_pos <;> linarith [hu.1, hu.2]
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (19/29 : ℝ) ≤ 21/31)
    ((by fun_prop : Continuous (fun u : ℝ => (841/209)*((31/10)*u-2))).intervalIntegrable _ _)
    (hc.intervalIntegrable_of_Icc (by norm_num)) (fun _ hu => positiveGain_log_minorant hu)
  have he : (∫ u in (19/29 : ℝ)..(21/31), (841/209)*((31/10)*u-2)) = 2/341 := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (f := fun u : ℝ => (31/10)*u)
        (g := fun _ : ℝ => (2 : ℝ))
        ((continuous_const.mul continuous_id).intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const_mul]
    norm_num [integral_id]
  rw [he] at hi
  linarith

/-- A purely analytic strict seed at (s,t)=(29/10,31/10), paying the full fixed-delta loss.
This is not the final 0.899 counting bound. -/
theorem positiveGain_explicit_seed {δ : ℝ} (hδ : δ ≤ 1/10) :
    (1/5000 : ℝ) ≤
      -(∫ v in (2 : ℝ)..(21/10), log (v-1)/v) +
      (1/2)*(∫ u in (19/29 : ℝ)..(21/31), log ((31/10)*u-1)/(u*(1-u))) -
      omega3XIntegralEnvelope (29/10) (31/10)/(1-2*δ) := by
  have hi := positiveGain_envelope_le_simplex
    (by norm_num : (2 : ℝ) ≤ 29/10) (by norm_num : (29/10 : ℝ) ≤ 31/10)
    (by norm_num : (31/10 : ℝ) ≤ 10)
  norm_num at hi
  have hd : 0 < 1-2*δ := by linarith
  have hp : omega3XIntegralEnvelope (29/10) (31/10)/(1-2*δ) ≤ 31/146334 := by
    apply (div_le_iff₀ hd).mpr
    linarith
  linarith [positiveGain_loss_le, positiveGain_gain_ge]

end Wu2008DoubleSieve
