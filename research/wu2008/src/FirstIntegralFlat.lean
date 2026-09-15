import FirstPublicationAudit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section
open Real Set MeasureTheory
open scoped Interval
open Wu08OriginalFirstSteps
namespace FirstIntegralRecovery

/-- FTC on the original moving inner endpoint. -/
theorem B_hasDerivAt (x : ℝ) : HasDerivAt B (k (x-1)) x := by
  change HasDerivAt (fun z : ℝ => ∫ v in (2:ℝ)..(z-1), k v) (k (x-1)) x
  have h := intervalIntegral.integral_hasDerivAt_right
    (k_continuous.intervalIntegrable (μ := volume) 2 (x-1))
    k_continuous.stronglyMeasurable.stronglyMeasurableAtFilter
    k_continuous.continuousAt
  simpa only [B, Function.comp_def, id_eq, mul_one] using h.comp x ((hasDerivAt_id x).sub_const 1)

/-- Integration by parts pays the entire triangular domain without a new cut. -/
theorem C_parts {s : ℝ} (hs : 4 ≤ s) :
    C s = B (s-1)*log (s-1) - ∫ v in (3:ℝ)..(s-1), k (v-1)*log v := by
  have ho : (3:ℝ) ≤ s-1 := by linarith
  have hl : ContinuousOn log (uIcc (3:ℝ) (s-1)) := by
    apply continuousOn_id.log
    intro x hx
    rw [uIcc_of_le ho] at hx
    exact (show 0 < x by linarith [hx.1]).ne'
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := B) (v := log) (u' := fun v => k (v-1)) (v' := fun v => 1/v)
    B_continuous.continuousOn hl
    (fun x _ => B_hasDerivAt x)
    (fun x hx => by
      rw [min_eq_left ho,max_eq_right ho] at hx
      simpa only [one_div] using hasDerivAt_log (show x ≠ 0 by linarith [hx.1]))
    ((k_continuous.comp (continuous_id.sub continuous_const)).intervalIntegrable 3 (s-1))
    (reciprocal_integrable (by norm_num) ho)
  have hc : C s = ∫ v in (3:ℝ)..(s-1), B v*(1/v) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le ho] at hv
    dsimp only
    rw [max_eq_right (show (1:ℝ) ≤ v by linarith [hv.1])]
    ring
  rw [hc,h]
  norm_num [B]

/-- The conjectured one-dimensional representation, now derived from actual C. -/
theorem C_flat {s : ℝ} (hs : 4 ≤ s) :
    C s = ∫ u in (2:ℝ)..(s-2), log (u-1)/u * log ((s-1)/(u+1)) := by
  have ho : (2:ℝ) ≤ s-2 := by linarith
  have hk := k_continuous.intervalIntegrable (μ := volume) 2 (s-2)
  have hlog : ContinuousOn (fun u : ℝ => log (u+1)) (uIcc (2:ℝ) (s-2)) := by
    apply (continuousOn_id.add continuousOn_const).log
    intro u hu
    rw [uIcc_of_le ho] at hu
    exact (show 0 < u+1 by linarith [hu.1]).ne'
  have hshift : (∫ v in (3:ℝ)..(s-1), k (v-1)*log v) =
      ∫ u in (2:ℝ)..(s-2), k u*log (u+1) := by
    have h := intervalIntegral.integral_comp_sub_right
      (a := (3:ℝ)) (b := s-1) (fun u : ℝ => k u*log (u+1)) 1
    simp only [sub_add_cancel] at h
    convert h using 1
    congr 1 <;> ring
  rw [C_parts hs,hshift]
  have hb : B (s-1) = ∫ u in (2:ℝ)..(s-2), k u := by
    unfold B
    congr 1
    ring
  rw [hb, ← intervalIntegral.integral_mul_const,
    ← intervalIntegral.integral_sub (hk.mul_const _) (hk.mul_continuousOn hlog)]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ho] at hu
  dsimp only
  rw [k_literal hu.1,log_div (show s-1 ≠ 0 by linarith)
    (show u+1 ≠ 0 by linarith [hu.1])]
  ring

end FirstIntegralRecovery
