import MathlibNt.Wu2008DoubleSieve.ImprovementMonotonicity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Integrability and the ordered depth limit

The source integral comparisons require integration of the actual limiting
gains. Effective-coefficient monotonicity supplies integrability without
assuming continuity of H or h. Dominated convergence then passes the already
constructed fixed-depth limits through the integral. This does not prove
the Buchstab/reboxing inequality whose terms these integrals will represent.
-/

namespace Wu2008DoubleSieve

open Finset Set Filter Real MeasureTheory
open scoped Classical Topology Interval
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

theorem continuousOn_wuUpperCoefficient :
    ContinuousOn wuUpperCoefficient (Ioi 0) :=
  (continuousOn_id.mul continuousOn_jr1965F).div_const _

theorem continuousOn_wuLowerCoefficient :
    ContinuousOn wuLowerCoefficient (Ioi 0) :=
  (continuousOn_id.mul continuousOn_jr1965f).div_const _

theorem wuImprovementAtInfinity_intervalIntegrable (upper : Bool) (k : ℕ) (hk : 1 ≤ k)
    {δ a b : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 10) :
    IntervalIntegrable (wuImprovementAtInfinity upper k δ) volume a b := by
  have hsub : uIcc a b ⊆ Ioi (0 : ℝ) := by
    rw [uIcc_of_le hab]
    intro x hx
    exact lt_of_lt_of_le (by linarith : (0 : ℝ) < a) hx.1
  cases upper
  · have hm : MonotoneOn (fun s => wuLowerCoefficient s +
        wuImprovementAtInfinity false k δ s) (uIcc a b) := by
      rw [uIcc_of_le hab]
      intro s hs t ht hst
      exact wu_effective_lower_fixed_depth_mono k hk hδ hδhi
        (ha.trans hs.1) hst (ht.2.trans hb)
    have hi := hm.intervalIntegrable (μ := volume)
    have hc := (continuousOn_wuLowerCoefficient.mono hsub).intervalIntegrable (μ := volume)
    convert hi.sub hc using 1
    ext s
    ring
  · have hm : MonotoneOn (fun s => wuUpperCoefficient s -
        wuImprovementAtInfinity true k δ s) (uIcc a b) := by
      rw [uIcc_of_le hab]
      intro s hs t ht hst
      exact wu_effective_upper_fixed_depth_mono k hk hδ hδhi
        (ha.trans hs.1) hst (ht.2.trans hb)
    have hi := hm.intervalIntegrable (μ := volume)
    have hc := (continuousOn_wuUpperCoefficient.mono hsub).intervalIntegrable (μ := volume)
    convert hc.sub hi using 1
    ext s
    ring

theorem wuImprovementLimit_intervalIntegrable (upper : Bool) {δ a b : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 10) :
    IntervalIntegrable (wuImprovementLimit upper δ) volume a b := by
  have hsub : uIcc a b ⊆ Ioi (0 : ℝ) := by
    rw [uIcc_of_le hab]
    intro x hx
    exact lt_of_lt_of_le (by linarith : (0 : ℝ) < a) hx.1
  cases upper
  · have hm : MonotoneOn (fun s => wuLowerCoefficient s +
        wuImprovementLimit false δ s) (uIcc a b) := by
      rw [uIcc_of_le hab]
      intro s hs t ht hst
      exact wu_effective_lower_limit_mono hδ hδhi
        (ha.trans hs.1) hst (ht.2.trans hb)
    have hi := hm.intervalIntegrable (μ := volume)
    have hc := (continuousOn_wuLowerCoefficient.mono hsub).intervalIntegrable (μ := volume)
    convert hi.sub hc using 1
    ext s
    ring
  · have hm : MonotoneOn (fun s => wuUpperCoefficient s -
        wuImprovementLimit true δ s) (uIcc a b) := by
      rw [uIcc_of_le hab]
      intro s hs t ht hst
      exact wu_effective_upper_limit_mono hδ hδhi
        (ha.trans hs.1) hst (ht.2.trans hb)
    have hi := hm.intervalIntegrable (μ := volume)
    have hc := (continuousOn_wuUpperCoefficient.mono hsub).intervalIntegrable (μ := volume)
    convert hc.sub hi using 1
    ext s
    ring

theorem wuImprovementAtInfinity_div_intervalIntegrable (upper : Bool) (k : ℕ) (hk : 1 ≤ k)
    {δ a b : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 10) :
    IntervalIntegrable (fun t => wuImprovementAtInfinity upper k δ t / t) volume a b := by
  have hc : ContinuousOn (fun t : ℝ => t⁻¹) (uIcc a b) := by
    apply continuousOn_id.inv₀
    rw [uIcc_of_le hab]
    intro t ht
    change t ≠ 0
    linarith [ht.1]
  simpa only [div_eq_mul_inv] using
    (wuImprovementAtInfinity_intervalIntegrable upper k hk hδ hδhi ha hab hb).mul_continuousOn hc

theorem wuImprovementLimit_div_intervalIntegrable (upper : Bool) {δ a b : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 10) :
    IntervalIntegrable (fun t => wuImprovementLimit upper δ t / t) volume a b := by
  have hc : ContinuousOn (fun t : ℝ => t⁻¹) (uIcc a b) := by
    apply continuousOn_id.inv₀
    rw [uIcc_of_le hab]
    intro t ht
    change t ≠ 0
    linarith [ht.1]
  simpa only [div_eq_mul_inv] using
    (wuImprovementLimit_intervalIntegrable upper hδ hδhi ha hab hb).mul_continuousOn hc

/-- A depth-independent integrable majorant for both actual gains. -/
theorem wuImprovementAtInfinity_div_norm_le_ten (upper : Bool) (k : ℕ) (hk : 1 ≤ k)
    {δ s : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hs10 : s ≤ 10) :
    ‖wuImprovementAtInfinity upper k δ s / s‖ ≤ 10 := by
  have hs0 : 0 < s := by linarith
  have hH := wuImprovementAtInfinity_nonneg upper k hk hδ hδhi hs hs10
  have ha : 0 ≤ wuLowerCoefficient s :=
    div_nonneg (mul_nonneg hs0.le (jr1965f_nonneg hs0)) (by positivity)
  have hA : wuUpperCoefficient s ≤ 10 := by
    unfold wuUpperCoefficient
    apply (div_le_iff₀ (by positivity : 0 < 2 * exp eulerMascheroniConstant)).2
    have hf := mul_le_mul_of_nonneg_left (jr1965F_le_delayConstant hs) hs0.le
    unfold jr1965DelayConstant at hf
    nlinarith [exp_pos eulerMascheroniConstant]
  have hbound : wuImprovementAtInfinity upper k δ s ≤ 10 := by
    cases upper
    · have h := wuImprovementAtInfinity_lower_bound hk hδ hδhi hs hs10
      linarith
    · exact (wuImprovementAtInfinity_upper_bound hk hδ hδhi hs hs10).trans hA
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hH hs0.le)]
  apply (div_le_iff₀ hs0).2
  linarith

/-- The depth limit commutes with the source integral at fixed delta.
This occurs after the threshold limit, never simultaneously with it. -/
theorem wuImprovement_integral_depth_limit (upper : Bool) {δ a b : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 10) :
    Tendsto (fun k : ℕ => ∫ t in a..b, wuImprovementAtInfinity upper (k + 1) δ t / t)
      atTop (𝓝 (∫ t in a..b, wuImprovementLimit upper δ t / t)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 10)
  · exact Eventually.of_forall (fun k =>
      (wuImprovementAtInfinity_div_intervalIntegrable upper (k + 1) (by omega)
        hδ hδhi ha hab hb).def'.aestronglyMeasurable)
  · apply Eventually.of_forall
    intro k
    apply ae_of_all
    intro t ht
    rw [uIoc_of_le hab] at ht
    exact wuImprovementAtInfinity_div_norm_le_ten upper (k + 1) (by omega)
      hδ hδhi (ha.trans ht.1.le) (ht.2.trans hb)
  · exact intervalIntegrable_const
  · apply ae_of_all
    intro t ht
    rw [uIoc_of_le hab] at ht
    exact (wuImprovementAtInfinity_tendsto upper hδ hδhi
      (ha.trans ht.1.le) (ht.2.trans hb)).div_const t

end Wu2008DoubleSieve
