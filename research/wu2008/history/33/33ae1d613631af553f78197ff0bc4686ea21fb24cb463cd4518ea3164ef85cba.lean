import MathlibNt.Wu2008DoubleSieve.FirstFeedbackTriangle
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Continuity of the first-feedback triangular expression

The source (Wu 2004, Lemma 6.1, (6.4)) identifies the triangular logarithmic
expression with an indefinite integral. Its continuity therefore follows
from integrability of the input, not from continuity of the gain function.
-/

namespace Wu2008DoubleSieve

open Set MeasureTheory Real
open scoped Interval

theorem firstFeedback_source64_nested_continuousOn {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 1 3) :
    ContinuousOn (fun v => ∫ u in (v - 1)..4, (∫ x in (u - 1)..3, f x) / u)
      (Icc 3 5) := by
  have hi : IntervalIntegrable (fun u => (∫ x in (u - 1)..3, f x) / u) volume 2 4 := by
    simpa only [show (3 : ℝ) - 1 = 2 by norm_num] using
      (firstFeedback_source64 hf (v := 3) (by norm_num) (by norm_num)).1
  have hp := intervalIntegral.continuousOn_primitive_interval_left ((intervalIntegrable_iff').mp hi)
  apply hp.comp (continuous_id.sub continuous_const).continuousOn
  rw [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)]
  intro v hv
  change 2 ≤ v - 1 ∧ v - 1 ≤ 4
  exact ⟨by linarith [hv.1], by linarith [hv.2]⟩

theorem firstFeedback_source64_continuousOn {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 1 3) :
    ContinuousOn (fun v => ∫ x in (v - 2)..3, f x * log ((x + 1) / (v - 1)))
      (Icc 3 5) := by
  apply (firstFeedback_source64_nested_continuousOn hf).congr
  intro v hv
  exact (firstFeedback_source64 hf hv.1 hv.2).2.2.symm

theorem firstFeedback_source64_intervalIntegrable {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 1 3) :
    IntervalIntegrable
      (fun v => ∫ x in (v - 2)..3, f x * log ((x + 1) / (v - 1))) volume 3 5 := by
  apply ContinuousOn.intervalIntegrable
  simpa only [uIcc_of_le (by norm_num : (3 : ℝ) ≤ 5)] using
    firstFeedback_source64_continuousOn hf

theorem firstFeedback_scalar_continuousOn {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 1 3) :
    ContinuousOn
      (fun v => (∫ x in (v - 2)..3, f x * log ((x + 1) / (v - 1))) / v)
      (Icc 3 5) := by
  apply (firstFeedback_source64_continuousOn hf).div continuousOn_id
  intro v hv
  change v ≠ 0
  linarith [hv.1]

end Wu2008DoubleSieve
