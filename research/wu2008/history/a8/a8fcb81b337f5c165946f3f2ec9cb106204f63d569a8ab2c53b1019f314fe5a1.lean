import MathlibNt.Wu2008DoubleSieve.FirstFeedbackTriangle
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedKernel

/-!
# The triangular exchange for the weighted first feedback

Wu (2004), author TeX lines 2594--2608. The arbitrary input below is only
interval integrable. The triangle theorem supplies absolute integrability
before the order of integration is changed, including coincident endpoints.
-/

namespace Wu2008DoubleSieve

open Set MeasureTheory Real
open scoped Interval

theorem firstFeedbackWeighted_triangle {A B c : ℝ} {f : ℝ → ℝ}
    (hA : 0 < A) (hAB : A ≤ B) (hBc : B < c)
    (hf : IntervalIntegrable f volume (A - 1) (B - 1)) :
    IntervalIntegrable (fun u =>
      (∫ x in (u - 1)..(B - 1), f x) * firstFeedbackWeightedKernel c u)
      volume A B ∧
    IntervalIntegrable (fun x =>
      f x * ∫ u in A..(x + 1), firstFeedbackWeightedKernel c u)
      volume (A - 1) (B - 1) ∧
    (∫ u in A..B, (∫ x in (u - 1)..(B - 1), f x) *
      firstFeedbackWeightedKernel c u) =
      ∫ x in (A - 1)..(B - 1),
        f x * ∫ u in A..(x + 1), firstFeedbackWeightedKernel c u := by
  have hk : ContinuousOn
      (fun p : ℝ × ℝ => firstFeedbackWeightedKernel c p.1)
      (Icc A ((B - 1) + 1) ×ˢ Icc (A - 1) (B - 1)) := by
    apply (firstFeedbackWeightedKernel_continuousOn hA hAB hBc).comp
      continuous_fst.continuousOn
    intro p hp
    rw [uIcc_of_le hAB]
    exact ⟨hp.1.1, by linarith [hp.1.2]⟩
  have h := firstFeedback_triangle (a := A) (c := B - 1) (d := 1)
    (k := fun u _ => firstFeedbackWeightedKernel c u) (by linarith) hf hk
  simpa only [sub_add_cancel, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_const_mul] using h

theorem firstFeedbackWeighted_exchange {f : ℝ → ℝ} {a b c : ℝ} (C : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (hc : 0 < c)
    (hac : 2 ≤ a * c) (hbc : b * c ≤ 4)
    (hf : IntervalIntegrable f volume 1 3) :
    IntervalIntegrable (fun u =>
      (C + ∫ x in (u - 1)..3, f x) * firstFeedbackWeightedKernel c u)
      volume (a * c) (b * c) ∧
    IntervalIntegrable (fun x =>
      f x * log ((1 - a) * (x + 1) / (a * (c - 1 - x))))
      volume (a * c - 1) (b * c - 1) ∧
    (∫ u in (a * c)..(b * c),
      (C + ∫ x in (u - 1)..3, f x) * firstFeedbackWeightedKernel c u) =
      log ((b - a * b) / (a - a * b)) *
        (C + ∫ x in (b * c - 1)..3, f x) +
      ∫ x in (a * c - 1)..(b * c - 1),
        f x * log ((1 - a) * (x + 1) / (a * (c - 1 - x))) := by
  have habc := mul_le_mul_of_nonneg_right hab hc.le
  have hbc' : b * c < c := by nlinarith
  have hfi {p q : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) (hq : q ≤ 3) :
      IntervalIntegrable f volume p q := by
    apply hf.mono_set
    rw [uIcc_of_le hpq, uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]
    intro x hx
    exact ⟨hp.trans hx.1, hx.2.trans hq⟩
  have htri := firstFeedbackWeighted_triangle (mul_pos ha hc) habc hbc'
    (hfi (by linarith : 1 ≤ a * c - 1) (by linarith) (by linarith : b * c - 1 ≤ 3))
  have hlog (x : ℝ) (hx : x ∈ Icc (a * c - 1) (b * c - 1)) :
      (∫ u in (a * c)..(x + 1), firstFeedbackWeightedKernel c u) =
        log ((1 - a) * (x + 1) / (a * (c - 1 - x))) :=
    firstFeedbackWeightedKernel_integral_partial ha hc hx.1 (by linarith [hx.2])
  have hirhs : IntervalIntegrable (fun x =>
      f x * log ((1 - a) * (x + 1) / (a * (c - 1 - x))))
      volume (a * c - 1) (b * c - 1) := by
    apply htri.2.1.congr
    intro x hx
    rw [uIoc_of_le (by linarith)] at hx
    dsimp only
    rw [hlog x ⟨hx.1.le, hx.2⟩]
  have hext :
      (∫ u in (a * c)..(b * c), (∫ x in (u - 1)..(b * c - 1), f x) *
        firstFeedbackWeightedKernel c u) =
      ∫ x in (a * c - 1)..(b * c - 1),
        f x * log ((1 - a) * (x + 1) / (a * (c - 1 - x))) := by
    rw [htri.2.2]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le (by linarith)]
    intro x hx
    dsimp only
    rw [hlog x hx]
  have hconst : IntervalIntegrable (fun u =>
      (C + ∫ x in (b * c - 1)..3, f x) * firstFeedbackWeightedKernel c u)
      volume (a * c) (b * c) :=
    ((firstFeedbackWeightedKernel_continuousOn (mul_pos ha hc) habc hbc').intervalIntegrable).const_mul _
  have hsplit (u : ℝ) (hu : u ∈ Icc (a * c) (b * c)) :
      (C + ∫ x in (u - 1)..3, f x) * firstFeedbackWeightedKernel c u =
      (C + ∫ x in (b * c - 1)..3, f x) * firstFeedbackWeightedKernel c u +
      (∫ x in (u - 1)..(b * c - 1), f x) * firstFeedbackWeightedKernel c u := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hfi (by linarith [hu.1]) (by linarith [hu.2]) (by linarith : b * c - 1 ≤ 3))
      (hfi (by linarith) (by linarith : b * c - 1 ≤ 3) (by norm_num))]
    ring
  refine ⟨?_, hirhs, ?_⟩
  · apply (hconst.add htri.1).congr
    intro u hu
    rw [uIoc_of_le habc] at hu
    exact (hsplit u ⟨hu.1.le, hu.2⟩).symm
  · calc
      _ = ∫ u in (a * c)..(b * c),
          ((C + ∫ x in (b * c - 1)..3, f x) * firstFeedbackWeightedKernel c u +
          (∫ x in (u - 1)..(b * c - 1), f x) * firstFeedbackWeightedKernel c u) := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le habc]
        exact hsplit
      _ = _ := by
        rw [intervalIntegral.integral_add hconst htri.1,
          intervalIntegral.integral_const_mul,
          firstFeedbackWeightedKernel_integral_scaled ha hab hb hc, hext]
        ring

end Wu2008DoubleSieve
