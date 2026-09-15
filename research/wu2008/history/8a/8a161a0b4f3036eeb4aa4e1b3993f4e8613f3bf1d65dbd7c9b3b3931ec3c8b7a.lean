import MathlibNt.Wu2008DoubleSieve.TableFeedbackRows

/-!
# The zero-scalar row retains nonzero feedback

Positivity of a literal logarithmic tail integral suffices; no integral
value or table entry is numerically evaluated.
-/

namespace Wu2008DoubleSieve

open Set Real MeasureTheory
open scoped Interval

theorem tableFeedback_last_matrix_entry_pos : 0 < tableFeedbackMatrix 4 8 := by
  let f : ℝ → ℝ := fun x => 1 / (2 * x) * log ((x + 1) ^ 2 / ((3 - 1) * (3 - 1)))
  have hsub : Icc (29 / 10 : ℝ) 3 ⊆ Icc (1 : ℝ) 3 := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hpos : ∀ x ∈ Icc (29 / 10 : ℝ) 3, 0 < f x := by
    intro x hx
    apply mul_pos (div_pos (by norm_num) (by linarith [hx.1]))
    apply Real.log_pos
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < (3 - 1) * (3 - 1))).mpr
    nlinarith [hx.1]
  have hcont : ContinuousOn f (Icc (29 / 10 : ℝ) 3) :=
    (firstFeedbackXi_tail_continuousOn (s := 3) (t := 3)
      (by norm_num) (by norm_num)).mono hsub
  have hi : 0 < ∫ x in (29 / 10 : ℝ)..3, f x :=
    intervalIntegral.integral_pos (by norm_num) hcont
      (fun x hx => (hpos x ⟨hx.1.le, hx.2⟩).le)
      ⟨3, ⟨by norm_num, le_rfl⟩, hpos 3 ⟨by norm_num, le_rfl⟩⟩
  have hK := firstFeedbackXi_intervalIntegrable (s := 3) (t := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hf : IntervalIntegrable f volume (29 / 10) 3 :=
    (show ContinuousOn f (uIcc (29 / 10 : ℝ) 3) by
      rwa [uIcc_of_le (by norm_num : (29 / 10 : ℝ) ≤ 3)]).intervalIntegrable
  have hmono : (∫ x in (29 / 10 : ℝ)..3, f x) ≤
      ∫ x in (29 / 10 : ℝ)..3, firstFeedbackXi x 3 3 := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      hf (hK.mono_set ?_)
    · intro x hx
      have ht : (Icc ((3 : ℝ) - 2) 3).indicator (fun _ : ℝ => (1 : ℝ)) x = 1 := by
        apply indicator_of_mem
        norm_num
        exact hsub hx
      have hm : (Icc ((3 : ℝ) - 3 / 3 - 1) (3 - 2)).indicator
          (fun _ : ℝ => (1 : ℝ)) x = 0 := by
        apply indicator_of_notMem
        norm_num
        linarith [hx.1]
      have hb : 0 ≤ firstFeedbackSigmaZero x / (2 * x) *
          log (16 / (((3 : ℝ) - 1) * (3 - 1))) :=
        mul_nonneg (div_nonneg (firstFeedbackSigmaZero_nonneg (hsub hx))
          (by linarith [hx.1])) (Real.log_nonneg (by norm_num))
      change f x ≤ _
      rw [firstFeedbackXi, ht, hm]
      simp only [zero_div, zero_mul, add_zero]
      change f x ≤ _ + f x
      linarith
    · rw [uIcc_of_le (by norm_num : (29 / 10 : ℝ) ≤ 3),
        uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]
      exact hsub
  have hs : tableFeedbackS 4 = 3 := by norm_num [tableFeedbackS]
  have ht : tableFeedbackT 4 = 3 := rfl
  change 0 < ∫ x in tableFeedbackR 8..tableFeedbackR (8 + 1),
    firstFeedbackXi x (tableFeedbackS 4) (tableFeedbackT 4)
  rw [hs, ht]
  norm_num only [tableFeedbackR, Nat.cast_ofNat, show (8 : ℕ) ≠ 0 by decide,
    show (8 + 1 : ℕ) ≠ 0 by decide, if_false]
  exact hi.trans_le hmono

end Wu2008DoubleSieve
