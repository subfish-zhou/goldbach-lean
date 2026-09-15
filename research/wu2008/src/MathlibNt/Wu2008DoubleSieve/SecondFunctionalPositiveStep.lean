import MathlibNt.Wu2008DoubleSieve.SecondFunctionalCoupledFeedbackRows

/-! Right-endpoint lower sums for a nonnegative density on an arbitrary finite grid. -/
namespace Wu2008DoubleSieve.SecondFunctionalPositive
open Set MeasureTheory
open scoped BigOperators Interval

 theorem restrict_integrable {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 1 3)
    {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 3) :
    IntervalIntegrable f volume a b := by
  apply hf.mono_set
  rw [uIcc_of_le hab, uIcc_of_le (show (1:ℝ) ≤ 3 by norm_num)]
  exact Icc_subset_Icc ha hb

/-- The tail is retained, so this is not a truncated integral identity. -/
theorem step_lower_with_tail (n : ℕ) (g : ℕ → ℝ) (hg0 : g 0 = 1)
    (hg : StrictMonoOn g (Iic n)) (hb : ∀ k ≤ n, g k ∈ Icc 1 3)
    (H d : ℝ → ℝ) (hH : AntitoneOn H (Icc 1 3))
    (hd0 : ∀ x ∈ Icc 1 3, 0 ≤ d x)
    (hd : IntervalIntegrable d volume 1 3)
    (hHd : IntervalIntegrable (fun x => H x * d x) volume 1 3) :
    (∑ k ∈ Finset.range n, (∫ x in g k..g (k+1), d x) * H (g (k+1))) +
      (∫ x in g n..3, H x * d x) ≤ ∫ x in (1:ℝ)..3, H x * d x := by
  have hseg (k : ℕ) (hk : k < n) : g k ≤ g (k+1) :=
    (hg (by exact Nat.le_of_lt hk) (by exact hk) (Nat.lt_succ_self k)).le
  have hprod (k : ℕ) (hk : k < n) :
      IntervalIntegrable (fun x => H x * d x) volume (g k) (g (k+1)) :=
    restrict_integrable hHd (hb k (Nat.le_of_lt hk)).1 (hseg k hk) (hb (k+1) hk).2
  have hs : (∑ k ∈ Finset.range n, (∫ x in g k..g (k+1), d x) * H (g (k+1))) ≤
      ∑ k ∈ Finset.range n, ∫ x in g k..g (k+1), H x * d x := by
    apply Finset.sum_le_sum
    intro k hk
    have hkn := Finset.mem_range.mp hk
    have hdi := restrict_integrable hd (hb k (Nat.le_of_lt hkn)).1
      (hseg k hkn) (hb (k+1) hkn).2
    rw [mul_comm, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (hseg k hkn) (hdi.const_mul _) (hprod k hkn)
    intro x hx
    have hx13 : x ∈ Icc (1:ℝ) 3 :=
      ⟨(hb k (Nat.le_of_lt hkn)).1.trans hx.1, hx.2.trans (hb (k+1) hkn).2⟩
    exact mul_le_mul_of_nonneg_right (hH hx13 (hb (k+1) hkn) hx.2) (hd0 x hx13)
  rw [intervalIntegral.sum_integral_adjacent_intervals hprod, hg0] at hs
  have hn := hb n le_rfl
  have he := intervalIntegral.integral_add_adjacent_intervals
    (restrict_integrable hHd (by norm_num) hn.1 hn.2)
    (restrict_integrable hHd hn.1 hn.2 (by norm_num))
  linarith only [hs, he]

 theorem tail_nonnegative (H d : ℝ → ℝ) {a : ℝ} (ha : a ∈ Icc 1 3)
    (hH : ∀ x ∈ Icc 1 3, 0 ≤ H x) (hd : ∀ x ∈ Icc 1 3, 0 ≤ d x) :
    0 ≤ ∫ x in a..3, H x * d x := by
  apply intervalIntegral.integral_nonneg ha.2
  intro x hx
  have hx13 : x ∈ Icc (1:ℝ) 3 := ⟨ha.1.trans hx.1, hx.2⟩
  exact mul_nonneg (hH x hx13) (hd x hx13)

/-- Discarding the nonnegative tail only weakens the lower bound. -/
theorem step_lower (n : ℕ) (g : ℕ → ℝ) (hg0 : g 0 = 1)
    (hg : StrictMonoOn g (Iic n)) (hb : ∀ k ≤ n, g k ∈ Icc 1 3)
    (H d : ℝ → ℝ) (hH : AntitoneOn H (Icc 1 3))
    (hH0 : ∀ x ∈ Icc 1 3, 0 ≤ H x) (hd0 : ∀ x ∈ Icc 1 3, 0 ≤ d x)
    (hd : IntervalIntegrable d volume 1 3)
    (hHd : IntervalIntegrable (fun x => H x * d x) volume 1 3) :
    (∑ k ∈ Finset.range n, (∫ x in g k..g (k+1), d x) * H (g (k+1))) ≤
      ∫ x in (1:ℝ)..3, H x * d x := by
  have ht := tail_nonnegative H d (hb n le_rfl) hH0 hd0
  have hs := step_lower_with_tail n g hg0 hg hb H d hH hd0 hd hHd
  linarith only [ht, hs]

end Wu2008DoubleSieve.SecondFunctionalPositive
