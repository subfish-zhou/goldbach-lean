import MathlibNt.Wu2008DoubleSieve.FirstFeedback

/-!
# Right-endpoint integration of the actual upper gain

Adjacent interval integrals telescope. No disjointness of closed cells
is asserted at their shared endpoints.
-/

namespace Wu2008DoubleSieve

open Set Real MeasureTheory
open scoped BigOperators Interval

theorem tableFeedback_cell_subset {r : ℕ → ℝ} {n k : ℕ}
    (hr : Monotone r) (hfirst : r 0 = 1) (hlast : r n = 3) (hk : k < n) :
    uIcc (r k) (r (k + 1)) ⊆ uIcc (1 : ℝ) 3 := by
  rw [uIcc_of_le (hr (Nat.le_succ k)), uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]
  intro x hx
  have hleft := hr (Nat.zero_le k)
  have hright := hr (show k + 1 ≤ n by omega)
  rw [hfirst] at hleft
  rw [hlast] at hright
  exact ⟨hleft.trans hx.1, hx.2.trans hright⟩

theorem tableFeedback_partition_lower {δ : ℝ} {r : ℕ → ℝ} {n : ℕ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hr : Monotone r) (hfirst : r 0 = 1) (hlast : r n = 3)
    {K : ℝ → ℝ} (hK : IntervalIntegrable K volume 1 3)
    (hHK : IntervalIntegrable (fun x => wuImprovementLimit true δ x * K x) volume 1 3)
    (hK0 : ∀ x ∈ Icc (1 : ℝ) 3, 0 ≤ K x) :
    (∑ k ∈ Finset.range n,
      wuImprovementLimit true δ (r (k + 1)) * ∫ x in r k..r (k + 1), K x) ≤
      ∫ x in (1 : ℝ)..3, wuImprovementLimit true δ x * K x := by
  have hsub (k : ℕ) (hk : k < n) :=
    tableFeedback_cell_subset hr hfirst hlast hk
  have hcell (k : ℕ) (hk : k < n) :
      wuImprovementLimit true δ (r (k + 1)) * (∫ x in r k..r (k + 1), K x) ≤
        ∫ x in r k..r (k + 1), wuImprovementLimit true δ x * K x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (hr (Nat.le_succ k))
      ((hK.mono_set (hsub k hk)).const_mul _) (hHK.mono_set (hsub k hk))
    intro x hx
    have hx13 : x ∈ Icc (1 : ℝ) 3 := by
      have hm := hsub k hk
      rw [uIcc_of_le (hr (Nat.le_succ k)),
        uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at hm
      exact hm hx
    have hr13 : r (k + 1) ∈ Icc (1 : ℝ) 3 := by
      have hm := hsub k hk
      rw [uIcc_of_le (hr (Nat.le_succ k)),
        uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at hm
      exact hm ⟨hr (Nat.le_succ k), le_rfl⟩
    exact mul_le_mul_of_nonneg_right
      (wuImprovementLimit_upper_antitone hδ hδhi
        ⟨hx13.1, by linarith [hx13.2]⟩ ⟨hr13.1, by linarith [hr13.2]⟩ hx.2)
      (hK0 x hx13)
  calc
    _ ≤ ∑ k ∈ Finset.range n,
        ∫ x in r k..r (k + 1), wuImprovementLimit true δ x * K x :=
      Finset.sum_le_sum (fun k hk => hcell k (Finset.mem_range.mp hk))
    _ = _ := by
      rw [intervalIntegral.sum_integral_adjacent_intervals
        (fun k hk => hHK.mono_set (hsub k hk)), hfirst, hlast]

theorem tableFeedback_first_partition {δ s t : ℝ} {r : ℕ → ℝ} {n : ℕ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hs : 2 ≤ s) (hs3 : s ≤ 3) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hratio : 2 ≤ t - t / s)
    (hr : Monotone r) (hfirst : r 0 = 1) (hlast : r n = 3) :
    firstFunctionalGainPsi δ s t +
      (∑ k ∈ Finset.range n, wuImprovementLimit true δ (r (k + 1)) *
        ∫ x in r k..r (k + 1), firstFeedbackXi x s t) ≤
      wuImprovementLimit true δ s := by
  have hpart := tableFeedback_partition_lower hδ hδhi hr hfirst hlast
    (firstFeedbackXi_intervalIntegrable hs hs3 ht ht5 hratio)
    (firstFeedbackXi_gain_intervalIntegrable true hδ (by linarith)
      hs hs3 ht ht5 hratio)
    (fun x hx => firstFeedbackXi_nonneg hs hs3 ht ht5 hx)
  have hfeedback := wuImprovementLimit_firstFeedback hδ hδhi hs hs3 ht ht5 hratio
  linarith

end Wu2008DoubleSieve
