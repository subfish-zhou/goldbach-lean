import MathlibNt.SieveTheory.LiLiuGoldbachG10BuchstabBridge

open scoped BigOperators
open Finset
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Raising the first-prime lower cutoff gives precisely the closed high subfamily. -/
theorem goldbachC10Pairs_filter_first_ge (N : ℕ) (b c t : ℝ) (hbt : b ≤ t) :
    (goldbachC10Pairs N b c).filter (fun rs => t ≤ (rs.1 : ℝ)) =
      goldbachC10Pairs N t c := by
  classical
  ext rs
  simp only [mem_filter, mem_goldbachC10Pairs_iff]
  constructor
  · rintro ⟨⟨hr, hs, hcop, _hb, hrc, hcs, hsquare⟩, ht⟩
    exact ⟨hr, hs, hcop, ht, hrc, hcs, hsquare⟩
  · rintro ⟨hr, hs, hcop, ht, hrc, hcs, hsquare⟩
    exact ⟨⟨hr, hs, hcop, hbt.trans ht, hrc, hcs, hsquare⟩, ht⟩

/-- Exact labelled partition, valid for any additive weights; no inequality is subtracted. -/
theorem goldbachC10Pairs_sum_split_first {α : Type*} [AddCommMonoid α]
    (N : ℕ) (b c t : ℝ) (hbt : b ≤ t) (f : ℕ × ℕ → α) :
    (∑ rs ∈ goldbachC10Pairs N b c, f rs) =
      (∑ rs ∈ (goldbachC10Pairs N b c).filter (fun rs => (rs.1 : ℝ) < t), f rs) +
      ∑ rs ∈ goldbachC10Pairs N t c, f rs := by
  classical
  have h := sum_filter_add_sum_filter_not (goldbachC10Pairs N b c)
    (fun rs => (rs.1 : ℝ) < t) f
  simp only [not_lt] at h
  rw [goldbachC10Pairs_filter_first_ge N b c t hbt] at h
  exact h.symm

/-- Strict low first-prime part of the original H-sum, with all other labels retained. -/
noncomputable def goldbachS5ClosedBelow (A : Finset ℕ) (N : ℕ) (b c t : ℝ) : ℤ := by
  classical
  exact ∑ rs ∈ (goldbachC10Pairs N b c).filter (fun rs => (rs.1 : ℝ) < t),
    literalH A (N * rs.1) (rs.1 * rs.2) rs.2

theorem goldbachS5Closed_eq_below_add_raisedCutoff
    (A : Finset ℕ) (N : ℕ) (b c t : ℝ) (hbt : b ≤ t) :
    goldbachS5Closed A N b c =
      goldbachS5ClosedBelow A N b c t + goldbachS5Closed A N t c := by
  rw [goldbachS5Closed_eq_sum_goldbachC10Pairs,
    goldbachS5Closed_eq_sum_goldbachC10Pairs]
  exact goldbachC10Pairs_sum_split_first N b c t hbt _

/-- The source-paper boundary goes to the high term; the original epsilon carrier is unchanged.
Neither a high-only analytic upper bound nor a low improved estimate is claimed here. -/
theorem goldbachS5Closed_actual_split_first (N : ℕ) (hN : 2 ≤ N) (ε : ℝ) :
    goldbachS5Closed (goldbachDifferenceCarrier N ε) N
        ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(1 / 3 : ℝ)) =
      goldbachS5ClosedBelow (goldbachDifferenceCarrier N ε) N
        ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(1 / 3 : ℝ)) ((N : ℝ)^(1 / 10 : ℝ)) +
      goldbachS5Closed (goldbachDifferenceCarrier N ε) N
        ((N : ℝ)^(1 / 10 : ℝ)) ((N : ℝ)^(1 / 3 : ℝ)) := by
  apply goldbachS5Closed_eq_below_add_raisedCutoff
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig