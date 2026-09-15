import MathlibNt.Wu2004MeanValue.ActualOpenIntervals

/-! The manuscript tail is closed at both product endpoints. Its discrepancy
is the difference of two Wu prefixes PLUS the lower-endpoint atom. -/

namespace Wu2004MeanValue

open Classical Finset
open scoped BigOperators
noncomputable section

def closedScaledPrimeSet (lo hi : ℝ) (d b m : ℕ) : Finset ℕ :=
  (scaledPrimeSet hi d b m).filter (fun p => lo ≤ (m : ℝ) * p)

theorem mem_closedScaledPrimeSet {lo hi : ℝ} {d b m p : ℕ}
    (hhi : 0 ≤ hi) (hm : 0 < m) :
    p ∈ closedScaledPrimeSet lo hi d b m ↔
      p.Prime ∧ lo ≤ (m : ℝ) * p ∧ (m : ℝ) * p ≤ hi ∧ m * p ≡ b [MOD d] := by
  simp only [closedScaledPrimeSet, mem_filter, mem_scaledPrimeSet hhi hm]
  tauto

theorem closedScaledPrimeSet_partition (lo hi : ℝ) (d b m : ℕ)
    (hlo : 0 ≤ lo) (hlt : lo < hi) (hm : 0 < m) :
    closedScaledPrimeSet lo hi d b m =
      (openScaledPrimeSet lo hi d b m ∪ upperEndpointSet hi d b m) ∪
        upperEndpointSet lo d b m := by
  ext p
  simp only [mem_closedScaledPrimeSet (hlo.trans hlt.le) hm, mem_union,
    openScaledPrimeSet, upperEndpointSet, mem_filter,
    mem_scaledPrimeSet hlo hm, mem_scaledPrimeSet (hlo.trans hlt.le) hm]
  constructor
  · rintro ⟨hp, hlow, hupp, hcong⟩
    rcases hlow.eq_or_lt with heq | hlow
    · exact Or.inr ⟨⟨hp, heq.ge, hcong⟩, heq.symm⟩
    · rcases hupp.eq_or_lt with heq | hupp
      · exact Or.inl (Or.inr ⟨⟨hp, heq.le, hcong⟩, heq⟩)
      · exact Or.inl (Or.inl ⟨⟨hp, hupp.le, hcong⟩, hlow, hupp⟩)
  · rintro ((h | h) | h)
    · exact ⟨h.1.1, h.2.1.le, h.1.2.1, h.1.2.2⟩
    · exact ⟨h.1.1, by linarith [h.2], h.1.2.1, h.1.2.2⟩
    · exact ⟨h.1.1, h.2.ge, by linarith [h.2], h.1.2.2⟩

theorem closedScaledPrimeSet_card (lo hi : ℝ) (d b m : ℕ)
    (hlo : 0 ≤ lo) (hlt : lo < hi) (hm : 0 < m) :
    (closedScaledPrimeSet lo hi d b m).card =
      (openScaledPrimeSet lo hi d b m).card +
        (upperEndpointSet hi d b m).card + (upperEndpointSet lo d b m).card := by
  have hdisj : Disjoint (openScaledPrimeSet lo hi d b m) (upperEndpointSet hi d b m) := by
    apply disjoint_left.mpr
    intro p hp hq
    have hlt' := (mem_filter.mp hp).2.2
    have heq := (mem_filter.mp hq).2
    linarith
  have hdisj' : Disjoint
      (openScaledPrimeSet lo hi d b m ∪ upperEndpointSet hi d b m)
      (upperEndpointSet lo d b m) := by
    apply disjoint_left.mpr
    intro p hp hq
    have heq := (mem_filter.mp hq).2
    rcases mem_union.mp hp with hp | hp
    · have hlt' := (mem_filter.mp hp).2.1
      linarith
    · have heq' := (mem_filter.mp hp).2
      linarith
  rw [closedScaledPrimeSet_partition lo hi d b m hlo hlt hm,
    card_union_of_disjoint hdisj', card_union_of_disjoint hdisj]

theorem closedInterval_error_identity (lo hi : ℝ) (d b m : ℕ)
    (hlo : 0 ≤ lo) (hlt : lo < hi) (hm : 0 < m) :
    ((closedScaledPrimeSet lo hi d b m).card : ℝ) -
        (wuLi (hi / m) - wuLi (lo / m)) / d.totient =
      ebar hi d b m - ebar lo d b m + (upperEndpointSet lo d b m).card := by
  rw [closedScaledPrimeSet_card lo hi d b m hlo hlt hm, Nat.cast_add, Nat.cast_add]
  have h := openInterval_error_identity lo hi d b m hlo hlt hm
  linarith

def actualClosedErrorSum (S : Finset ℕ) (f lo hi : ℕ → ℝ) (d b : ℕ) : ℝ :=
  ∑ m ∈ S, if m.Coprime d then f m *
    (((closedScaledPrimeSet (lo m) (hi m) d b m).card : ℝ) -
      (wuLi (hi m / m) - wuLi (lo m / m)) / d.totient) else 0

theorem actualClosedErrorSum_eq (S : Finset ℕ) (f lo hi : ℕ → ℝ) (d b : ℕ)
    (hS : ∀ m ∈ S, 0 < m) (hlo : ∀ m ∈ S, 0 ≤ lo m)
    (hlt : ∀ m ∈ S, lo m < hi m) :
    actualClosedErrorSum S f lo hi d b =
      actualAPSum S f (fun m => hi m / m) d b -
        actualAPSum S f (fun m => lo m / m) d b + actualEndpointSum S f lo d b := by
  simp only [actualClosedErrorSum, actualAPSum, actualEndpointSum, sum_filter,
    ← sum_add_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro m hm
  by_cases hc : m.Coprime d
  · simp only [if_pos hc]
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (hS m hm).ne'
    have hmul (t : ℝ) : (m : ℝ) * (t / m) = t := by field_simp
    rw [hmul, hmul, closedInterval_error_identity (lo m) (hi m) d b m
      (hlo m hm) (hlt m hm) (hS m hm)]
    ring
  · simp only [if_neg hc, sub_self, add_zero]

theorem weighted_actualClosedErrorSum_le (S : Finset ℕ) (f lo hi : ℕ → ℝ)
    (Q : ℕ) (b : ℕ → ℕ) (hS : ∀ m ∈ S, 0 < m)
    (hlo : ∀ m ∈ S, 0 ≤ lo m) (hlt : ∀ m ∈ S, lo m < hi m) :
    (∑ d ∈ Icc 1 Q, wuModulusWeight d * |actualClosedErrorSum S f lo hi d (b d)|) ≤
      (∑ d ∈ Icc 1 Q, wuModulusWeight d *
        |actualAPSum S f (fun m => hi m / m) d (b d)|) +
      (∑ d ∈ Icc 1 Q, wuModulusWeight d *
        |actualAPSum S f (fun m => lo m / m) d (b d)|) +
      ∑ d ∈ Icc 1 Q, wuModulusWeight d * |actualEndpointSum S f lo d (b d)| := by
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_le_sum
  intro d _
  rw [actualClosedErrorSum_eq S f lo hi d (b d) hS hlo hlt, ← mul_add, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ (wuModulusWeight_nonneg d)
  exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)

end
end Wu2004MeanValue
