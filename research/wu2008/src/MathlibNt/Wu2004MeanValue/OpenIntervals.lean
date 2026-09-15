import MathlibNt.Wu2004MeanValue.RealEndpoints

/-!
# Open product intervals and the upper-endpoint atom

The frozen manuscript's `B_H` has two open endpoints. Wu's prime count on
printed p. 220 instead has a closed upper endpoint. Subtracting two Wu counts
therefore requires removal of one possible upper-endpoint prime, not an
unqualified equality with the open interval.
-/

namespace Wu2004MeanValue

open Finset
open scoped BigOperators
noncomputable section

def openScaledPrimeSet (lo hi : ℝ) (d b m : ℕ) : Finset ℕ :=
  (scaledPrimeSet hi d b m).filter
    (fun p => lo < (m : ℝ) * p ∧ (m : ℝ) * p < hi)

def upperEndpointSet (hi : ℝ) (d b m : ℕ) : Finset ℕ :=
  (scaledPrimeSet hi d b m).filter (fun p => (m : ℝ) * p = hi)

theorem scaledPrimeSet_partition (lo hi : ℝ) (d b m : ℕ)
    (hlo : 0 ≤ lo) (hlt : lo < hi) (hm : 0 < m) :
    scaledPrimeSet hi d b m =
      (scaledPrimeSet lo d b m ∪ openScaledPrimeSet lo hi d b m) ∪
        upperEndpointSet hi d b m := by
  ext p
  simp only [mem_union, openScaledPrimeSet, upperEndpointSet, mem_filter,
    mem_scaledPrimeSet hlo hm, mem_scaledPrimeSet (hlo.trans hlt.le) hm]
  constructor
  · rintro ⟨hp, hphi, hcong⟩
    by_cases hplo : (m : ℝ) * p ≤ lo
    · exact Or.inl (Or.inl ⟨hp, hplo, hcong⟩)
    · by_cases hpeq : (m : ℝ) * p = hi
      · exact Or.inr ⟨⟨hp, hphi, hcong⟩, hpeq⟩
      · exact Or.inl (Or.inr ⟨⟨hp, hphi, hcong⟩, lt_of_not_ge hplo,
          lt_of_le_of_ne hphi hpeq⟩)
  · rintro ((h | h) | h)
    · exact ⟨h.1, h.2.1.trans hlt.le, h.2.2⟩
    · exact h.1
    · exact h.1

theorem scaledPrimeCount_partition (lo hi : ℝ) (d b m : ℕ)
    (hlo : 0 ≤ lo) (hlt : lo < hi) (hm : 0 < m) :
    scaledPrimeCount hi d b m =
      scaledPrimeCount lo d b m + (openScaledPrimeSet lo hi d b m).card +
        (upperEndpointSet hi d b m).card := by
  have hdisj : Disjoint (scaledPrimeSet lo d b m) (openScaledPrimeSet lo hi d b m) := by
    apply Finset.disjoint_left.mpr
    intro p hp hpo
    have hp' := (mem_scaledPrimeSet hlo hm).mp hp
    have hpo' := (mem_filter.mp hpo).2.1
    linarith
  have hdisj' : Disjoint (scaledPrimeSet lo d b m ∪ openScaledPrimeSet lo hi d b m)
      (upperEndpointSet hi d b m) := by
    apply Finset.disjoint_left.mpr
    intro p hp hpe
    have hpeq := (mem_filter.mp hpe).2
    rcases mem_union.mp hp with hp | hp
    · have hple := ((mem_scaledPrimeSet hlo hm).mp hp).2.1
      linarith
    · have hplt := (mem_filter.mp hp).2.2
      linarith
  unfold scaledPrimeCount
  rw [scaledPrimeSet_partition lo hi d b m hlo hlt hm,
    card_union_of_disjoint hdisj', card_union_of_disjoint hdisj]

theorem upperEndpointSet_card_le_one (hi : ℝ) (d b m : ℕ) (hm : 0 < m) :
    (upperEndpointSet hi d b m).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  have hp' := (mem_filter.mp hp).2
  have hq' := (mem_filter.mp hq).2
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have heq : (p : ℝ) = q := mul_left_cancel₀ hmR (hp'.trans hq'.symm)
  exact_mod_cast heq

/-- Exact open-interval error, with no endpoint convention hidden in li. -/
theorem openInterval_error_identity (lo hi : ℝ) (d b m : ℕ)
    (hlo : 0 ≤ lo) (hlt : lo < hi) (hm : 0 < m) :
    ((openScaledPrimeSet lo hi d b m).card : ℝ) -
        (wuLi (hi / m) - wuLi (lo / m)) / Nat.totient d =
      ebar hi d b m - ebar lo d b m -
        (upperEndpointSet hi d b m).card := by
  have hcount := scaledPrimeCount_partition lo hi d b m hlo hlt hm
  have hreal :
      (scaledPrimeCount hi d b m : ℝ) =
        (scaledPrimeCount lo d b m : ℝ) + (openScaledPrimeSet lo hi d b m).card +
          (upperEndpointSet hi d b m).card := by exact_mod_cast hcount
  unfold ebar
  rw [hreal]
  ring

/-- One possible upper-endpoint atom per positive coefficient index. -/
theorem abs_sum_upperEndpoint_le (S : Finset ℕ) (hi f : ℕ → ℝ)
    (d b : ℕ) (F : ℝ) (hF : 0 ≤ F)
    (hpos : ∀ m ∈ S, 0 < m) (hf : ∀ m ∈ S, |f m| ≤ F) :
    |∑ m ∈ S, f m * (upperEndpointSet (hi m) d b m).card| ≤ F * S.card := by
  calc
    _ ≤ ∑ m ∈ S, |f m * (upperEndpointSet (hi m) d b m).card| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ S, F := by
      apply sum_le_sum
      intro m hm
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤
        (upperEndpointSet (hi m) d b m).card)]
      have hb : ((upperEndpointSet (hi m) d b m).card : ℝ) ≤ 1 := by
        exact_mod_cast upperEndpointSet_card_le_one (hi m) d b m (hpos m hm)
      calc
        _ ≤ F * 1 := mul_le_mul (hf m hm) hb (by positivity) hF
        _ = _ := mul_one _
    _ = _ := by simp [mul_comm]

end
end Wu2004MeanValue