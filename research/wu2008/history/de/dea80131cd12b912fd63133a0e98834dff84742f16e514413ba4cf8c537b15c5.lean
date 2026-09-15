import MathlibNt.Wu2004MeanValue.OriginalTriplesBlock

/-!
# Finite assembly for arbitrary half-open scale covers

The only covering premise concerns real numbers and scale intervals. No
exception certificate, injectivity premise, or conclusion-shaped count bound
is assumed. In particular the interface is applicable to moving dyadic sums.
-/

namespace Wu2004MeanValue

open Classical Finset
open scoped BigOperators
noncomputable section

theorem originalTripleCount_le_low_add_blocks {ι : Type*}
    (S : Finset ι) (H : ι → ℝ) (N : ℕ) (a η R : ℝ)
    (hcover : ∀ x : ℝ, R < x → x ≤ η * N →
      ∃ i ∈ S, H i < x ∧ x ≤ 2 * H i) :
    originalTripleCount N a η ≤ (originalTriplesLow N a η R).card +
      ∑ i ∈ S, originalTripleBlockCount (H i) N a η := by
  have hsub : originalTriples N a η ⊆ originalTriplesLow N a η R ∪
      S.biUnion (fun i => originalTriplesBlock (H i) N a η) := by
    intro t ht
    by_cases hlow : (t.2.1 : ℝ) * t.2.2 ≤ R
    · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨ht, hlow⟩))
    · obtain ⟨i, hi, hblock⟩ := hcover ((t.2.1 : ℝ) * t.2.2)
        (lt_of_not_ge hlow) (mem_originalTriples.mp ht).2.2.2.2.2.2
      exact mem_union.mpr (Or.inr (mem_biUnion.mpr
        ⟨i, hi, mem_filter.mpr ⟨ht, hblock⟩⟩))
  have hcard := (card_le_card hsub).trans (card_union_le _ _)
  exact hcard.trans (Nat.add_le_add_left (card_biUnion_le) _)

/-- A fully paid finite bound, ready for a uniform dyadic sieve estimate. -/
theorem originalTripleCount_le_cover {ι : Type*}
    (S : Finset ι) (H z : ι → ℝ) (N : ℕ) (a η R : ℝ)
    (ha : 1 < a) (hη : η < 1 / 2) (hR : 0 ≤ R)
    (hH : ∀ i ∈ S, 0 < H i)
    (hz : ∀ i ∈ S, z i ≤ (1 - η) * N)
    (hcover : ∀ x : ℝ, R < x → x ≤ η * N →
      ∃ i ∈ S, H i < x ∧ x ≤ 2 * H i) :
    originalTripleCount N a η ≤ (⌊Real.sqrt R⌋₊ + 1) * (⌊R⌋₊ + 1) +
      ∑ i ∈ S, (blockSiftedCount (H i) N a η (z i) +
        3 * (⌊Real.sqrt (2 * H i)⌋₊ + 1)) := by
  apply (originalTripleCount_le_low_add_blocks S H N a η R hcover).trans
  apply Nat.add_le_add (originalTriplesLow_card_le hR)
  exact sum_le_sum (fun i hi => originalTripleBlockCount_le (hH i hi) ha hη (hz i hi))

/-- Real-valued form with the boundary sum separate from the sifted sum. -/
theorem originalTripleCount_le_cover_real {ι : Type*}
    (S : Finset ι) (H z : ι → ℝ) (N : ℕ) (a η R : ℝ)
    (ha : 1 < a) (hη : η < 1 / 2) (hR : 0 ≤ R)
    (hH : ∀ i ∈ S, 0 < H i)
    (hz : ∀ i ∈ S, z i ≤ (1 - η) * N)
    (hcover : ∀ x : ℝ, R < x → x ≤ η * N →
      ∃ i ∈ S, H i < x ∧ x ≤ 2 * H i) :
    (originalTripleCount N a η : ℝ) ≤
      (Real.sqrt R + 1) * (R + 1) +
      (∑ i ∈ S, (blockSiftedCount (H i) N a η (z i) : ℝ)) +
      3 * ∑ i ∈ S, (Real.sqrt (2 * H i) + 1) := by
  have hnat := originalTripleCount_le_cover S H z N a η R ha hη hR hH hz hcover
  have hcast : (originalTripleCount N a η : ℝ) ≤
      ((⌊Real.sqrt R⌋₊ : ℝ) + 1) * ((⌊R⌋₊ : ℝ) + 1) +
      ∑ i ∈ S, ((blockSiftedCount (H i) N a η (z i) : ℝ) +
        3 * ((⌊Real.sqrt (2 * H i)⌋₊ : ℝ) + 1)) := by exact_mod_cast hnat
  have hlow : ((⌊Real.sqrt R⌋₊ : ℝ) + 1) * ((⌊R⌋₊ : ℝ) + 1) ≤
      (Real.sqrt R + 1) * (R + 1) :=
    mul_le_mul (add_le_add (Nat.floor_le (Real.sqrt_nonneg R)) le_rfl)
      (add_le_add (Nat.floor_le hR) le_rfl) (by positivity) (by positivity)
  have hsum : (∑ i ∈ S, ((blockSiftedCount (H i) N a η (z i) : ℝ) +
        3 * ((⌊Real.sqrt (2 * H i)⌋₊ : ℝ) + 1))) ≤
      ∑ i ∈ S, ((blockSiftedCount (H i) N a η (z i) : ℝ) +
        3 * (Real.sqrt (2 * H i) + 1)) := by
    apply sum_le_sum
    intro i _
    have hf := Nat.floor_le (Real.sqrt_nonneg (2 * H i))
    linarith
  calc
    (originalTripleCount N a η : ℝ) ≤ _ := hcast.trans (add_le_add hlow hsum)
    _ = _ := by rw [sum_add_distrib, ← mul_sum]; ring

end
end Wu2004MeanValue
