import MixedEtaUniform

namespace LowComplement
open Finset Real Wu2008DoubleSieve MixedSixth
open scoped Classical Topology
noncomputable section

def B (N n : ℕ) (δ : ℝ) : ℝ :=
  main N n δ 0 - (MixedEta.highMain N n δ -
    truncatedSixthLowerNormalizedMain N δ 0 (MixedEta.selected N n (highCells δ n)))

def lowMain (N n : ℕ) (δ : ℝ) : ℝ :=
  ∑ k ∈ packing N n (lowCells δ n),
    (wuLowerCoefficient (sourceS δ n k) + wuImprovementLimit false δ (sourceS δ n k)) *
      MixedEta.theta N n k δ

def rest (N n : ℕ) (δ : ℝ) : Finset (ℕ × ℕ) :=
  truncatedSixthLowerPairs N δ \ MixedEta.selected N n (lowCells δ n)

theorem split_raw (N n : ℕ) (δ : ℝ) :
    B N n δ = truncatedSixthLowerNormalizedMain N δ 0 (MixedEta.complement N n δ) +
      lowMain N n δ +
      truncatedSixthLowerNormalizedMain N δ 0 (MixedEta.selected N n (highCells δ n)) := by
  unfold B main HighConsumer.mixedMain
  simp_rw [MixedEta.theta_swap]
  simp only [sub_zero]
  change truncatedSixthLowerNormalizedMain N δ 0 (MixedEta.complement N n δ) +
    lowMain N n δ + MixedEta.highMain N n δ -
    (MixedEta.highMain N n δ - truncatedSixthLowerNormalizedMain N δ 0
      (MixedEta.selected N n (highCells δ n))) = _
  ring

theorem rest_partition {N n : ℕ} {δ : ℝ} (hN : 1 < N) (hδ : 0 ≤ δ) :
    rest N n δ = MixedEta.complement N n δ ∪ MixedEta.selected N n (highCells δ n) := by
  obtain ⟨_,hh,hd⟩ := MixedEta.actual_selected_geometry hN hδ n
  ext p
  simp only [rest,MixedEta.complement,mem_sdiff,mem_union]
  constructor
  · rintro ⟨hp,hl⟩
    by_cases hx : p ∈ MixedEta.selected N n (highCells δ n)
    · exact Or.inr hx
    · exact Or.inl ⟨hp,not_or.mpr ⟨hl,hx⟩⟩
  · rintro (⟨hp,h⟩ | hp)
    · exact ⟨hp,fun hl => h (Or.inl hl)⟩
    · exact ⟨hh hp,fun hl => disjoint_left.mp hd hl hp⟩

theorem B_eq_rest_low {N n : ℕ} {δ : ℝ} (hN : 1 < N) (hδ : 0 ≤ δ) :
    B N n δ = truncatedSixthLowerNormalizedMain N δ 0 (rest N n δ) + lowMain N n δ := by
  have hd : Disjoint (MixedEta.complement N n δ) (MixedEta.selected N n (highCells δ n)) := by
    apply disjoint_left.mpr
    intro p hp hh
    exact (mem_sdiff.mp hp).2 (mem_union_right _ hh)
  rw [split_raw,rest_partition hN hδ]
  unfold truncatedSixthLowerNormalizedMain
  rw [sum_union hd]
  ring

/-- Full classical mother plus the actual low replacement debit, not a count sum. -/
theorem B_eq_classical_low_gain {N n : ℕ} {δ : ℝ} (hN : 1 < N) (hδ : 0 ≤ δ) :
    B N n δ = truncatedSixthLowerNormalizedMain N δ 0 (truncatedSixthLowerPairs N δ) +
      (lowMain N n δ -
        truncatedSixthLowerNormalizedMain N δ 0 (MixedEta.selected N n (lowCells δ n))) := by
  have hl := (MixedEta.actual_selected_geometry hN hδ n).1
  have he : truncatedSixthLowerNormalizedMain N δ 0 (rest N n δ) +
      truncatedSixthLowerNormalizedMain N δ 0 (MixedEta.selected N n (lowCells δ n)) =
      truncatedSixthLowerNormalizedMain N δ 0 (truncatedSixthLowerPairs N δ) := by
    unfold truncatedSixthLowerNormalizedMain rest
    rw [← sum_union sdiff_disjoint,sdiff_union_of_subset hl]
  rw [B_eq_rest_low hN hδ]
  linarith only [he]

end
end LowComplement
