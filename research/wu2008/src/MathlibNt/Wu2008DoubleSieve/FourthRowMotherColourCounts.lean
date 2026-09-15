import MathlibNt.Wu2008DoubleSieve.FourthRowMotherLists

/-! # Exact finite band-word counts, with no cardinality hypothesis -/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

def fourthRowMotherBandCount (x y z : ℕ) : List ℕ → ℕ
  | [] => 1
  | [j] => if j = 0 then x else if j = 1 then y else if j = 2 then z else 0
  | j :: h :: cs =>
      if 0 < x then
        if j = 0 then fourthRowMotherBandCount (x - 1) y z (h :: cs) else 0
      else if 0 < y then
        if j = 1 then fourthRowMotherBandCount x (y - 1) z (h :: cs) else 0
      else if 0 < z then
        if j = 2 then fourthRowMotherBandCount x y (z - 1) (h :: cs) else 0
      else 0

theorem fourthRowMother_coloured_empty (cs : List ℕ) :
    (fourthRowMotherColoured ∅ (fun _ => 0) cs).card =
      fourthRowMotherBandCount 0 0 0 cs := by
  cases cs with
  | nil =>
      simp only [fourthRowMotherColoured, List.length_nil, fourthRowMother_prefixes_zero,
        filter_singleton, List.map_nil, ite_true, card_singleton, fourthRowMotherBandCount]
  | cons j cs =>
      cases cs with
      | nil =>
          simp [fourthRowMotherColoured, fourthRowMotherPrefixes, fourthRowMotherBandCount]
      | cons h cs =>
          simp [fourthRowMotherColoured, fourthRowMother_prefixes_empty, fourthRowMotherBandCount]

theorem fourthRowMother_colour_count_sum (s : Finset ℕ) (χ : ℕ → ℕ)
    (hcap : ∀ p ∈ s, χ p ≤ 2) :
    fourthRowMotherColourCount s χ 0 + fourthRowMotherColourCount s χ 1 +
      fourthRowMotherColourCount s χ 2 = s.card := by
  have he : (s.filter fun p => χ p = 0) ∪ (s.filter fun p => χ p = 1) ∪
      (s.filter fun p => χ p = 2) = s := by
    ext p
    simp only [mem_union, mem_filter]
    constructor
    · tauto
    · intro hp
      have hc := hcap p hp
      rcases (show χ p = 0 ∨ χ p = 1 ∨ χ p = 2 by omega) with h | h | h
      · exact Or.inl (Or.inl ⟨hp, h⟩)
      · exact Or.inl (Or.inr ⟨hp, h⟩)
      · exact Or.inr ⟨hp, h⟩
  have hd01 : Disjoint (s.filter fun p => χ p = 0) (s.filter fun p => χ p = 1) := by
    simp only [disjoint_left, mem_filter]
    omega
  have hd2 : Disjoint ((s.filter fun p => χ p = 0) ∪ (s.filter fun p => χ p = 1))
      (s.filter fun p => χ p = 2) := by
    simp only [disjoint_left, mem_union, mem_filter]
    omega
  simpa only [fourthRowMotherColourCount, card_union_of_disjoint hd2,
    card_union_of_disjoint hd01] using congrArg card he

theorem fourthRowMother_coloured_card (s : Finset ℕ) (χ : ℕ → ℕ)
    (hχ : Monotone χ) (hcap : ∀ p ∈ s, χ p ≤ 2) (cs : List ℕ) :
    (fourthRowMotherColoured s χ cs).card =
      fourthRowMotherBandCount (fourthRowMotherColourCount s χ 0)
        (fourthRowMotherColourCount s χ 1) (fourthRowMotherColourCount s χ 2) cs := by
  induction cs using List.twoStepInduction generalizing s with
  | nil =>
      simp only [fourthRowMotherColoured, List.length_nil, fourthRowMother_prefixes_zero,
        filter_singleton, List.map_nil, ite_true, card_singleton, fourthRowMotherBandCount]
  | singleton j =>
      rw [fourthRowMother_coloured_single, fourthRowMotherBandCount]
      split_ifs with h0 h1 h2
      · rw [h0]
      · rw [h1]
      · rw [h2]
      · unfold fourthRowMotherColourCount
        apply card_eq_zero.mpr
        apply eq_empty_iff_forall_notMem.mpr
        intro p hp
        obtain ⟨hp, he⟩ := mem_filter.mp hp
        have hh := hcap p hp
        omega
  | cons_cons j h cs _ ih =>
      by_cases hs : s.Nonempty
      · have ha := s.min'_mem hs
        have he := fourthRowMother_min_colour hs hχ hcap
        have hsum := fourthRowMother_colour_count_sum s χ hcap
        have hspos := card_pos.mpr hs
        rw [fourthRowMother_coloured_cons s hs χ j h cs,
          ih h (s.erase (s.min' hs)) (fun p hp => hcap p (mem_erase.mp hp).2)]
        simp only [fourthRowMother_colour_erase ha]
        rw [fourthRowMotherBandCount]
        by_cases hx : 0 < fourthRowMotherColourCount s χ 0
        · simp only [if_pos hx] at he ⊢
          rw [he]
          by_cases hj : j = 0 <;> simp [hj, eq_comm]
        · simp only [if_neg hx] at he ⊢
          by_cases hy : 0 < fourthRowMotherColourCount s χ 1
          · simp only [if_pos hy] at he ⊢
            rw [he]
            by_cases hj : j = 1 <;> simp [hj, eq_comm]
          · simp only [if_neg hy] at he ⊢
            have hz : 0 < fourthRowMotherColourCount s χ 2 := by omega
            rw [if_pos hz, he]
            by_cases hj : j = 2 <;> simp [hj, eq_comm]
      · have he := not_nonempty_iff_eq_empty.mp hs
        subst s
        simp [fourthRowMotherColoured, fourthRowMother_prefixes_empty,
          fourthRowMotherColourCount, fourthRowMotherBandCount]

end Wu2008DoubleSieve
