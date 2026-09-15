import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherScalar

/-! # Exact four-colour counts of arbitrary-length least-factor prefixes -/
namespace Wu2008DoubleSieve
open Finset
open scoped Classical

def secondFunctionalMotherBandCount (x y z w : ℕ) : List ℕ → ℕ
  | [] => 1
  | [j] => if j = 0 then x else if j = 1 then y else if j = 2 then z
      else if j = 3 then w else 0
  | j :: h :: cs =>
      if 0 < x then
        if j = 0 then secondFunctionalMotherBandCount (x-1) y z w (h::cs) else 0
      else if 0 < y then
        if j = 1 then secondFunctionalMotherBandCount x (y-1) z w (h::cs) else 0
      else if 0 < z then
        if j = 2 then secondFunctionalMotherBandCount x y (z-1) w (h::cs) else 0
      else if 0 < w then
        if j = 3 then secondFunctionalMotherBandCount x y z (w-1) (h::cs) else 0
      else 0

theorem secondFunctionalMother_min_colour {s : Finset ℕ} (hs : s.Nonempty)
    {χ : ℕ → ℕ} (hχ : Monotone χ) (hcap : ∀ p ∈ s, χ p ≤ 3) :
    χ (s.min' hs) =
      if 0 < fourthRowMotherColourCount s χ 0 then 0
      else if 0 < fourthRowMotherColourCount s χ 1 then 1
      else if 0 < fourthRowMotherColourCount s χ 2 then 2 else 3 := by
  have ha := s.min'_mem hs
  have hle := hcap _ ha
  have hc (j : ℕ) (hj : 0 < fourthRowMotherColourCount s χ j) :
      χ (s.min' hs) ≤ j := by
    obtain ⟨p, hp⟩ := card_pos.mp hj
    obtain ⟨hp, he⟩ := mem_filter.mp hp
    exact he ▸ hχ (s.min'_le p hp)
  have hpos : 0 < fourthRowMotherColourCount s χ (χ (s.min' hs)) :=
    card_pos.mpr ⟨s.min' hs, mem_filter.mpr ⟨ha, rfl⟩⟩
  split_ifs with h0 h1 h2
  · exact Nat.eq_zero_of_le_zero (hc 0 h0)
  · have hh := hc 1 h1
    have hn : χ (s.min' hs) ≠ 0 := fun he => h0 (he ▸ hpos)
    omega
  · have hh := hc 2 h2
    have hn0 : χ (s.min' hs) ≠ 0 := fun he => h0 (he ▸ hpos)
    have hn1 : χ (s.min' hs) ≠ 1 := fun he => h1 (he ▸ hpos)
    omega
  · have hn0 : χ (s.min' hs) ≠ 0 := fun he => h0 (he ▸ hpos)
    have hn1 : χ (s.min' hs) ≠ 1 := fun he => h1 (he ▸ hpos)
    have hn2 : χ (s.min' hs) ≠ 2 := fun he => h2 (he ▸ hpos)
    omega

theorem secondFunctionalMother_colour_count_sum (s : Finset ℕ) (χ : ℕ → ℕ)
    (hcap : ∀ p ∈ s, χ p ≤ 3) :
    fourthRowMotherColourCount s χ 0 + fourthRowMotherColourCount s χ 1 +
      fourthRowMotherColourCount s χ 2 + fourthRowMotherColourCount s χ 3 = s.card := by
  have he : (s.filter fun p => χ p = 0) ∪ (s.filter fun p => χ p = 1) ∪
      (s.filter fun p => χ p = 2) ∪ (s.filter fun p => χ p = 3) = s := by
    ext p
    simp only [mem_union, mem_filter]
    constructor
    · tauto
    · intro hp
      have hc := hcap p hp
      have hh : χ p = 0 ∨ χ p = 1 ∨ χ p = 2 ∨ χ p = 3 := by omega
      tauto
  have hd01 : Disjoint (s.filter fun p => χ p = 0) (s.filter fun p => χ p = 1) := by
    simp only [disjoint_left, mem_filter]
    omega
  have hd2 : Disjoint ((s.filter fun p => χ p = 0) ∪ (s.filter fun p => χ p = 1))
      (s.filter fun p => χ p = 2) := by
    simp only [disjoint_left, mem_union, mem_filter]
    omega
  have hd3 : Disjoint ((s.filter fun p => χ p = 0) ∪ (s.filter fun p => χ p = 1) ∪
      (s.filter fun p => χ p = 2)) (s.filter fun p => χ p = 3) := by
    simp only [disjoint_left, mem_union, mem_filter]
    omega
  simpa only [fourthRowMotherColourCount, card_union_of_disjoint hd3,
    card_union_of_disjoint hd2, card_union_of_disjoint hd01] using congrArg card he

theorem secondFunctionalMother_coloured_card (s : Finset ℕ) (χ : ℕ → ℕ)
    (hχ : Monotone χ) (hcap : ∀ p ∈ s, χ p ≤ 3) (cs : List ℕ) :
    (fourthRowMotherColoured s χ cs).card =
      secondFunctionalMotherBandCount (fourthRowMotherColourCount s χ 0)
        (fourthRowMotherColourCount s χ 1) (fourthRowMotherColourCount s χ 2)
        (fourthRowMotherColourCount s χ 3) cs := by
  induction cs using List.twoStepInduction generalizing s with
  | nil =>
      simp only [fourthRowMotherColoured, List.length_nil, fourthRowMother_prefixes_zero,
        filter_singleton, List.map_nil, ite_true, card_singleton, secondFunctionalMotherBandCount]
  | singleton j =>
      rw [fourthRowMother_coloured_single, secondFunctionalMotherBandCount]
      split_ifs with h0 h1 h2 h3
      · rw [h0]
      · rw [h1]
      · rw [h2]
      · rw [h3]
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
        have he := secondFunctionalMother_min_colour hs hχ hcap
        have hpos : 0 < fourthRowMotherColourCount s χ (χ (s.min' hs)) :=
          card_pos.mpr ⟨s.min' hs, mem_filter.mpr ⟨ha, rfl⟩⟩
        rw [fourthRowMother_coloured_cons s hs χ j h cs,
          ih h (s.erase (s.min' hs)) (fun p hp => hcap p (mem_erase.mp hp).2)]
        simp only [fourthRowMother_colour_erase ha]
        rw [secondFunctionalMotherBandCount]
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
            by_cases hz : 0 < fourthRowMotherColourCount s χ 2
            · simp only [if_pos hz] at he ⊢
              rw [he]
              by_cases hj : j = 2 <;> simp [hj, eq_comm]
            · simp only [if_neg hz] at he ⊢
              rw [he] at hpos
              rw [if_pos hpos, he]
              by_cases hj : j = 3 <;> simp [hj, eq_comm]
      · have he := not_nonempty_iff_eq_empty.mp hs
        subst s
        simp [fourthRowMotherColoured, fourthRowMother_prefixes_empty,
          fourthRowMotherColourCount, secondFunctionalMotherBandCount]

end Wu2008DoubleSieve
