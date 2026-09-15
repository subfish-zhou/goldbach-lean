import MathlibNt.Wu2008DoubleSieve.FiniteWeights

/-!
# Least-distinct-factor labels for the fourth-row mother weight

The first r-1 entries are forced minima; the last entry ranges over the
remaining tail. Values are distinct, but the integer they divide need
not be squarefree.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

noncomputable def fourthRowMotherPrefixes (s : Finset ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | 1 => s.image fun p => [p]
  | r + 2 => if hs : s.Nonempty then
      (fourthRowMotherPrefixes (s.erase (s.min' hs)) (r + 1)).image
        (List.cons (s.min' hs))
    else ∅

theorem fourthRowMother_prefixes_zero (s : Finset ℕ) :
    fourthRowMotherPrefixes s 0 = {[]} := rfl

theorem fourthRowMother_prefixes_one (s : Finset ℕ) :
    fourthRowMotherPrefixes s 1 = s.image fun p => [p] := rfl

theorem fourthRowMother_prefixes_empty (r : ℕ) :
    fourthRowMotherPrefixes ∅ (r + 1) = ∅ := by
  cases r <;> simp [fourthRowMotherPrefixes]

theorem fourthRowMother_prefixes_cons (s : Finset ℕ) (hs : s.Nonempty) (r : ℕ) :
    fourthRowMotherPrefixes s (r + 2) =
      (fourthRowMotherPrefixes (s.erase (s.min' hs)) (r + 1)).image
        (List.cons (s.min' hs)) := by
  simp only [fourthRowMotherPrefixes, dif_pos hs]

theorem fourthRowMother_prefix_length {s : Finset ℕ} {r : ℕ} {l : List ℕ}
    (hl : l ∈ fourthRowMotherPrefixes s r) : l.length = r := by
  induction r using Nat.twoStepInduction generalizing s l with
  | zero =>
      have he := mem_singleton.mp hl
      subst l
      rfl
  | one =>
      obtain ⟨p, _, rfl⟩ := mem_image.mp hl
      rfl
  | more r _ ih =>
      by_cases hs : s.Nonempty
      · rw [fourthRowMother_prefixes_cons s hs r] at hl
        obtain ⟨t, ht, rfl⟩ := mem_image.mp hl
        simp only [List.length_cons, ih ht]
      · rw [not_nonempty_iff_eq_empty.mp hs, fourthRowMother_prefixes_empty] at hl
        exact False.elim (notMem_empty _ hl)

theorem fourthRowMother_prefix_card (s : Finset ℕ) (r : ℕ) :
    (fourthRowMotherPrefixes s (r + 1)).card = s.card - r := by
  induction r generalizing s with
  | zero =>
      rw [fourthRowMother_prefixes_one, card_image_of_injective]
      · omega
      · intro a b h
        simpa using h
  | succ r ih =>
      by_cases hs : s.Nonempty
      · rw [fourthRowMother_prefixes_cons s hs r, card_image_of_injective,
          ih, card_erase_of_mem (s.min'_mem hs)]
        · omega
        · intro a b h
          exact (List.cons.inj h).2
      · simp [not_nonempty_iff_eq_empty.mp hs, fourthRowMother_prefixes_empty]

noncomputable def fourthRowMotherColourCount (s : Finset ℕ) (χ : ℕ → ℕ) (j : ℕ) : ℕ :=
  (s.filter fun p => χ p = j).card

noncomputable def fourthRowMotherColoured (s : Finset ℕ) (χ : ℕ → ℕ) (cs : List ℕ) :
    Finset (List ℕ) :=
  (fourthRowMotherPrefixes s cs.length).filter fun l => l.map χ = cs

theorem fourthRowMother_coloured_single (s : Finset ℕ) (χ : ℕ → ℕ) (j : ℕ) :
    (fourthRowMotherColoured s χ [j]).card = fourthRowMotherColourCount s χ j := by
  have he : fourthRowMotherColoured s χ [j] =
      (s.filter fun p => χ p = j).image (fun p => [p]) := by
    ext l
    simp only [fourthRowMotherColoured, List.length_singleton,
      fourthRowMother_prefixes_one, mem_filter, mem_image]
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hc⟩
      exact ⟨p, ⟨hp, by simpa using hc⟩, rfl⟩
    · rintro ⟨p, ⟨hp, hc⟩, rfl⟩
      exact ⟨⟨p, hp, rfl⟩, by simp [hc]⟩
  rw [he, card_image_of_injective]
  · rfl
  · intro a b h
    simpa using h

theorem fourthRowMother_coloured_cons (s : Finset ℕ) (hs : s.Nonempty)
    (χ : ℕ → ℕ) (j h : ℕ) (cs : List ℕ) :
    (fourthRowMotherColoured s χ (j :: h :: cs)).card =
      if χ (s.min' hs) = j then
        (fourthRowMotherColoured (s.erase (s.min' hs)) χ (h :: cs)).card else 0 := by
  have he : fourthRowMotherColoured s χ (j :: h :: cs) =
      if χ (s.min' hs) = j then
        (fourthRowMotherColoured (s.erase (s.min' hs)) χ (h :: cs)).image
          (List.cons (s.min' hs)) else ∅ := by
    unfold fourthRowMotherColoured
    simp only [List.length_cons, Nat.add_assoc]
    rw [fourthRowMother_prefixes_cons s hs cs.length]
    by_cases hc : χ (s.min' hs) = j
    · simp only [if_pos hc]
      ext l
      simp only [mem_filter, mem_image]
      constructor
      · rintro ⟨⟨t, ht, rfl⟩, hl⟩
        exact ⟨t, ⟨ht, (List.cons.inj hl).2⟩, rfl⟩
      · rintro ⟨t, ⟨ht, hl⟩, rfl⟩
        exact ⟨⟨t, ht, rfl⟩, by simp only [List.map_cons, hc, hl]⟩
    · simp only [if_neg hc]
      ext l
      simp only [mem_filter, mem_image, notMem_empty, iff_false]
      rintro ⟨⟨t, _, rfl⟩, hl⟩
      exact hc (List.cons.inj hl).1
  rw [he]
  split_ifs
  · apply card_image_of_injective
    intro a b h
    exact (List.cons.inj h).2
  · rfl

theorem fourthRowMother_colour_erase {s : Finset ℕ} {χ : ℕ → ℕ} {p : ℕ}
    (hp : p ∈ s) (j : ℕ) :
    fourthRowMotherColourCount (s.erase p) χ j =
      fourthRowMotherColourCount s χ j - if χ p = j then 1 else 0 := by
  unfold fourthRowMotherColourCount
  rw [filter_erase]
  by_cases hc : χ p = j
  · rw [if_pos hc, card_erase_of_mem (mem_filter.mpr ⟨hp, hc⟩)]
  · rw [if_neg hc, erase_eq_of_notMem (by simp [hc]), Nat.sub_zero]

theorem fourthRowMother_min_colour {s : Finset ℕ} (hs : s.Nonempty)
    {χ : ℕ → ℕ} (hχ : Monotone χ) (hcap : ∀ p ∈ s, χ p ≤ 2) :
    χ (s.min' hs) =
      if 0 < fourthRowMotherColourCount s χ 0 then 0
      else if 0 < fourthRowMotherColourCount s χ 1 then 1 else 2 := by
  have ha := s.min'_mem hs
  have hle := hcap _ ha
  have hc (j : ℕ) (hj : 0 < fourthRowMotherColourCount s χ j) :
      χ (s.min' hs) ≤ j := by
    obtain ⟨p, hp⟩ := card_pos.mp hj
    obtain ⟨hp, he⟩ := mem_filter.mp hp
    exact he ▸ hχ (s.min'_le p hp)
  have hpos : 0 < fourthRowMotherColourCount s χ (χ (s.min' hs)) :=
    card_pos.mpr ⟨s.min' hs, mem_filter.mpr ⟨ha, rfl⟩⟩
  split_ifs with h0 h1
  · exact Nat.eq_zero_of_le_zero (hc 0 h0)
  · have hh := hc 1 h1
    have hne : χ (s.min' hs) ≠ 0 := by
      intro he
      rw [he] at hpos
      exact h0 hpos
    omega
  · have hne0 : χ (s.min' hs) ≠ 0 := by
      intro he
      rw [he] at hpos
      exact h0 hpos
    have hne1 : χ (s.min' hs) ≠ 1 := by
      intro he
      rw [he] at hpos
      exact h1 hpos
    omega

end Wu2008DoubleSieve
