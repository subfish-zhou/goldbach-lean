import MathlibNt.Wu2008DoubleSieve.FourthRowMotherLists

/-! # Exact two-, three-, and four-label prefix membership -/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

theorem fourthRowMother_mem_cons {s : Finset ℕ} {a b : ℕ} {l : List ℕ} :
    a :: b :: l ∈ fourthRowMotherPrefixes s (l.length + 2) ↔
      a ∈ s ∧ (∀ q ∈ s, a ≤ q) ∧
        b :: l ∈ fourthRowMotherPrefixes (s.erase a) (l.length + 1) := by
  by_cases hs : s.Nonempty
  · rw [fourthRowMother_prefixes_cons s hs]
    constructor
    · intro h
      obtain ⟨t, ht, he⟩ := mem_image.mp h
      obtain ⟨ha, rfl⟩ := List.cons.inj he
      subst a
      exact ⟨s.min'_mem hs, fun q hq => s.min'_le q hq, ht⟩
    · rintro ⟨ha, hmin, ht⟩
      have he : s.min' hs = a := le_antisymm (s.min'_le a ha) (hmin _ (s.min'_mem hs))
      rw [he]
      exact mem_image.mpr ⟨b :: l, ht, rfl⟩
  · rw [not_nonempty_iff_eq_empty.mp hs, fourthRowMother_prefixes_empty]
    simp

theorem fourthRowMother_mem_pair {s : Finset ℕ} {a b : ℕ} :
    [a, b] ∈ fourthRowMotherPrefixes s 2 ↔
      a ∈ s ∧ b ∈ s ∧ a < b ∧ ∀ q ∈ s, a ≤ q := by
  rw [show 2 = ([] : List ℕ).length + 2 from rfl, fourthRowMother_mem_cons]
  simp only [List.length_nil, zero_add, fourthRowMother_prefixes_one, mem_image,
    List.cons.injEq, and_true, exists_eq_right, mem_erase]
  constructor
  · rintro ⟨ha, hm, hba, hb⟩
    exact ⟨ha, hb, lt_of_le_of_ne (hm b hb) hba.symm, hm⟩
  · rintro ⟨ha, hb, hab, hm⟩
    exact ⟨ha, hm, ne_of_gt hab, hb⟩

theorem fourthRowMother_mem_triple {s : Finset ℕ} {a b c : ℕ} :
    [a, b, c] ∈ fourthRowMotherPrefixes s 3 ↔
      (a, b, c) ∈ firstTwoTriples s := by
  rw [show 3 = ([c] : List ℕ).length + 2 from rfl,
    fourthRowMother_mem_cons]
  change a ∈ s ∧ (∀ q ∈ s, a ≤ q) ∧ [b, c] ∈ fourthRowMotherPrefixes (s.erase a) 2 ↔ _
  rw [fourthRowMother_mem_pair, mem_firstTwoTriples]
  simp only [mem_erase]
  constructor
  · rintro ⟨ha, hm, ⟨hba, hb⟩, ⟨hca, hc⟩, hbc, hm2⟩
    refine ⟨ha, hb, hc, lt_of_le_of_ne (hm b hb) hba.symm, hbc, ?_⟩
    intro q hq hqb
    by_contra hqa
    exact (not_lt_of_ge (hm2 q ⟨hqa, hq⟩)) hqb
  · rintro ⟨ha, hb, hc, hab, hbc, hm⟩
    refine ⟨ha, ?_, ⟨ne_of_gt hab, hb⟩, ⟨ne_of_gt (hab.trans hbc), hc⟩, hbc, ?_⟩
    · intro q hq
      by_cases hqb : q < b
      · rw [hm q hq hqb]
      · omega
    · intro q hq
      by_contra hqb
      exact hq.1 (hm q hq.2 (by omega))

theorem fourthRowMother_mem_quadruple {s : Finset ℕ} {a b c d : ℕ} :
    [a, b, c, d] ∈ fourthRowMotherPrefixes s 4 ↔
      a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ d ∈ s ∧ a < b ∧ b < c ∧ c < d ∧
        ∀ q ∈ s, q < c → q = a ∨ q = b := by
  rw [show 4 = ([c, d] : List ℕ).length + 2 from rfl,
    fourthRowMother_mem_cons]
  change a ∈ s ∧ (∀ q ∈ s, a ≤ q) ∧ [b, c, d] ∈ fourthRowMotherPrefixes (s.erase a) 3 ↔ _
  rw [fourthRowMother_mem_triple, mem_firstTwoTriples]
  simp only [mem_erase]
  constructor
  · rintro ⟨ha, hm, ⟨hba, hb⟩, ⟨hca, hc⟩, ⟨hda, hd⟩, hbc, hcd, hm2⟩
    refine ⟨ha, hb, hc, hd, lt_of_le_of_ne (hm b hb) hba.symm, hbc, hcd, ?_⟩
    intro q hq hqc
    by_cases hqa : q = a
    · exact Or.inl hqa
    · exact Or.inr (hm2 q ⟨hqa, hq⟩ hqc)
  · rintro ⟨ha, hb, hc, hd, hab, hbc, hcd, hm⟩
    refine ⟨ha, ?_, ⟨ne_of_gt hab, hb⟩, ⟨ne_of_gt (hab.trans hbc), hc⟩,
      ⟨ne_of_gt (hab.trans (hbc.trans hcd)), hd⟩, hbc, hcd, ?_⟩
    · intro q hq
      by_cases hqc : q < c
      · rcases hm q hq hqc with rfl | rfl <;> omega
      · omega
    · intro q hq hqc
      exact (hm q hq.2 hqc).resolve_left hq.1

theorem fourthRowMother_first_two_exact_card (s : Finset ℕ) :
    (firstTwoTriples s).card = s.card - 2 := by
  have he : (firstTwoTriples s).image (fun t => [t.1, t.2.1, t.2.2]) =
      fourthRowMotherPrefixes s 3 := by
    ext l
    constructor
    · rintro hl
      obtain ⟨⟨a, b, c⟩, ht, rfl⟩ := mem_image.mp hl
      exact fourthRowMother_mem_triple.mpr ht
    · intro hl
      have hlen := fourthRowMother_prefix_length hl
      obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp hlen
      exact mem_image.mpr ⟨(a, b, c), fourthRowMother_mem_triple.mp hl, rfl⟩
  have hinj : Function.Injective (fun t : ℕ × ℕ × ℕ => [t.1, t.2.1, t.2.2]) := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    simpa only [List.cons.injEq, and_true, Prod.mk.injEq] using h
  rw [← fourthRowMother_prefix_card s 2, ← he, card_image_of_injective _ hinj]

end Wu2008DoubleSieve
