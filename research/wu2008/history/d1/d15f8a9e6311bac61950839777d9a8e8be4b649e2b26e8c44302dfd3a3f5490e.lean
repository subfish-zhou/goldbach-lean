import MathlibNt.Wu2004MeanValue.RefinedCounting
import MathlibNt.Wu2004MeanValue.OriginalLargeTriples

/-!
# Exact finite good/bad subtraction

Bad prime values have unique ordered prime factors. Thus projecting the small
and large bad triples onto `p` loses no multiplicity, even on the square
diagonal. The small cutoff is closed and its large complement is strict.
-/

namespace Wu2004MeanValue

open Classical Finset
open MathlibNt.ChensTheorem
open MathlibNt.SieveTheory.SwitchingPrinciple
noncomputable section

def refinedBad (N : ℕ) (a : ℝ) : Finset ℕ :=
  chenGoodRepresentations N \ refinedGood N a

theorem bad_prime_product_not_mem_refinedGood {N p r q : ℕ} {a : ℝ}
    (ha : a < 2) (hr : r.Prime) (hq : q.Prime)
    (hN : N = p + r * q) (hrq : r ≤ q)
    (hbad : (q : ℝ) ^ (a - 1) < r) : p ∉ refinedGood N a := by
  intro hp
  obtain ⟨_, s, t, ht, hs, hN', hgood⟩ := mem_refinedGood.mp hp
  have he : r * q = s * t := by omega
  rcases hs with rfl | hs
  · simp only [one_mul] at he
    exact Nat.not_prime_mul hr.ne_one hq.ne_one (he ▸ ht)
  · have hst := refined_prime_factor_ordered ht ha hgood
    obtain ⟨rfl, rfl⟩ := ordered_prime_factors_unique hr hq hs ht hrq hst he
    exact (not_le_of_gt hbad) hgood

theorem mem_refinedBad {N p : ℕ} {a : ℝ} (ha : 3 / 2 < a) (ha2 : a < 2) :
    p ∈ refinedBad N a ↔ p.Prime ∧
      ∃ r q : ℕ, r.Prime ∧ q.Prime ∧ N = p + r * q ∧ r ≤ q ∧
        (q : ℝ) ^ (a - 1) < r := by
  constructor
  · intro hp
    obtain ⟨hchen, hnot⟩ := mem_sdiff.mp hp
    obtain ⟨hpp, hprime | ⟨r, q, hr, hq, hrq, hN⟩⟩ :=
      chenGood_prime_or_ordered_product hchen
    · exact False.elim (hnot (prime_complement_mem_refinedGood (by linarith) hpp hprime))
    · refine ⟨hpp, r, q, hr, hq, hN, hrq, ?_⟩
      by_contra h
      exact hnot (mem_refinedGood.mpr
        ⟨hpp, r, q, hq, Or.inr hr, hN, le_of_not_gt h⟩)
  · rintro ⟨hpp, r, q, hr, hq, hN, hrq, hbad⟩
    apply mem_sdiff.mpr
    refine ⟨?_, bad_prime_product_not_mem_refinedGood ha2 hr hq hN hrq hbad⟩
    have hs : Semiprime (N - p) := by
      rw [hN, Nat.add_sub_cancel_left]
      exact mul_prime_semiprime hr hq
    exact mem_filter.mpr ⟨mem_range.mpr (by have := hs.1; omega), hpp, hs⟩

theorem prime_square_mem_refinedBad {N p q : ℕ} {a : ℝ}
    (ha : 3 / 2 < a) (ha2 : a < 2) (hp : p.Prime) (hq : q.Prime)
    (hN : N = p + q * q) : p ∈ refinedBad N a :=
  (mem_refinedBad ha ha2).mpr
    ⟨hp, q, q, hq, hq, hN, le_rfl, prime_square_is_bad hq ha2⟩

theorem refinedGood_bad_partition (N : ℕ) (a : ℝ) :
    refinedGood N a ∪ refinedBad N a = chenGoodRepresentations N ∧
      Disjoint (refinedGood N a) (refinedBad N a) := by
  constructor
  · rw [union_comm]
    exact sdiff_union_of_subset (refinedGood_subset_chenGood N a)
  · exact disjoint_sdiff

theorem chenGood_card_eq_refined_add_bad (N : ℕ) (a : ℝ) :
    (chenGoodRepresentations N).card =
      (refinedGood N a).card + (refinedBad N a).card := by
  have h := card_sdiff_add_card_eq_card (refinedGood_subset_chenGood N a)
  simpa only [refinedBad, Nat.add_comm] using h.symm

theorem refinedBad_eq_original_images (N : ℕ) (a η : ℝ)
    (ha : 3 / 2 < a) (ha2 : a < 2) :
    refinedBad N a =
      (originalTriples N a η).image Prod.fst ∪
        (originalLargeTriples N a η).image Prod.fst := by
  ext p
  constructor
  · intro hp
    obtain ⟨hpp, r, q, hr, hq, hN, hrq, hbad⟩ := (mem_refinedBad ha ha2).mp hp
    rcases le_or_gt ((r : ℝ) * q) (η * N) with hsmall | hlarge
    · exact mem_union.mpr (Or.inl (mem_image.mpr
        ⟨(p, r, q), mem_originalTriples.mpr ⟨hpp, hr, hq, hN, hrq, hbad, hsmall⟩, rfl⟩))
    · exact mem_union.mpr (Or.inr (mem_image.mpr
        ⟨(p, r, q), mem_originalLargeTriples.mpr
          ⟨hpp, hr, hq, hN, hrq, hbad, hlarge⟩, rfl⟩))
  · intro hp
    rcases mem_union.mp hp with hsmall | hlarge
    · obtain ⟨⟨p', r, q⟩, ht, rfl⟩ := mem_image.mp hsmall
      obtain ⟨hpp, hr, hq, hN, hrq, hbad, _⟩ := mem_originalTriples.mp ht
      exact (mem_refinedBad ha ha2).mpr ⟨hpp, r, q, hr, hq, hN, hrq, hbad⟩
    · obtain ⟨⟨p', r, q⟩, ht, rfl⟩ := mem_image.mp hlarge
      obtain ⟨hpp, hr, hq, hN, hrq, hbad, _⟩ := mem_originalLargeTriples.mp ht
      exact (mem_refinedBad ha ha2).mpr ⟨hpp, r, q, hr, hq, hN, hrq, hbad⟩

theorem originalTriples_prime_projection_injOn (N : ℕ) (a η : ℝ) :
    Set.InjOn Prod.fst (originalTriples N a η : Set (ℕ × ℕ × ℕ)) := by
  rintro ⟨p, r, q⟩ ht ⟨p', s, t⟩ hu he
  change p = p' at he
  subst p'
  obtain ⟨_, hr, hq, hN, hrq, _, _⟩ := mem_originalTriples.mp ht
  obtain ⟨_, hs, ht, hN', hst, _, _⟩ := mem_originalTriples.mp hu
  obtain ⟨rfl, rfl⟩ := ordered_prime_factors_unique hr hq hs ht hrq hst (by omega)
  rfl

theorem originalLargeTriples_prime_projection_injOn (N : ℕ) (a η : ℝ) :
    Set.InjOn Prod.fst (originalLargeTriples N a η : Set (ℕ × ℕ × ℕ)) := by
  rintro ⟨p, r, q⟩ ht ⟨p', s, t⟩ hu he
  change p = p' at he
  subst p'
  obtain ⟨_, hr, hq, hN, hrq, _, _⟩ := mem_originalLargeTriples.mp ht
  obtain ⟨_, hs, ht, hN', hst, _, _⟩ := mem_originalLargeTriples.mp hu
  obtain ⟨rfl, rfl⟩ := ordered_prime_factors_unique hr hq hs ht hrq hst (by omega)
  rfl

theorem original_bad_images_disjoint (N : ℕ) (a η : ℝ) :
    Disjoint ((originalTriples N a η).image Prod.fst)
      ((originalLargeTriples N a η).image Prod.fst) := by
  apply disjoint_left.mpr
  intro p hp hp'
  obtain ⟨⟨p', r, q⟩, hsmall, he⟩ := mem_image.mp hp
  obtain ⟨⟨p'', s, t⟩, hlarge, he'⟩ := mem_image.mp hp'
  change p' = p at he
  change p'' = p at he'
  subst p'
  subst p''
  obtain ⟨_, hr, hq, hN, hrq, _, hsmall⟩ := mem_originalTriples.mp hsmall
  obtain ⟨_, hs, ht, hN', hst, _, hlarge⟩ := mem_originalLargeTriples.mp hlarge
  obtain ⟨rfl, rfl⟩ := ordered_prime_factors_unique hr hq hs ht hrq hst (by omega)
  exact (not_lt_of_ge hsmall) hlarge

theorem refinedBad_card_eq_original_counts (N : ℕ) (a η : ℝ)
    (ha : 3 / 2 < a) (ha2 : a < 2) :
    (refinedBad N a).card = originalTripleCount N a η + originalLargeTripleCount N a η := by
  rw [refinedBad_eq_original_images N a η ha ha2,
    card_union_of_disjoint (original_bad_images_disjoint N a η),
    card_image_of_injOn (originalTriples_prime_projection_injOn N a η),
    card_image_of_injOn (originalLargeTriples_prime_projection_injOn N a η)]
  rfl

theorem chenGood_card_eq_refined_add_original_counts (N : ℕ) (a η : ℝ)
    (ha : 3 / 2 < a) (ha2 : a < 2) :
    (chenGoodRepresentations N).card =
      (refinedGood N a).card + originalTripleCount N a η + originalLargeTripleCount N a η := by
  rw [chenGood_card_eq_refined_add_bad N a, refinedBad_card_eq_original_counts N a η ha ha2,
    Nat.add_assoc]

theorem chenGood_card_le_refined_add_bad (N : ℕ) (a η : ℝ)
    (ha : 3 / 2 < a) (ha2 : a < 2) :
    (chenGoodRepresentations N).card ≤
      (refinedGood N a).card + originalTripleCount N a η + originalLargeTripleCount N a η :=
  (chenGood_card_eq_refined_add_original_counts N a η ha ha2).le

/-- The separately owned Wu count has an explicit unit correction. The unit
is not a refined representation and is paid here by at most one. -/
theorem chenGood_add_unit_card_le_refined_add_bad (N : ℕ) (a η : ℝ)
    (ha : 3 / 2 < a) (ha2 : a < 2) :
    (chenGoodRepresentations N).card + (if (N - 1).Prime then 1 else 0) ≤
      (refinedGood N a).card + originalTripleCount N a η + originalLargeTripleCount N a η + 1 := by
  have h := chenGood_card_le_refined_add_bad N a η ha ha2
  split_ifs <;> omega

end
end Wu2004MeanValue
