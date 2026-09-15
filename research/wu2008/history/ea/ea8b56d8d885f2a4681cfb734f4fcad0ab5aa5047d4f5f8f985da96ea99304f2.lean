import MathlibNt.Wu2004MeanValue.OriginalTriples

/-!
# Literal triples in one half-open block

Interior triples inject into the accepted open `blockPairs` sieve. The three
new boundary payments concern the original target, not AP endpoint errors.
-/

namespace Wu2004MeanValue

open Classical Finset
open scoped BigOperators
noncomputable section

theorem originalTriple_product_lt_rpow {N : ℕ} {a η : ℝ} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ originalTriples N a η) (ha : 1 < a) :
    (t.2.1 : ℝ) * t.2.2 < (t.2.1 : ℝ) ^ (a / (a - 1)) := by
  have hr0 : (0 : ℝ) < t.2.1 := by
    exact_mod_cast (mem_originalTriples.mp ht).2.1.pos
  have hpow := (mem_originalTriples.mp ht).2.2.2.2.2.1
  have hq : (t.2.2 : ℝ) < (t.2.1 : ℝ) ^ (a - 1)⁻¹ :=
    (Real.lt_rpow_inv_iff_of_pos (Nat.cast_nonneg _) hr0.le (sub_pos.mpr ha)).mpr hpow
  have hexp : a / (a - 1) = 1 + (a - 1)⁻¹ := by
    field_simp [(sub_pos.mpr ha).ne']
    ring
  calc
    (t.2.1 : ℝ) * t.2.2 < (t.2.1 : ℝ) * (t.2.1 : ℝ) ^ (a - 1)⁻¹ :=
      mul_lt_mul_of_pos_left hq hr0
    _ = (t.2.1 : ℝ) ^ (a / (a - 1)) := by
      rw [hexp, Real.rpow_add hr0, Real.rpow_one]

theorem originalTriple_block_geometry {H : ℝ} {N : ℕ} {a η : ℝ}
    {t : ℕ × ℕ × ℕ} (ht : t ∈ originalTriplesBlock H N a η)
    (hH : 0 < H) (ha : 1 < a) :
    H ^ ((a - 1) / a) < t.2.1 ∧
      (t.2.1 : ℝ) ≤ Real.sqrt (2 * H) ∧
      (t.2.1 : ℝ) * t.2.2 < (t.2.1 : ℝ) ^ (a / (a - 1)) := by
  obtain ⟨ht, hlow, hupp⟩ := mem_filter.mp ht
  have hp := originalTriple_product_lt_rpow ht ha
  have hr0 : (0 : ℝ) ≤ t.2.1 := Nat.cast_nonneg _
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hexp : a / (a - 1) * ((a - 1) / a) = 1 := by
    field_simp [(sub_pos.mpr ha).ne', ha0.ne']
  have h := Real.rpow_lt_rpow hH.le (hlow.trans hp) (div_pos (sub_pos.mpr ha) ha0)
  rw [← Real.rpow_mul hr0, hexp, Real.rpow_one] at h
  exact ⟨h, originalTriple_source_le_sqrt ht hupp, hp⟩

def originalTriplesBlockInterior (H : ℝ) (N : ℕ) (a η : ℝ) :
    Finset (ℕ × ℕ × ℕ) :=
  (originalTriplesBlock H N a η).filter (fun t =>
    (t.2.1 : ℝ) * t.2.2 ≠ 2 * H ∧
    (t.2.1 : ℝ) * t.2.2 ≠ η * N ∧ t.2.1 ≠ t.2.2)

theorem originalTriple_interior_mem_blockPairs {H : ℝ} {N : ℕ} {a η : ℝ}
    {t : ℕ × ℕ × ℕ} (ht : t ∈ originalTriplesBlockInterior H N a η)
    (hH : 0 < H) (ha : 1 < a) (hη : η < 1 / 2) :
    originalTriplePair t ∈ blockPairs H N a η := by
  obtain ⟨hb, htop, hcap, hdiag⟩ := mem_filter.mp ht
  have hgeom := originalTriple_block_geometry hb hH ha
  obtain ⟨ht, hlow, hupp⟩ := mem_filter.mp hb
  obtain ⟨_, hr, hq, _, hrq, _, hsmall⟩ := mem_originalTriples.mp ht
  have hr0 : (0 : ℝ) < t.2.1 := by exact_mod_cast hr.pos
  have hstrict : (t.2.1 : ℝ) < t.2.2 := by
    exact_mod_cast (lt_of_le_of_ne hrq hdiag)
  have hlo : blockLower H t.2.1 < (t.2.1 : ℝ) * t.2.2 := by
    exact max_lt hlow (by nlinarith [mul_lt_mul_of_pos_left hstrict hr0])
  have hhi : (t.2.1 : ℝ) * t.2.2 < blockUpper H N a η t.2.1 :=
    lt_min (lt_min (lt_of_le_of_ne hupp htop) hgeom.2.2)
      (lt_of_le_of_ne hsmall hcap)
  apply mem_blockPairs.mpr
  exact ⟨mem_blockSource.mpr
    ⟨hr, originalTriple_source_coprime ht hη, hgeom.1, hgeom.2.1, hlo.trans hhi⟩,
    hq, hlo, hhi⟩

theorem originalTriplesBlockInterior_card_le {H : ℝ} {N : ℕ} {a η z : ℝ}
    (hH : 0 < H) (ha : 1 < a) (hη : η < 1 / 2)
    (hz : z ≤ (1 - η) * N) :
    (originalTriplesBlockInterior H N a η).card ≤ blockSiftedCount H N a η z := by
  apply card_le_card_of_injOn originalTriplePair
  · intro t ht
    apply mem_filter.mpr
    exact ⟨originalTriple_interior_mem_blockPairs ht hH ha hη,
      originalTriple_prime_value_sifted (mem_filter.mp (mem_filter.mp ht).1).1 hz⟩
  · intro t ht u hu he
    exact originalTriplePair_injOn N a η
      (mem_filter.mp (mem_filter.mp ht).1).1
      (mem_filter.mp (mem_filter.mp hu).1).1 he

theorem originalTriplesBlock_product_boundary_card_le
    {H : ℝ} {N : ℕ} {a η : ℝ} (X : ℝ) :
    ((originalTriplesBlock H N a η).filter
      (fun t => (t.2.1 : ℝ) * t.2.2 = X)).card ≤ ⌊Real.sqrt (2 * H)⌋₊ + 1 := by
  apply le_trans
    (card_le_card_of_injOn (fun t : ℕ × ℕ × ℕ => t.2.1)
      (t := range (⌊Real.sqrt (2 * H)⌋₊ + 1)) ?_ ?_)
    (by rw [card_range])
  · intro t ht
    obtain ⟨hb, _⟩ := mem_filter.mp ht
    obtain ⟨ht, _, hupp⟩ := mem_filter.mp hb
    change t.2.1 ∈ range (⌊Real.sqrt (2 * H)⌋₊ + 1)
    simpa only [mem_range, Nat.lt_succ_iff,
      Nat.le_floor_iff (Real.sqrt_nonneg _)] using originalTriple_source_le_sqrt ht hupp
  · intro t ht u hu hr
    change t.2.1 = u.2.1 at hr
    obtain ⟨htb, htX⟩ := mem_filter.mp ht
    obtain ⟨hub, huX⟩ := mem_filter.mp hu
    have ht := (mem_filter.mp htb).1
    have hu := (mem_filter.mp hub).1
    have hr0 : (t.2.1 : ℝ) ≠ 0 := by
      exact_mod_cast (mem_originalTriples.mp ht).2.1.ne_zero
    have hq : t.2.2 = u.2.2 := by
      have he : (t.2.1 : ℝ) * t.2.2 = (t.2.1 : ℝ) * u.2.2 := by
        calc
          _ = X := htX
          _ = (u.2.1 : ℝ) * u.2.2 := huX.symm
          _ = _ := by rw [hr]
      exact_mod_cast mul_left_cancel₀ hr0 he
    apply originalTriplePair_injOn N a η ht hu
    exact congrArg (fun rq : ℕ × ℕ => (⟨rq.1, rq.2⟩ : Σ _ : ℕ, ℕ))
      (Prod.ext hr hq)

theorem originalTriplesBlock_diagonal_card_le {H : ℝ} {N : ℕ} {a η : ℝ} :
    ((originalTriplesBlock H N a η).filter
      (fun t => t.2.1 = t.2.2)).card ≤ ⌊Real.sqrt (2 * H)⌋₊ + 1 := by
  apply le_trans
    (card_le_card_of_injOn (fun t : ℕ × ℕ × ℕ => t.2.1)
      (t := range (⌊Real.sqrt (2 * H)⌋₊ + 1)) ?_ ?_)
    (by rw [card_range])
  · intro t ht
    obtain ⟨hb, _⟩ := mem_filter.mp ht
    obtain ⟨ht, _, hupp⟩ := mem_filter.mp hb
    change t.2.1 ∈ range (⌊Real.sqrt (2 * H)⌋₊ + 1)
    simpa only [mem_range, Nat.lt_succ_iff,
      Nat.le_floor_iff (Real.sqrt_nonneg _)] using originalTriple_source_le_sqrt ht hupp
  · intro t ht u hu hr
    change t.2.1 = u.2.1 at hr
    obtain ⟨htb, htd⟩ := mem_filter.mp ht
    obtain ⟨hub, hud⟩ := mem_filter.mp hu
    apply originalTriplePair_injOn N a η (mem_filter.mp htb).1 (mem_filter.mp hub).1
    exact congrArg (fun rq : ℕ × ℕ => (⟨rq.1, rq.2⟩ : Σ _ : ℕ, ℕ))
      (Prod.ext hr (htd.symm.trans (hr.trans hud)))

/-- Every original boundary is paid, including coincident boundary events. -/
theorem originalTripleBlockCount_le {H : ℝ} {N : ℕ} {a η z : ℝ}
    (hH : 0 < H) (ha : 1 < a) (hη : η < 1 / 2)
    (hz : z ≤ (1 - η) * N) :
    originalTripleBlockCount H N a η ≤
      blockSiftedCount H N a η z + 3 * (⌊Real.sqrt (2 * H)⌋₊ + 1) := by
  let I := originalTriplesBlockInterior H N a η
  let T := (originalTriplesBlock H N a η).filter
    (fun t => (t.2.1 : ℝ) * t.2.2 = 2 * H)
  let C := (originalTriplesBlock H N a η).filter
    (fun t => (t.2.1 : ℝ) * t.2.2 = η * N)
  let D := (originalTriplesBlock H N a η).filter (fun t => t.2.1 = t.2.2)
  have hcover : originalTriplesBlock H N a η ⊆ I ∪ T ∪ C ∪ D := by
    intro t ht
    simp only [mem_union]
    by_cases htT : (t.2.1 : ℝ) * t.2.2 = 2 * H
    · exact Or.inl (Or.inl (Or.inr (mem_filter.mpr ⟨ht, htT⟩)))
    by_cases htC : (t.2.1 : ℝ) * t.2.2 = η * N
    · exact Or.inl (Or.inr (mem_filter.mpr ⟨ht, htC⟩))
    by_cases htD : t.2.1 = t.2.2
    · exact Or.inr (mem_filter.mpr ⟨ht, htD⟩)
    exact Or.inl (Or.inl (Or.inl (mem_filter.mpr ⟨ht, htT, htC, htD⟩)))
  have hcard := card_le_card hcover
  have hIT := card_union_le I T
  have hITC := card_union_le (I ∪ T) C
  have hITCD := card_union_le (I ∪ T ∪ C) D
  have hI : I.card ≤ blockSiftedCount H N a η z :=
    originalTriplesBlockInterior_card_le hH ha hη hz
  have hT : T.card ≤ ⌊Real.sqrt (2 * H)⌋₊ + 1 :=
    originalTriplesBlock_product_boundary_card_le (2 * H)
  have hC : C.card ≤ ⌊Real.sqrt (2 * H)⌋₊ + 1 :=
    originalTriplesBlock_product_boundary_card_le (η * N)
  have hD : D.card ≤ ⌊Real.sqrt (2 * H)⌋₊ + 1 :=
    originalTriplesBlock_diagonal_card_le
  change (originalTriplesBlock H N a η).card ≤ _
  omega

end
end Wu2004MeanValue
