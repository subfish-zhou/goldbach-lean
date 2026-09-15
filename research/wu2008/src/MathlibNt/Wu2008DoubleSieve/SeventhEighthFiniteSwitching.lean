import MathlibNt.Wu2008DoubleSieve.SeventhEighthCofactor

/-! Label-preserving finite switching. The physical carrier keeps all three
prime coordinates, including the diagonal r = b. -/
namespace Wu2008DoubleSieve.SeventhEighth
open Finset

noncomputable def atoms (N : ℕ) (D : Finset (ℕ × ℕ)) : Finset NinthLabel :=
  D.sigma fun t => sieveCarrier N (t.1 * t.2) (N * t.1) t.2

noncomputable def physical (N : ℕ) (D : Finset (ℕ × ℕ)) : Finset NinthLabel := by
  classical
  exact D.sigma fun t => (range (N + 1)).filter fun r =>
    Nat.Prime r ∧ t.2 ≤ r ∧ t.1 * t.2 * r < N ∧ Nat.Prime (N - t.1 * t.2 * r)

noncomputable def divisorBad (N : ℕ) (D : Finset (ℕ × ℕ)) : Finset NinthLabel := by
  classical
  exact (atoms N D).filter fun x => x.2 ∣ N

noncomputable def squareBad (N : ℕ) (D : Finset (ℕ × ℕ)) : Finset NinthLabel := by
  classical
  exact (atoms N D).filter fun x => x.1.1 ^ 2 ∣ N - x.2

noncomputable def unitBad (N : ℕ) (D : Finset (ℕ × ℕ)) : Finset NinthLabel := by
  classical
  exact (atoms N D).filter fun x => (N - x.2) / (x.1.1 * x.1.2) = 1

noncomputable def good (N : ℕ) (D : Finset (ℕ × ℕ)) : Finset NinthLabel := by
  classical
  exact (atoms N D).filter fun x => ¬x.2 ∣ N ∧
    ¬x.1.1 ^ 2 ∣ N - x.2 ∧ (N - x.2) / (x.1.1 * x.1.2) ≠ 1

@[simp] theorem mem_atoms {N : ℕ} {D : Finset (ℕ × ℕ)} {x : NinthLabel} :
    x ∈ atoms N D ↔ x.1 ∈ D ∧ x.2 ∈ sieveCarrier N (x.1.1 * x.1.2) (N * x.1.1) x.1.2 := by
  classical
  exact mem_sigma

theorem atom_data {N : ℕ} {D : Finset (ℕ × ℕ)} {x : NinthLabel}
    (hx : x ∈ atoms N D) : x.2 ≤ N ∧ Nat.Prime x.2 ∧
    x.1.1 * x.1.2 ∣ N - x.2 := by
  classical
  obtain ⟨hr, hp, hd, _⟩ := mem_filter.mp (mem_atoms.mp hx).2
  exact ⟨by have := mem_range.mp hr; omega, hp, hd⟩

theorem atoms_card (N : ℕ) (D : Finset (ℕ × ℕ)) :
    ((atoms N D).card : ℤ) = ∑ t ∈ D, sieveCount N (t.1 * t.2) (N * t.1) t.2 := by
  classical
  simp only [atoms, card_sigma, Nat.cast_sum, sieveCount]

def switch (N : ℕ) (x : NinthLabel) : NinthLabel :=
  ⟨x.1, (N - x.2) / (x.1.1 * x.1.2)⟩

theorem good_card_le_physical {N : ℕ} {D : Finset (ℕ × ℕ)}
    (hN : 4 ≤ N) (he : Even N)
    (hD : ∀ t ∈ D, Nat.Prime t.1 ∧ Nat.Prime t.2 ∧ N ≤ t.1 * t.2 ^ 3) :
    (good N D).card ≤ (physical N D).card := by
  classical
  apply card_le_card_of_injOn (switch N)
  · intro x hx
    obtain ⟨hx, hn, hs, hu⟩ := mem_filter.mp hx
    obtain ⟨ht, hp⟩ := mem_atoms.mp hx
    obtain ⟨ha, hb, hg⟩ := hD x.1 ht
    obtain ⟨hpN, hpp, hd⟩ := atom_data hx
    have hmul := Nat.mul_div_cancel' hd
    obtain h1 | ⟨hm, hmb⟩ := cofactor_one_or_prime hN he ha hb hg hp hn hs
    · exact (hu h1).elim
    apply mem_sigma.mpr
    refine ⟨ht, mem_filter.mpr ⟨mem_range.mpr ?_, hm, hmb, ?_, ?_⟩⟩
    · dsimp [switch]
      exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    · dsimp [switch]
      rw [hmul]
      have := hpp.pos
      omega
    · dsimp [switch]
      simpa only [hmul, Nat.sub_sub_self hpN] using hpp
  · intro x hx y hy hxy
    have hxa := (mem_filter.mp hx).1
    have hya := (mem_filter.mp hy).1
    obtain ⟨hxp, _, hxd⟩ := atom_data hxa
    obtain ⟨hyp, _, hyd⟩ := atom_data hya
    have ht : x.1 = y.1 := by
      simpa only [switch] using congrArg (fun z : NinthLabel => z.1) hxy
    have hm : (N - x.2) / (x.1.1 * x.1.2) =
        (N - y.2) / (y.1.1 * y.1.2) := congrArg Sigma.snd hxy
    have hcomp : N - x.2 = N - y.2 := by
      rw [← Nat.mul_div_cancel' hxd, ← Nat.mul_div_cancel' hyd, hm, ht]
    have hp : x.2 = y.2 := by omega
    exact Sigma.ext ht (heq_of_eq hp)

theorem atoms_card_le_parts (N : ℕ) (D : Finset (ℕ × ℕ)) :
    (atoms N D).card ≤ (good N D).card + (divisorBad N D).card +
      (squareBad N D).card + (unitBad N D).card := by
  classical
  have hsub : atoms N D ⊆ ((good N D ∪ divisorBad N D) ∪ squareBad N D) ∪ unitBad N D := by
    intro x hx
    by_cases hd : x.2 ∣ N
    · simp only [mem_union]; exact Or.inl (Or.inl (Or.inr (mem_filter.mpr ⟨hx, hd⟩)))
    by_cases hs : x.1.1 ^ 2 ∣ N - x.2
    · simp only [mem_union]; exact Or.inl (Or.inr (mem_filter.mpr ⟨hx, hs⟩))
    by_cases hu : (N - x.2) / (x.1.1 * x.1.2) = 1
    · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hx, hu⟩))
    exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl
      (mem_union.mpr (Or.inl (mem_filter.mpr ⟨hx, hd, hs, hu⟩))))))
  have h0 := card_le_card hsub
  have h1 := card_union_le ((good N D ∪ divisorBad N D) ∪ squareBad N D) (unitBad N D)
  have h2 := card_union_le (good N D ∪ divisorBad N D) (squareBad N D)
  have h3 := card_union_le (good N D) (divisorBad N D)
  omega

/-- No target count or packing hypothesis: only primality and domain geometry. -/
theorem finite_switching {N : ℕ} {D : Finset (ℕ × ℕ)}
    (hN : 4 ≤ N) (he : Even N)
    (hD : ∀ t ∈ D, Nat.Prime t.1 ∧ Nat.Prime t.2 ∧ N ≤ t.1 * t.2 ^ 3) :
    (∑ t ∈ D, sieveCount N (t.1 * t.2) (N * t.1) t.2 : ℤ) ≤
      (physical N D).card + (divisorBad N D).card + (squareBad N D).card +
        (unitBad N D).card := by
  rw [← atoms_card]
  have hp := atoms_card_le_parts N D
  have hg := good_card_le_physical hN he hD
  have h : (atoms N D).card ≤ (physical N D).card + (divisorBad N D).card +
      (squareBad N D).card + (unitBad N D).card := by omega
  exact_mod_cast h

end Wu2008DoubleSieve.SeventhEighth
