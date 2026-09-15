import MathlibNt.Wu2008DoubleSieve.NinthSwitchingCountCarriers

/-!
# The three exceptional families in the ninth switching count

Each family is a concrete filter of the labelled atom set. Regrouping by
the prime index or its positive complement pays the pair budget only once
per fibre. Small cofactors include unit cofactors.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

noncomputable def ninthDivisorAtoms (N : ℕ) (w u : ℝ) : Finset NinthLabel :=
  (ninthAtoms N w u).filter (fun x => x.2 ∣ N)

noncomputable def ninthSquareAtoms (N : ℕ) (w u : ℝ) : Finset NinthLabel :=
  (ninthAtoms N w u).filter (fun x => x.1.1 ^ 2 ∣ N - x.2)

noncomputable def ninthSmallAtoms (N : ℕ) (w u : ℝ) : Finset NinthLabel :=
  (ninthAtoms N w u).filter (fun x => (ninthCofactor N x : ℝ) < u)

/-- Prime indices dividing `N`, with every selected pair label retained. -/
theorem ninthDivisorAtoms_card_le {N : ℕ} {k u : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hk : 0 < k) :
    ((ninthDivisorAtoms N ((N : ℝ) ^ k) u).card : ℝ) ≤
      (1 / k ^ 2) * (Real.sqrt N + 1) := by
  have h := ninth_atoms_card_le_indices hN he hk
    (A := ninthDivisorAtoms N ((N : ℝ) ^ k) u) (filter_subset _ _)
    (S := N.primeFactors)
    (by
      intro r hr
      obtain ⟨hrp, hrd, _⟩ := Nat.mem_primeFactors.mp hr
      exact mem_primeIndices.mpr ⟨Nat.le_of_dvd (by omega) hrd, hrp⟩)
    (by
      intro x hx
      obtain ⟨hx, hd⟩ := mem_filter.mp hx
      exact Nat.mem_primeFactors.mpr
        ⟨(mem_primeIndices.mp (ninthAtom_index hx)).2, hd, by omega⟩)
  exact h.trans (mul_le_mul_of_nonneg_left
    (primeFactors_card_le_sqrt_add_one N) (by positivity))

/-- Repeated first primes map to the actual large-prime-square exception
carrier, not a squarefreeness assumption on the complement. -/
theorem ninthSquareAtoms_card_le {N : ℕ} {k u : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hk : 0 < k)
    (hw : 2 ≤ (N : ℝ) ^ k) :
    ((ninthSquareAtoms N ((N : ℝ) ^ k) u).card : ℝ) ≤
      (2 / k ^ 2) * (N : ℝ) ^ (1 - k) := by
  have h := ninth_atoms_card_le_complements hN he hk
    (A := ninthSquareAtoms N ((N : ℝ) ^ k) u) (filter_subset _ _)
    (E := largePrimeSquareExceptions N ((N : ℝ) ^ k))
    (by
      intro x hx
      obtain ⟨hx, hd⟩ := mem_filter.mp hx
      obtain ⟨hrN, hrp⟩ := mem_primeIndices.mp (ninthAtom_index hx)
      obtain ⟨ha, _, _, hwa, _⟩ :=
        mem_lowerPairs_source.mp (mem_filter.mp (mem_ninthAtoms.mp hx).1).1
      exact mem_largePrimeSquareExceptions.mpr
        ⟨complement_pos_of_even hN he hrN hrp, Nat.sub_le N x.2,
          x.1.1, ha, hwa, hd⟩)
  calc
    _ ≤ (1 / k ^ 2) *
        ((largePrimeSquareExceptions N ((N : ℝ) ^ k)).card : ℝ) := h
    _ ≤ (1 / k ^ 2) * (2 * (N : ℝ) ^ (1 - k)) :=
      mul_le_mul_of_nonneg_left
        (largePrimeSquareExceptions_card_le_rpow (by omega) hw) (by positivity)
    _ = _ := by ring

/-- The accepted small-cofactor geometry places the positive complement
in the initial interval, including when the cofactor is one. -/
theorem ninthSmallAtom_complement_le {N : ℕ} {k w : ℝ}
    (hN : 1 < N) (hk : 1 / 14 ≤ k) {x : NinthLabel}
    (hx : x ∈ ninthSmallAtoms N w ((N : ℝ) ^ (1 / 2 - 3 * k))) :
    ((N - x.2 : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 - k) := by
  obtain ⟨hx, hc⟩ := mem_filter.mp hx
  obtain ⟨ht, hau⟩ := mem_filter.mp (mem_ninthAtoms.mp hx).1
  obtain ⟨ha, _, _, _, _, _, hsize⟩ := mem_lowerPairs_source.mp ht
  have h := ninth_small_cofactor_complement_le hN hk
    ((lower_pair_size_iff ha.pos).mpr hsize) hau hc
  have hm : (x.1.1 : ℝ) * x.1.2 * ninthCofactor N x = (N - x.2 : ℕ) := by
    exact_mod_cast ninthAtom_mul_cofactor hx
  rwa [hm] at h

theorem ninthSmallAtoms_card_le {N : ℕ} {k1 k2 : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hk1 : 1 / 14 ≤ k1) (hk2 : 0 < k2) :
    ((ninthSmallAtoms N ((N : ℝ) ^ k2)
      ((N : ℝ) ^ (1 / 2 - 3 * k1))).card : ℝ) ≤
        (1 / k2 ^ 2) * (N : ℝ) ^ (1 - k1) := by
  have h := ninth_atoms_card_le_complements hN he hk2
    (A := ninthSmallAtoms N ((N : ℝ) ^ k2) ((N : ℝ) ^ (1 / 2 - 3 * k1)))
    (filter_subset _ _) (E := Icc 1 ⌊(N : ℝ) ^ (1 - k1)⌋₊)
    (by
      intro x hx
      obtain ⟨hrN, hrp⟩ := mem_primeIndices.mp
        (ninthAtom_index (mem_filter.mp hx).1)
      exact mem_Icc.mpr
        ⟨complement_pos_of_even hN he hrN hrp,
          Nat.le_floor (ninthSmallAtom_complement_le (by omega) hk1 hx)⟩)
  have hcard : ((Icc 1 ⌊(N : ℝ) ^ (1 - k1)⌋₊).card : ℝ) ≤
      (N : ℝ) ^ (1 - k1) := by
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using
      Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) (1 - k1))
  exact h.trans (mul_le_mul_of_nonneg_left hcard (by positivity))

end Wu2008DoubleSieve
