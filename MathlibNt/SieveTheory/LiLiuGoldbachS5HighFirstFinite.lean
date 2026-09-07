import MathlibNt.SieveTheory.LiLiuGoldbachS5FirstPrimeSplit
import MathlibNt.SieveTheory.LiLiuGoldbachS5CountTransport

open scoped BigOperators
open Finset

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem goldbachC10HighFirstPairs_eq_filter (N : ℕ) (hN : 2 ≤ N) :
    goldbachC10Pairs N ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) =
      (goldbachC9Pairs N).filter (fun rs => (N : ℝ) ^ (1 / 10 : ℝ) ≤ (rs.1 : ℝ)) := by
  classical
  rw [goldbachC9Pairs_eq_C10Pairs]
  exact (goldbachC10Pairs_filter_first_ge _ _ _ _
    (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num))).symm

noncomputable def goldbachS5HighFirstActualAtoms (N : ℕ) (ε : ℝ) :
    Finset (Σ _rs : ℕ × ℕ, ℕ) := by
  classical
  exact (goldbachS5ActualAtoms N ε).filter
    (fun x => (N : ℝ) ^ (1 / 10 : ℝ) ≤ (x.1.1 : ℝ))

theorem goldbachS5HighFirstClosed_eq_card (N : ℕ) (hN : 2 ≤ N) (ε : ℝ) :
    goldbachS5Closed (goldbachDifferenceCarrier N ε) N
      ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) =
        ((goldbachS5HighFirstActualAtoms N ε).card : ℤ) := by
  classical
  have heq : goldbachS5HighFirstActualAtoms N ε =
      (goldbachC10Pairs N ((N : ℝ) ^ (1 / 10 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ))).sigma (fun rs =>
          (goldbachDifferenceCarrier N ε).filter
            (literalHPoint (N * rs.1) (rs.1 * rs.2) rs.2)) := by
    ext x
    rw [goldbachC10HighFirstPairs_eq_filter N hN]
    simp only [goldbachS5HighFirstActualAtoms, mem_filter,
      mem_goldbachS5ActualAtoms_iff, mem_sigma, goldbachC9Prod, goldbachC8Prod]
    tauto
  rw [heq, goldbachS5Closed_eq_sum_goldbachC10Pairs]
  simp [literalH]

/-- Equality of labelled mothers, including the closed first-prime boundary. -/
theorem goldbachB9HighFirstAtoms_eq_filter (N : ℕ) (hN : 2 ≤ N) :
    goldbachB10Atoms N 0 ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) =
      (goldbachB9PlusAtoms N).filter
        (fun x => (N : ℝ) ^ (1 / 10 : ℝ) ≤ (x.1.1 : ℝ)) := by
  classical
  rw [goldbachB9PlusAtoms_eq_B10ZeroPrefix]
  ext x
  simp only [mem_goldbachB10Atoms_iff, mem_filter,
    goldbachC10HighFirstPairs_eq_filter N hN, goldbachC9Pairs_eq_C10Pairs]
  tauto

theorem goldbachB9HighFirstSiftedAtoms_eq_filter (N : ℕ) (hN : 2 ≤ N) (Z : ℝ) :
    goldbachB10SiftedAtoms N 0 ((N : ℝ) ^ (1 / 10 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)) Z =
      (goldbachB9PlusSiftedAtoms N Z).filter
        (fun x => (N : ℝ) ^ (1 / 10 : ℝ) ≤ (x.1.1 : ℝ)) := by
  classical
  rw [goldbachB9PlusSiftedAtoms_eq_B10ZeroPrefix]
  ext x
  simp only [mem_goldbachB10SiftedAtoms_iff, mem_filter,
    goldbachC10HighFirstPairs_eq_filter N hN, goldbachC9Pairs_eq_C10Pairs]
  tauto

/-- The original injective atom map preserves the restricted first-prime label. -/
theorem goldbachS5HighFirstSwitch_mem {N : ℕ} {ε : ℝ}
    (hN : 2 ≤ N) (hε : 0 < ε)
    (hcut : (N : ℝ) ^ (2 / 3 : ℝ) ≤ ε * N)
    {x : Σ _rs : ℕ × ℕ, ℕ}
    (hx : x ∈ goldbachS5GoodNonsquareAtoms N ε)
    (hfirst : (N : ℝ) ^ (1 / 10 : ℝ) ≤ (x.1.1 : ℝ)) :
    goldbachS5Switch x ∈ goldbachB10Atoms N 0
      ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) ∧
      (goldbachB9PlusOutput N (goldbachS5Switch x)).Prime := by
  classical
  obtain ⟨hp, _⟩ := goldbachS5Switch_mem_primeAtoms hN hε hcut hx
  obtain ⟨hm, hprime⟩ := mem_filter.mp hp
  rw [goldbachB9HighFirstAtoms_eq_filter N hN]
  exact ⟨mem_filter.mpr ⟨hm, hfirst⟩, hprime⟩

/-- Only the error budgets use the full family; the main term is the high mother itself. -/
theorem goldbachS5HighFirstClosed_le_sifted {N : ℕ} {ε Z : ℝ}
    (hN : 2 ≤ N) (hε : 0 < ε)
    (hcut : (N : ℝ) ^ (2 / 3 : ℝ) ≤ ε * N) (hZ : 1 ≤ Z) :
    goldbachS5Closed (goldbachDifferenceCarrier N ε) N
      ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) ≤
        goldbachB10SiftedCount N 0 ((N : ℝ) ^ (1 / 10 : ℝ))
          ((N : ℝ) ^ (1 / 3 : ℝ)) Z +
        400 * goldbachBadCount (goldbachDifferenceCarrier N ε) N +
        400 * goldbachS5SquareCount N + 400 * (Nat.floor Z : ℤ) := by
  classical
  let H := fun x : Σ _rs : ℕ × ℕ, ℕ =>
    (N : ℝ) ^ (1 / 10 : ℝ) ≤ (x.1.1 : ℝ)
  let G := (goldbachS5GoodNonsquareAtoms N ε).filter H
  let P := (goldbachB9PlusPrimeAtoms N).filter H
  let S := (goldbachB9PlusSiftedAtoms N Z).filter H
  let L := (goldbachB9PlusAtoms N).filter
    (fun x => (goldbachB9PlusOutput N x : ℝ) < Z)
  have hsplit : goldbachS5HighFirstActualAtoms N ε ⊆
      G ∪ (goldbachS5BadAtoms N ε ∪ goldbachS5SquareAtoms N ε) := by
    intro x hx
    simp only [goldbachS5HighFirstActualAtoms, mem_filter] at hx
    simp only [G, mem_union, mem_filter, goldbachS5GoodNonsquareAtoms,
      goldbachS5GoodAtoms, goldbachS5BadAtoms, goldbachS5SquareAtoms, H]
    tauto
  have hcard : (goldbachS5HighFirstActualAtoms N ε).card ≤
      G.card + (goldbachS5BadAtoms N ε).card + (goldbachS5SquareAtoms N ε).card :=
    (card_le_card hsplit).trans ((card_union_le _ _).trans
      (by simpa [Nat.add_assoc] using
        Nat.add_le_add_left (card_union_le (goldbachS5BadAtoms N ε)
          (goldbachS5SquareAtoms N ε)) G.card))
  have hG : G.card ≤ P.card := by
    apply card_le_card_of_injOn goldbachS5Switch
    · intro x hx
      obtain ⟨hx, hfirst⟩ := mem_filter.mp hx
      have hm := goldbachS5HighFirstSwitch_mem hN hε hcut hx hfirst
      rw [goldbachB9HighFirstAtoms_eq_filter N hN] at hm
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨(mem_filter.mp hm.1).1, hm.2⟩,
        (mem_filter.mp hm.1).2⟩
    · intro x hx y hy hxy
      exact goldbachS5Switch_injOn
        (mem_filter.mp (mem_filter.mp (mem_filter.mp hx).1).1).1
        (mem_filter.mp (mem_filter.mp (mem_filter.mp hy).1).1).1 hxy
  have hPS : P ⊆ S ∪ L := by
    intro x hx
    obtain ⟨hxP, hxH⟩ := mem_filter.mp hx
    by_cases hlo : (goldbachB9PlusOutput N x : ℝ) < Z
    · exact mem_union_right _ (mem_filter.mpr ⟨(mem_filter.mp hxP).1, hlo⟩)
    · exact mem_union_left _ (mem_filter.mpr
        ⟨goldbachB9Plus_highPrime_subset_sifted N Z
          (mem_filter.mpr ⟨hxP, le_of_not_gt hlo⟩), hxH⟩)
  have hP : P.card ≤ S.card + L.card := (card_le_card hPS).trans (card_union_le _ _)
  have hbad := goldbachS5BadAtoms_card_le (N := N) hε
  have hsquare := goldbachS5SquareAtoms_card_le (N := N) hε
  have hlow := goldbachB9Plus_low_card_le N hZ
  have hS : (S.card : ℤ) = goldbachB10SiftedCount N 0
      ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) Z := by
    rw [goldbachB10SiftedCount_eq_card_atoms, goldbachB9HighFirstSiftedAtoms_eq_filter N hN]
  rw [goldbachS5HighFirstClosed_eq_card N hN, ← hS]
  dsimp only [L] at hP
  omega

theorem goldbachS5HighFirstClosed_le_sifted_normalized (ε η : ℝ)
    (hε : 0 < ε) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ Z : ℝ,
      1 ≤ Z → Z ≤ Real.sqrt (N : ℝ) →
      (goldbachS5Closed (goldbachDifferenceCarrier N ε) N
        ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ) ≤
        (goldbachB10SiftedCount N 0 ((N : ℝ) ^ (1 / 10 : ℝ))
          ((N : ℝ) ^ (1 / 3 : ℝ)) Z : ℝ) +
        η * (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by
  obtain ⟨Ns, hNs, hs⟩ := exists_goldbachS4_switch_threshold ε hε
  obtain ⟨Nb, hNb, hb⟩ := goldbachS4_finiteLoss_normalized (η / 2) (by positivity)
  obtain ⟨Nq, _hNq, hq⟩ := goldbachS5SquareCount_normalized (η / 2) (by positivity)
  refine ⟨max Ns (max Nb Nq), (hNb.trans (le_max_left _ _)).trans (le_max_right _ _), ?_⟩
  intro N hN Z hZ hZu
  have hsN : Ns ≤ N := (le_max_left _ _).trans hN
  have hbN : Nb ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hqN : Nq ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hfinite := goldbachS5HighFirstClosed_le_sifted (hNs.trans hsN) hε (hs N hsN) hZ
  have hreal :
      (goldbachS5Closed (goldbachDifferenceCarrier N ε) N
        ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ) ≤
        (goldbachB10SiftedCount N 0 ((N : ℝ) ^ (1 / 10 : ℝ))
          ((N : ℝ) ^ (1 / 3 : ℝ)) Z : ℝ) +
        400 * (goldbachBadCount (goldbachDifferenceCarrier N ε) N : ℝ) +
        400 * (goldbachS5SquareCount N : ℝ) + 400 * (Nat.floor Z : ℝ) := by
    exact_mod_cast hfinite
  have hbad := hb N hbN ε Z (by linarith) hZu
  have hsquare := hq N hqN
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig