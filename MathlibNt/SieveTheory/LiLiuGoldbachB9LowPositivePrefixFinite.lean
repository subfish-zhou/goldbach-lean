import MathlibNt.SieveTheory.LiLiuGoldbachS5FirstPrimeSplit
import MathlibNt.SieveTheory.LiLiuGoldbachB9C10Bridge

open scoped BigOperators
open Finset

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableGoldbachB9LowPositivePrefix (p : Prop) :
    Decidable p := Classical.propDecidable p

noncomputable def goldbachS5LowFirstActualAtoms (N : ℕ) (eps : ℝ) :
    Finset (Σ _rs : ℕ × ℕ, ℕ) := by
  classical
  exact (goldbachS5ActualAtoms N eps).filter
    (fun x => (x.1.1 : ℝ) < (N : ℝ) ^ (1 / 10 : ℝ))

theorem goldbachS5ClosedBelow_eq_card_lowActualAtoms (N : ℕ) (eps : ℝ) :
    goldbachS5ClosedBelow (goldbachDifferenceCarrier N eps) N
      ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))
      ((N : ℝ) ^ (1 / 10 : ℝ)) =
        ((goldbachS5LowFirstActualAtoms N eps).card : ℤ) := by
  classical
  have heq : goldbachS5LowFirstActualAtoms N eps =
      ((goldbachC10Pairs N ((N : ℝ) ^ (4 / 53 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ))).filter
          (fun rs => (rs.1 : ℝ) < (N : ℝ) ^ (1 / 10 : ℝ))).sigma
            (fun rs => (goldbachDifferenceCarrier N eps).filter
              (literalHPoint (N * rs.1) (rs.1 * rs.2) rs.2)) := by
    ext x
    simp only [goldbachS5LowFirstActualAtoms, mem_filter,
      mem_goldbachS5ActualAtoms_iff, mem_sigma, goldbachC9Pairs_eq_C10Pairs,
      goldbachC9Prod, goldbachC8Prod]
    tauto
  rw [heq]
  simp [goldbachS5ClosedBelow, literalH]

/-- The original positive-epsilon B10 mother, restricted only at the first label. -/
noncomputable def goldbachB9LowPositivePrefixAtoms (N : ℕ) (eps : ℝ) :
    Finset (Σ _rs : ℕ × ℕ, ℕ) := by
  classical
  exact (goldbachB10Atoms N eps ((N : ℝ) ^ (4 / 53 : ℝ))
    ((N : ℝ) ^ (1 / 3 : ℝ))).filter
      (fun x => (x.1.1 : ℝ) < (N : ℝ) ^ (1 / 10 : ℝ))

noncomputable def goldbachB9LowPositivePrefixSiftedAtoms (N : ℕ) (eps Z : ℝ) :
    Finset (Σ _rs : ℕ × ℕ, ℕ) := by
  classical
  exact (goldbachB10SiftedAtoms N eps ((N : ℝ) ^ (4 / 53 : ℝ))
    ((N : ℝ) ^ (1 / 3 : ℝ)) Z).filter
      (fun x => (x.1.1 : ℝ) < (N : ℝ) ^ (1 / 10 : ℝ))

noncomputable def goldbachB9LowPositivePrefixSiftedCount (N : ℕ) (eps Z : ℝ) : ℤ :=
  (goldbachB9LowPositivePrefixSiftedAtoms N eps Z).card

noncomputable def goldbachB9LowPositivePrefixPrimeAtoms (N : ℕ) (eps : ℝ) :
    Finset (Σ _rs : ℕ × ℕ, ℕ) := by
  classical
  exact (goldbachB9LowPositivePrefixAtoms N eps).filter
    (fun x => (goldbachPi10Output N x).Prime)

theorem mem_goldbachB9LowPositivePrefixAtoms_iff {N : ℕ} {eps : ℝ}
    {x : Σ _rs : ℕ × ℕ, ℕ} :
    x ∈ goldbachB9LowPositivePrefixAtoms N eps ↔
      x ∈ goldbachB10Atoms N eps ((N : ℝ) ^ (4 / 53 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)) ∧
      (x.1.1 : ℝ) < (N : ℝ) ^ (1 / 10 : ℝ) := by
  classical
  exact mem_filter

theorem mem_goldbachB9LowPositivePrefixSiftedAtoms_iff {N : ℕ} {eps Z : ℝ}
    {x : Σ _rs : ℕ × ℕ, ℕ} :
    x ∈ goldbachB9LowPositivePrefixSiftedAtoms N eps Z ↔
      x ∈ goldbachB10SiftedAtoms N eps ((N : ℝ) ^ (4 / 53 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)) Z ∧
      (x.1.1 : ℝ) < (N : ℝ) ^ (1 / 10 : ℝ) := by
  classical
  exact mem_filter

theorem goldbachB9LowPositivePrefixSiftedAtoms_eq_filter (N : ℕ) (eps Z : ℝ) :
    goldbachB9LowPositivePrefixSiftedAtoms N eps Z =
      (goldbachB9LowPositivePrefixAtoms N eps).filter
        (fun x => literalHPoint N 1 Z (goldbachPi10Output N x)) := by
  classical
  ext x
  simp only [mem_goldbachB9LowPositivePrefixSiftedAtoms_iff, mem_filter,
    mem_goldbachB9LowPositivePrefixAtoms_iff, mem_goldbachB10Atoms_iff,
    mem_goldbachB10SiftedAtoms_iff]
  tauto

theorem goldbachB9LowPositivePrefixPrimeAtoms_eq_Pi10_filter (N : ℕ) (eps : ℝ) :
    goldbachB9LowPositivePrefixPrimeAtoms N eps =
      (goldbachPi10Atoms N eps ((N : ℝ) ^ (4 / 53 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ))).filter
          (fun x => (x.1.1 : ℝ) < (N : ℝ) ^ (1 / 10 : ℝ)) := by
  classical
  ext x
  rw [goldbachB9LowPositivePrefixPrimeAtoms, mem_filter]
  simp only [mem_filter,
    mem_goldbachB9LowPositivePrefixAtoms_iff, mem_goldbachB10Atoms_iff,
    mem_goldbachPi10Atoms_iff, goldbachB10Point, goldbachPi10Point,
    goldbachPi10Output]
  tauto

theorem goldbachB9LowPositivePrefixAtoms_product_window {N : ℕ} {eps : ℝ}
    {x : Σ _rs : ℕ × ℕ, ℕ} (hx : x ∈ goldbachB9LowPositivePrefixAtoms N eps) :
    x.2.Prime ∧
      eps * (N : ℝ) < ((x.1.1 * x.1.2) * x.2 : ℕ) ∧
      (((x.1.1 * x.1.2) * x.2 : ℕ) : ℝ) < N := by
  obtain ⟨hxB, _⟩ := mem_goldbachB9LowPositivePrefixAtoms_iff.mp hx
  obtain ⟨hrs, _, hq, hlo, hhi⟩ := mem_goldbachB10Atoms_iff.mp hxB
  have hp := mem_goldbachC10Pairs_iff.mp hrs
  have hm : (0 : ℝ) < (goldbachC10Prod x.1 : ℝ) := by
    exact_mod_cast Nat.mul_pos hp.1.pos hp.2.1.pos
  refine ⟨hq, ?_, ?_⟩
  · simpa [goldbachC10Prod, Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using
      (div_lt_iff₀ hm).mp hlo
  · simpa [goldbachC10Prod, Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using
      (lt_div_iff₀ hm).mp hhi

theorem goldbachB9LowPositivePrefixSiftedAtoms_product_window {N : ℕ} {eps Z : ℝ}
    {x : Σ _rs : ℕ × ℕ, ℕ}
    (hx : x ∈ goldbachB9LowPositivePrefixSiftedAtoms N eps Z) :
    x.2.Prime ∧
      eps * (N : ℝ) < ((x.1.1 * x.1.2) * x.2 : ℕ) ∧
      (((x.1.1 * x.1.2) * x.2 : ℕ) : ℝ) < N := by
  classical
  rw [goldbachB9LowPositivePrefixSiftedAtoms_eq_filter] at hx
  exact goldbachB9LowPositivePrefixAtoms_product_window (mem_filter.mp hx).1

/-- This inclusion is used only for the already-paid low-output error. -/
theorem goldbachB9LowPositivePrefixAtoms_subset_B9Plus (N : ℕ) (eps : ℝ) :
    goldbachB9LowPositivePrefixAtoms N eps ⊆ goldbachB9PlusAtoms N := by
  intro x hx
  have hrs := (mem_goldbachB10Atoms_iff.mp
    (mem_goldbachB9LowPositivePrefixAtoms_iff.mp hx).1).1
  obtain ⟨hq, _, hhi⟩ := goldbachB9LowPositivePrefixAtoms_product_window hx
  refine mem_goldbachB9PlusAtoms_iff.mpr
    ⟨(goldbachC9Pairs_eq_C10Pairs N).symm ▸ hrs, hq, ?_⟩
  exact_mod_cast hhi

/-- Retain the strict epsilon bound from the original integer, before any switch. -/
theorem goldbachS5ActualAtom_retained_epsilon {N : ℕ} {eps : ℝ}
    {x : Σ _rs : ℕ × ℕ, ℕ} (heps : 0 < eps)
    (hx : x ∈ goldbachS5ActualAtoms N eps) :
    eps * (N : ℝ) < (goldbachC9Prod x.1 * goldbachS5Cofactor x : ℕ) ∧
      eps * (N : ℝ) / (goldbachC10Prod x.1 : ℝ) <
        (goldbachS5Cofactor x : ℝ) := by
  obtain ⟨hrs, hn, _⟩ := mem_goldbachS5ActualAtoms_iff.mp hx
  have hlo := (goldbachG10DifferenceCarrier_bounds heps hn).2.2
  rw [goldbachS5ActualAtom_factorization hx] at hlo
  have hm : (0 : ℝ) < (goldbachC10Prod x.1 : ℝ) := by
    exact_mod_cast goldbachC9Prod_pos hrs
  refine ⟨hlo, (div_lt_iff₀ hm).mpr ?_⟩
  simpa only [Nat.cast_mul, goldbachC9Prod, goldbachC8Prod,
    goldbachC10Prod, mul_comm] using hlo

theorem goldbachS5LowFirstSwitch_preserves_pair (x : Σ _rs : ℕ × ℕ, ℕ) :
    (goldbachS5Switch x).1 = x.1 := rfl

theorem goldbachS5LowFirstSwitch_mem_positivePrimeAtoms {N : ℕ} {eps : ℝ}
    (hN : 2 ≤ N) (heps : 0 < eps)
    (hcut : (N : ℝ) ^ (2 / 3 : ℝ) ≤ eps * N)
    {x : Σ _rs : ℕ × ℕ, ℕ}
    (hx : x ∈ goldbachS5GoodNonsquareAtoms N eps)
    (hfirst : (x.1.1 : ℝ) < (N : ℝ) ^ (1 / 10 : ℝ)) :
    goldbachS5Switch x ∈ goldbachB9LowPositivePrefixPrimeAtoms N eps := by
  classical
  have ha := (mem_filter.mp (mem_filter.mp hx).1).1
  have hretained := (goldbachS5ActualAtom_retained_epsilon heps ha).2
  obtain ⟨hp, _⟩ := goldbachS5Switch_mem_primeAtoms hN heps hcut hx
  obtain ⟨hmother, hout⟩ := mem_filter.mp hp
  obtain ⟨hrs, hq, hprod⟩ := mem_goldbachB9PlusAtoms_iff.mp hmother
  have hmpos := goldbachC9Prod_pos hrs
  have hmR : (0 : ℝ) < (goldbachC10Prod x.1 : ℝ) := by
    exact_mod_cast hmpos
  apply mem_filter.mpr
  refine ⟨mem_goldbachB9LowPositivePrefixAtoms_iff.mpr ⟨?_, hfirst⟩, hout⟩
  apply mem_goldbachB10Atoms_iff.mpr
  refine ⟨(goldbachC9Pairs_eq_C10Pairs N) ▸ hrs, ?_, hq, hretained, ?_⟩
  · apply mem_range.mpr
    have hle := Nat.le_mul_of_pos_left (goldbachS5Switch x).2 hmpos
    omega
  · apply (lt_div_iff₀ hmR).mpr
    exact_mod_cast (by simpa [goldbachS5Switch, goldbachC9Prod, goldbachC8Prod,
      goldbachC10Prod, mul_comm] using hprod :
        goldbachS5Cofactor x * goldbachC10Prod x.1 < N)

theorem goldbachS5ClosedBelow_le_positivePrefix_sifted {N : ℕ} {eps Z : ℝ}
    (hN : 2 ≤ N) (heps : 0 < eps)
    (hcut : (N : ℝ) ^ (2 / 3 : ℝ) ≤ eps * N) (hZ : 1 ≤ Z) :
    goldbachS5ClosedBelow (goldbachDifferenceCarrier N eps) N
      ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))
      ((N : ℝ) ^ (1 / 10 : ℝ)) ≤
        goldbachB9LowPositivePrefixSiftedCount N eps Z +
        400 * goldbachBadCount (goldbachDifferenceCarrier N eps) N +
        400 * goldbachS5SquareCount N + 400 * (Nat.floor Z : ℤ) := by
  classical
  let G := (goldbachS5GoodNonsquareAtoms N eps).filter
    (fun x => (x.1.1 : ℝ) < (N : ℝ) ^ (1 / 10 : ℝ))
  let P := goldbachB9LowPositivePrefixPrimeAtoms N eps
  let S := goldbachB9LowPositivePrefixSiftedAtoms N eps Z
  let L := (goldbachB9PlusAtoms N).filter
    (fun x => (goldbachB9PlusOutput N x : ℝ) < Z)
  have hsplit : goldbachS5LowFirstActualAtoms N eps ⊆
      G ∪ (goldbachS5BadAtoms N eps ∪ goldbachS5SquareAtoms N eps) := by
    intro x hx
    simp only [goldbachS5LowFirstActualAtoms, mem_filter] at hx
    simp only [G, mem_union, mem_filter, goldbachS5GoodNonsquareAtoms,
      goldbachS5GoodAtoms, goldbachS5BadAtoms, goldbachS5SquareAtoms]
    tauto
  have hcard : (goldbachS5LowFirstActualAtoms N eps).card ≤
      G.card + (goldbachS5BadAtoms N eps).card + (goldbachS5SquareAtoms N eps).card :=
    (card_le_card hsplit).trans ((card_union_le _ _).trans
      (by simpa [Nat.add_assoc] using
        Nat.add_le_add_left (card_union_le (goldbachS5BadAtoms N eps)
          (goldbachS5SquareAtoms N eps)) G.card))
  have hG : G.card ≤ P.card := by
    apply card_le_card_of_injOn goldbachS5Switch
    · intro x hx
      obtain ⟨hx, hfirst⟩ := mem_filter.mp hx
      exact goldbachS5LowFirstSwitch_mem_positivePrimeAtoms hN heps hcut hx hfirst
    · intro x hx y hy hxy
      exact goldbachS5Switch_injOn
        (mem_filter.mp (mem_filter.mp (mem_filter.mp hx).1).1).1
        (mem_filter.mp (mem_filter.mp (mem_filter.mp hy).1).1).1 hxy
  have hPS : P ⊆ S ∪ L := by
    intro x hx
    obtain ⟨hxB, hp⟩ := mem_filter.mp hx
    by_cases hlo : (goldbachPi10Output N x : ℝ) < Z
    · exact mem_union_right _ (mem_filter.mpr
        ⟨goldbachB9LowPositivePrefixAtoms_subset_B9Plus N eps hxB, hlo⟩)
    · apply mem_union_left
      change x ∈ goldbachB9LowPositivePrefixSiftedAtoms N eps Z
      rw [goldbachB9LowPositivePrefixSiftedAtoms_eq_filter]
      apply mem_filter.mpr
      refine ⟨hxB, by simp, ?_⟩
      intro ell hell hd _
      have heq := (Nat.prime_dvd_prime_iff_eq hell hp).mp hd
      simpa [heq] using le_of_not_gt hlo
  have hP : P.card ≤ S.card + L.card :=
    (card_le_card hPS).trans (card_union_le _ _)
  have hbad := goldbachS5BadAtoms_card_le (N := N) heps
  have hsquare := goldbachS5SquareAtoms_card_le (N := N) heps
  have hlow := goldbachB9Plus_low_card_le N hZ
  rw [goldbachS5ClosedBelow_eq_card_lowActualAtoms]
  change ((goldbachS5LowFirstActualAtoms N eps).card : ℤ) ≤
    (S.card : ℤ) + 400 * goldbachBadCount (goldbachDifferenceCarrier N eps) N +
      400 * goldbachS5SquareCount N + 400 * (Nat.floor Z : ℤ)
  dsimp only [L] at hP
  omega

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig