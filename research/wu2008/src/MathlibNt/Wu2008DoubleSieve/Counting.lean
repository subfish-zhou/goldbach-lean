import MathlibNt.SieveTheory.Chen.Representations
import Mathlib.Tactic.SplitIfs

/-!
# Wu's prime-complement count and the frozen Chen representation count

The positive-complement interpretation of Wu's count allows `Ω 1 = 0`, but
excludes zero before using `Ω`. The actual frozen-release set
`SwitchingPrinciple.chenGoodRepresentations` additionally excludes the unit.
Their difference is exactly the prime `N - 1`, when it is prime.

The separately named totalized count uses Mathlib's arithmetic function
`ArithmeticFunction.cardFactors`, whose value at zero is zero by convention.
It is not a definition of mathematical `Ω(0)`. Its extra boundary point is
exactly `p = N` when `N` is prime. Every identity below holds for all natural
`N`, without an evenness or largeness assumption.
-/

namespace MathlibNt.Wu2008DoubleSieve

open SieveTheory.SwitchingPrinciple
open scoped ArithmeticFunction.Omega Classical

/-- Wu's prime complements with positive complement, including the unit. -/
noncomputable def wuPrimeComplements (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter
    (fun p => p.Prime ∧ 0 < N - p ∧ Ω (N - p) ≤ 2)

/-- A literal use of the totalized arithmetic function, not mathematical `Ω(0)`. -/
noncomputable def totalizedOmegaPrimeComplements (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter
    (fun p => p.Prime ∧ Ω (N - p) ≤ 2)

theorem mem_wuPrimeComplements {N p : ℕ} :
    p ∈ wuPrimeComplements N ↔
      p ≤ N ∧ p.Prime ∧ 0 < N - p ∧ Ω (N - p) ≤ 2 := by
  simp only [wuPrimeComplements, Finset.mem_filter, Finset.mem_range,
    Nat.lt_succ_iff]


theorem mem_releaseGoodRepresentations {N p : ℕ} :
    p ∈ chenGoodRepresentations N ↔
      p < N ∧ p.Prime ∧ 2 ≤ N - p ∧ Ω (N - p) ≤ 2 := by
  rw [chenGoodRepresentations, Finset.mem_filter, Finset.mem_range]
  change (p < N ∧ p.Prime ∧ 2 ≤ N - p ∧ (N - p ≠ 0 ∧ Ω (N - p) ≤ 2)) ↔ _
  constructor
  · rintro ⟨hpN, hp, htwo, _, hΩ⟩
    exact ⟨hpN, hp, htwo, hΩ⟩
  · rintro ⟨hpN, hp, htwo, hΩ⟩
    exact ⟨hpN, hp, htwo, by omega, hΩ⟩

/-- Exact set-level unit exception, including all small natural numbers. -/
theorem wuPrimeComplements_eq_release_union_unit (N : ℕ) :
    wuPrimeComplements N =
      chenGoodRepresentations N ∪
        (if (N - 1).Prime then {N - 1} else ∅) := by
  classical
  ext p
  rw [mem_wuPrimeComplements, Finset.mem_union, mem_releaseGoodRepresentations]
  constructor
  · rintro ⟨hpN, hp, hpos, hΩ⟩
    by_cases hunit : N - p = 1
    · have hpunit : p = N - 1 := by omega
      right
      simp [← hpunit, hp]
    · exact Or.inl ⟨by omega, hp, by omega, hΩ⟩
  · rintro (⟨hpN, hp, htwo, hΩ⟩ | hunit)
    · exact ⟨by omega, hp, by omega, hΩ⟩
    · split_ifs at hunit with hprime
      · have hpunit : p = N - 1 := Finset.mem_singleton.mp hunit
        have hN : 3 ≤ N := by have := hprime.two_le; omega
        have hsub : N - p = 1 := by omega
        exact ⟨by omega, hpunit ▸ hprime, by omega, by simp [hsub]⟩
      · simp at hunit

theorem release_disjoint_unit (N : ℕ) :
    Disjoint (chenGoodRepresentations N)
      (if (N - 1).Prime then {N - 1} else ∅) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hp hunit
  have hp' := mem_releaseGoodRepresentations.mp hp
  split_ifs at hunit with hprime
  · have hpunit : p = N - 1 := Finset.mem_singleton.mp hunit
    omega
  · simp at hunit

/-- The genuine released count differs from Wu's positive count by exactly
one if `N - 1` is prime, and by zero otherwise. -/
theorem wuPrimeComplements_card_eq_release (N : ℕ) :
    (wuPrimeComplements N).card =
      (chenGoodRepresentations N).card + if (N - 1).Prime then 1 else 0 := by
  classical
  rw [wuPrimeComplements_eq_release_union_unit,
    Finset.card_union_of_disjoint (release_disjoint_unit N)]
  split_ifs <;> simp


theorem mem_totalizedOmegaPrimeComplements {N p : ℕ} :
    p ∈ totalizedOmegaPrimeComplements N ↔
      p ≤ N ∧ p.Prime ∧ Ω (N - p) ≤ 2 := by
  simp only [totalizedOmegaPrimeComplements, Finset.mem_filter, Finset.mem_range,
    Nat.lt_succ_iff]

/-- The zero-complement artefact of the totalized arithmetic function is
exactly `p = N`, and occurs exactly when `N` is prime. -/
theorem totalizedOmegaPrimeComplements_eq_wu_union_zero (N : ℕ) :
    totalizedOmegaPrimeComplements N =
      wuPrimeComplements N ∪ (if N.Prime then {N} else ∅) := by
  classical
  ext p
  rw [mem_totalizedOmegaPrimeComplements, Finset.mem_union, mem_wuPrimeComplements]
  constructor
  · rintro ⟨hpN, hp, hΩ⟩
    by_cases hzero : p = N
    · right
      subst p
      simp [hp]
    · exact Or.inl ⟨hpN, hp, by omega, hΩ⟩
  · rintro (⟨hpN, hp, _, hΩ⟩ | hzero)
    · exact ⟨hpN, hp, hΩ⟩
    · split_ifs at hzero with hprime
      · have hpzero : p = N := Finset.mem_singleton.mp hzero
        subst p
        exact ⟨le_rfl, hprime, by simp⟩
      · simp at hzero

theorem wu_disjoint_zero (N : ℕ) :
    Disjoint (wuPrimeComplements N) (if N.Prime then {N} else ∅) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hp hzero
  have hp' := mem_wuPrimeComplements.mp hp
  split_ifs at hzero with hprime
  · have hpzero : p = N := Finset.mem_singleton.mp hzero
    omega
  · simp at hzero

theorem totalizedOmegaPrimeComplements_card_eq_wu (N : ℕ) :
    (totalizedOmegaPrimeComplements N).card =
      (wuPrimeComplements N).card + if N.Prime then 1 else 0 := by
  classical
  rw [totalizedOmegaPrimeComplements_eq_wu_union_zero,
    Finset.card_union_of_disjoint (wu_disjoint_zero N)]
  split_ifs <;> simp



theorem wuPrimeComplements_eq_empty_of_le_two {N : ℕ} (hN : N ≤ 2) :
    wuPrimeComplements N = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨_, hp, hpos, _⟩ := mem_wuPrimeComplements.mp hp
  have := hp.two_le
  omega



end MathlibNt.Wu2008DoubleSieve
