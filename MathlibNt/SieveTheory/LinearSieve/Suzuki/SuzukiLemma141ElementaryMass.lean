import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiVnSemanticResolution

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory
open LinearSieve SwitchingPrinciple

noncomputable def suzukiElementaryMass (S : BoundingSieve) (n z : ℕ) : ℝ :=
  ∑ t ∈ (suzukiSupportedBelow S z).powersetCard n,
    ∏ p ∈ t, S.nu p

private theorem nu_nonneg_of_mem_primeFactors (S : BoundingSieve) {p : ℕ}
    (hp : p ∈ S.prodPrimes.primeFactors) : 0 ≤ S.nu p := by
  exact (S.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hp)
    (Nat.mem_primeFactors.mp hp).2.1).le

private theorem elementaryMass_recurrence (S : BoundingSieve) (n z : ℕ) :
    suzukiElementaryMass S (n + 1) z =
      ∑ p ∈ suzukiSupportedBelow S z,
        S.nu p * suzukiElementaryMass S n p := by
  induction z with
  | zero =>
      unfold suzukiElementaryMass
      have hs : suzukiSupportedBelow S 0 = ∅ := by
        ext p
        simp [suzukiSupportedBelow]
      rw [hs, powersetCard_eq_empty.mpr (by simp)]
      simp
  | succ z ih =>
      by_cases hz : z ∈ S.prodPrimes.primeFactors
      · have hs : suzukiSupportedBelow S (z + 1) =
            insert z (suzukiSupportedBelow S z) := by
          ext p
          simp only [suzukiSupportedBelow, mem_filter, mem_insert]
          constructor
          · rintro ⟨hpP, hpz⟩
            rcases Nat.lt_succ_iff.mp hpz with hle
            rcases eq_or_lt_of_le hle with rfl | hlt
            · exact Or.inl rfl
            · exact Or.inr ⟨hpP, hlt⟩
          · rintro (rfl | ⟨hpP, hpz⟩)
            · exact ⟨hz, Nat.lt_succ_self _⟩
            · exact ⟨hpP, hpz.trans (Nat.lt_succ_self z)⟩
        have hnot : z ∉ suzukiSupportedBelow S z := by
          simp [suzukiSupportedBelow]
        unfold suzukiElementaryMass at ih
        unfold suzukiElementaryMass
        rw [hs, powersetCard_succ_insert hnot n]
        rw [sum_union]
        · rw [sum_insert hnot, ih]
          rw [sum_image]
          · have hsum :
                (∑ x ∈ powersetCard n (suzukiSupportedBelow S z),
                  ∏ p ∈ insert z x, S.nu p) =
                S.nu z * (∑ x ∈ powersetCard n (suzukiSupportedBelow S z),
                  ∏ p ∈ x, S.nu p) := by
              rw [Finset.mul_sum]
              apply sum_congr rfl
              intro x hx
              have hzx : z ∉ x := fun hzx =>
                hnot ((mem_powersetCard.mp hx).1 hzx)
              rw [prod_insert hzx]
            rw [hsum]
            ring
          · intro a ha b hb hab
            have hza : z ∉ a := fun hza =>
              hnot ((mem_powersetCard.mp ha).1 hza)
            have hzb : z ∉ b := fun hzb =>
              hnot ((mem_powersetCard.mp hb).1 hzb)
            have h := congrArg (fun t : Finset ℕ => t.erase z) hab
            simpa [hza, hzb] using h
        · rw [disjoint_left]
          intro t htold htnew
          rw [mem_powersetCard] at htold
          rw [mem_image] at htnew
          rcases htnew with ⟨u, hu, rfl⟩
          exact hnot (htold.1 (mem_insert_self z u))
      · have hs : suzukiSupportedBelow S (z + 1) =
            suzukiSupportedBelow S z := by
          ext p
          simp only [suzukiSupportedBelow, mem_filter]
          constructor
          · rintro ⟨hpP, hpz⟩
            have hpne : p ≠ z := fun h => hz (h ▸ hpP)
            exact ⟨hpP, lt_of_le_of_ne (Nat.lt_succ_iff.mp hpz) hpne⟩
          · rintro ⟨hpP, hpz⟩
            exact ⟨hpP, hpz.trans (Nat.lt_succ_self z)⟩
        unfold suzukiElementaryMass at ih ⊢
        rw [hs]
        exact ih

private theorem elementaryMass_nonneg (S : BoundingSieve) (n z : ℕ) :
    0 ≤ suzukiElementaryMass S n z := by
  unfold suzukiElementaryMass
  apply sum_nonneg
  intro t ht
  apply prod_nonneg
  intro p hp
  have htSub := (mem_powersetCard.mp ht).1 hp
  exact nu_nonneg_of_mem_primeFactors S (mem_filter.mp htSub).1

private theorem sourceDiscreteEuler_nonneg (S : BoundingSieve) (z : ℕ) :
    0 ≤ sourceDiscreteEuler S z := by
  unfold sourceDiscreteEuler
  apply prod_nonneg
  intro p hp
  have hpP := (mem_filter.mp hp).1
  have hlt := S.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hpP)
    (Nat.mem_primeFactors.mp hpP).2.1
  linarith

private theorem sourceDiscreteEuler_le_one (S : BoundingSieve) (z : ℕ) :
    sourceDiscreteEuler S z ≤ 1 := by
  unfold sourceDiscreteEuler
  apply prod_le_one
  · intro p hp
    have hpP := (mem_filter.mp hp).1
    have hlt := S.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hpP)
      (Nat.mem_primeFactors.mp hpP).2.1
    linarith
  · intro p hp
    have hnu := nu_nonneg_of_mem_primeFactors S (mem_filter.mp hp).1
    linarith

/-- The literal source recursion is bounded by the elementary symmetric mass on
all supported primes below `z`; source cutoffs are only discarded by
nonnegativity. -/
theorem suzukiSourceV_le_elementaryMass
    (S : BoundingSieve) (n D z : ℕ) :
    suzukiSourceV S n D z ≤ suzukiElementaryMass S n z := by
  induction n using Nat.twoStepInduction generalizing D z with
  | zero =>
      simp [suzukiSourceV, suzukiElementaryMass]
  | one =>
      rw [suzukiSourceV_one, elementaryMass_recurrence S 0 z]
      have hsub :
          (suzukiSupportedBelow S z).filter (fun p => D ≤ p ^ 3) ⊆
            suzukiSupportedBelow S z := filter_subset _ _
      calc
        (∑ p ∈ (suzukiSupportedBelow S z).filter (fun p => D ≤ p ^ 3),
            S.nu p * sourceDiscreteEuler S p) ≤
            ∑ p ∈ (suzukiSupportedBelow S z).filter (fun p => D ≤ p ^ 3),
              S.nu p * suzukiElementaryMass S 0 p := by
                apply sum_le_sum
                intro p hp
                have hpP := (mem_filter.mp (mem_filter.mp hp).1).1
                have hnu := nu_nonneg_of_mem_primeFactors S hpP
                have he := sourceDiscreteEuler_le_one S p
                simpa [suzukiElementaryMass, suzukiSupportedBelow] using
                  (mul_le_mul_of_nonneg_left he hnu)
        _ ≤ ∑ p ∈ suzukiSupportedBelow S z,
              S.nu p * suzukiElementaryMass S 0 p := by
                apply sum_le_sum_of_subset_of_nonneg hsub
                intro p hp _
                exact mul_nonneg
                  (nu_nonneg_of_mem_primeFactors S (mem_filter.mp hp).1)
                  (elementaryMass_nonneg S 0 p)
  | more n ih0 ih1 =>
      rw [suzukiSourceV_succ_of_pos S (n := n + 1) (by omega)]
      rw [elementaryMass_recurrence S (n + 1) z]
      have hsub :
          suzukiSourceOuterCarrier (n + 2) D z S.prodPrimes.primeFactors ⊆
            suzukiSupportedBelow S z := by
        intro p hp
        exact (mem_filter.mp hp).1
      calc
        (∑ p ∈ suzukiSourceOuterCarrier (n + 2) D z S.prodPrimes.primeFactors,
            S.nu p * suzukiSourceV S (n + 1) (D ⌈/⌉ p) p) ≤
            ∑ p ∈ suzukiSourceOuterCarrier (n + 2) D z S.prodPrimes.primeFactors,
              S.nu p * suzukiElementaryMass S (n + 1) p := by
                apply sum_le_sum
                intro p hp
                exact mul_le_mul_of_nonneg_left (ih1 (D := D ⌈/⌉ p) (z := p))
                  (nu_nonneg_of_mem_primeFactors S (mem_filter.mp (mem_filter.mp hp).1).1)
        _ ≤ ∑ p ∈ suzukiSupportedBelow S z,
              S.nu p * suzukiElementaryMass S (n + 1) p := by
                apply sum_le_sum_of_subset_of_nonneg hsub
                intro p hp _
                exact mul_nonneg
                  (nu_nonneg_of_mem_primeFactors S (mem_filter.mp hp).1)
                  (elementaryMass_nonneg S (n + 1) p)

end MathlibNt.SieveTheory
