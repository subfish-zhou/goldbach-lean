import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma141ElementaryMass

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open SwitchingPrinciple

private theorem two_terms_le_add_pow (A w : ℝ) (n : ℕ)
    (hA : 0 ≤ A) (hw : 0 ≤ w) :
    A ^ (n + 1) + (n + 1 : ℝ) * w * A ^ n ≤ (A + w) ^ (n + 1) := by
  rw [add_pow]
  let u : Finset ℕ := {n, n + 1}
  have hu : u ⊆ range (n + 1 + 1) := by
    intro k hk
    simp only [u, mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl <;> simp
  have hnonneg : ∀ k ∈ range (n + 1 + 1), k ∉ u →
      0 ≤ A ^ k * w ^ (n + 1 - k) * (n + 1).choose k := by
    intro k hk hku
    positivity
  calc
    A ^ (n + 1) + (n + 1 : ℝ) * w * A ^ n =
        ∑ k ∈ u, A ^ k * w ^ (n + 1 - k) * (n + 1).choose k := by
          simp [u, Nat.choose_self]
          ring
    _ ≤ ∑ k ∈ range (n + 1 + 1),
        A ^ k * w ^ (n + 1 - k) * (n + 1).choose k :=
      sum_le_sum_of_subset_of_nonneg hu hnonneg

private theorem elementary_factorial_mul_le_pow
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℝ)
    (hf : ∀ x ∈ s, 0 ≤ f x) (n : ℕ) :
    (n.factorial : ℝ) * (∑ t ∈ s.powersetCard n, ∏ x ∈ t, f x) ≤
      (∑ x ∈ s, f x) ^ n := by
  induction s using Finset.induction generalizing n with
  | empty =>
      cases n with
      | zero => simp
      | succ n =>
          rw [powersetCard_eq_empty.mpr (by simp)]
          simp
  | @insert a s ha ih =>
      cases n with
      | zero => simp
      | succ n =>
          have hfa : 0 ≤ f a := hf a (mem_insert_self a s)
          have hfs : ∀ x ∈ s, 0 ≤ f x := by
            intro x hx
            exact hf x (mem_insert_of_mem hx)
          have hrec :
              (∑ t ∈ (insert a s).powersetCard (n + 1), ∏ x ∈ t, f x) =
                (∑ t ∈ s.powersetCard (n + 1), ∏ x ∈ t, f x) +
                  f a * (∑ t ∈ s.powersetCard n, ∏ x ∈ t, f x) := by
            rw [powersetCard_succ_insert ha n, sum_union]
            · rw [sum_image]
              · congr 1
                rw [mul_sum]
                apply sum_congr rfl
                intro t ht
                have hat : a ∉ t := fun hat => ha ((mem_powersetCard.mp ht).1 hat)
                rw [prod_insert hat]
              · intro u hu v hv huv
                have hau : a ∉ u := fun hau => ha ((mem_powersetCard.mp hu).1 hau)
                have hav : a ∉ v := fun hav => ha ((mem_powersetCard.mp hv).1 hav)
                have h := congrArg (fun t : Finset α => t.erase a) huv
                simpa [hau, hav] using h
            · rw [disjoint_left]
              intro t htold htnew
              rw [mem_powersetCard] at htold
              rw [mem_image] at htnew
              rcases htnew with ⟨u, hu, rfl⟩
              exact ha (htold.1 (mem_insert_self a u))
          rw [hrec, sum_insert ha]
          have ih_succ := ih hfs (n + 1)
          have ih_n := ih hfs n
          have hfac : ((n + 1).factorial : ℝ) = (n + 1 : ℝ) * (n.factorial : ℝ) := by
            simp [Nat.factorial_succ]
          have hnonneg_fac : 0 ≤ (n.factorial : ℝ) := by positivity
          have hscaled_n :
              ((n + 1).factorial : ℝ) * f a *
                  (∑ t ∈ s.powersetCard n, ∏ x ∈ t, f x) ≤
                (n + 1 : ℝ) * f a * (∑ x ∈ s, f x) ^ n := by
            rw [hfac]
            calc
              (n + 1 : ℝ) * (n.factorial : ℝ) * f a *
                    (∑ t ∈ s.powersetCard n, ∏ x ∈ t, f x) =
                  ((n + 1 : ℝ) * f a) *
                    ((n.factorial : ℝ) *
                      (∑ t ∈ s.powersetCard n, ∏ x ∈ t, f x)) := by ring
              _ ≤ ((n + 1 : ℝ) * f a) * (∑ x ∈ s, f x) ^ n :=
                mul_le_mul_of_nonneg_left ih_n (mul_nonneg (by positivity) hfa)
              _ = (n + 1 : ℝ) * f a * (∑ x ∈ s, f x) ^ n := by ring
          have hsum_nonneg : 0 ≤ ∑ x ∈ s, f x := sum_nonneg hfs
          have hbin := two_terms_le_add_pow (∑ x ∈ s, f x) (f a) n hsum_nonneg hfa
          calc
            ((n + 1).factorial : ℝ) *
                ((∑ t ∈ s.powersetCard (n + 1), ∏ x ∈ t, f x) +
                  f a * ∑ t ∈ s.powersetCard n, ∏ x ∈ t, f x) =
                ((n + 1).factorial : ℝ) *
                    (∑ t ∈ s.powersetCard (n + 1), ∏ x ∈ t, f x) +
                  ((n + 1).factorial : ℝ) * f a *
                    (∑ t ∈ s.powersetCard n, ∏ x ∈ t, f x) := by ring
            _ ≤ (∑ x ∈ s, f x) ^ (n + 1) +
                  (n + 1 : ℝ) * f a * (∑ x ∈ s, f x) ^ n :=
              add_le_add ih_succ hscaled_n
            _ ≤ ((∑ x ∈ s, f x) + f a) ^ (n + 1) := hbin
            _ = (f a + ∑ x ∈ s, f x) ^ (n + 1) := by rw [add_comm]

/-- The elementary symmetric mass is bounded by the corresponding power sum,
with the exact factorial denominator. -/
theorem suzukiElementaryMass_le_pow_div_factorial
    (S : BoundingSieve) (n z : ℕ) :
    suzukiElementaryMass S n z ≤
      (∑ p ∈ suzukiSupportedBelow S z, S.nu p) ^ n / n.factorial := by
  have hnu : ∀ p ∈ suzukiSupportedBelow S z, 0 ≤ S.nu p := by
    intro p hp
    have hpP := (mem_filter.mp hp).1
    exact (S.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hpP)
      (Nat.mem_primeFactors.mp hpP).2.1).le
  have hmul := elementary_factorial_mul_le_pow
    (suzukiSupportedBelow S z) S.nu hnu n
  have hfac : (0 : ℝ) < n.factorial := by positivity
  unfold suzukiElementaryMass
  apply (le_div_iff₀ hfac).2
  simpa [mul_comm] using hmul

/-- Lemma 14.1 factorial bound, combining source domination by the elementary
symmetric mass with its ordered-tuple/factorial estimate. -/
theorem suzukiSourceV_le_pow_div_factorial
    (S : BoundingSieve) (n D z : ℕ) :
    suzukiSourceV S n D z ≤
      (∑ p ∈ suzukiSupportedBelow S z, S.nu p) ^ n / n.factorial :=
  (suzukiSourceV_le_elementaryMass S n D z).trans
    (suzukiElementaryMass_le_pow_div_factorial S n z)


end MathlibNt.SieveTheory
