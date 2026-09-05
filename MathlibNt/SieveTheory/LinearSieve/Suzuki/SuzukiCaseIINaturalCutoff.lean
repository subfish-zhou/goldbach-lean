import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiDiscreteParityRecurrence

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple

/-- Exact natural-cutoff identity for the total Section-14 extension.

The carrier hypothesis says precisely that every summand introduced when the
outer cutoff is enlarged from `y` to `z` has zero recursive tail.  This is the
support condition needed by the total extension; it must not be replaced merely
by the cubic relation defining `y`. -/
theorem section14ExtendedT_naturalCutoff_of_odd
    (S : BoundingSieve) {N D y z : ℕ} (hN : Odd N)
    (hyz : y ≤ z) (hyD : y ^ 3 ≤ D)
    (houter : ∀ p ∈ suzukiSupportedBelow S z, y ≤ p →
      section14ExtendedT S (N - 1) (D ⌈/⌉ p) p = 0) :
    section14ExtendedT S N D z =
      section14ExtendedT S N D y + section14ExtendedV S 1 D z := by
  classical
  have hN1 : 1 ≤ N := by
    obtain ⟨k, rfl⟩ := hN
    omega
  have hsub : suzukiSupportedBelow S y ⊆ suzukiSupportedBelow S z := by
    intro p hp
    simp only [suzukiSupportedBelow, mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.trans_le hyz⟩
  have hsum :
      (∑ p ∈ suzukiSupportedBelow S z,
          S.nu p * section14ExtendedT S (N - 1) (D ⌈/⌉ p) p) =
        ∑ p ∈ suzukiSupportedBelow S y,
          S.nu p * section14ExtendedT S (N - 1) (D ⌈/⌉ p) p := by
    symm
    apply Finset.sum_subset hsub
    intro p hpz hpy
    have hpP : p ∈ S.prodPrimes.primeFactors :=
      (Finset.mem_filter.mp hpz).1
    have hpnot : ¬ p < y := by
      intro hpy'
      exact hpy (Finset.mem_filter.mpr ⟨hpP, hpy'⟩)
    have hyp : y ≤ p := Nat.le_of_not_gt hpnot
    rw [houter p hpz hyp, mul_zero]
  rw [section14ExtendedT_eq_one_add_recurrence_of_odd S hN hN1,
    section14ExtendedT_eq_one_add_recurrence_of_odd S hN hN1,
    section14ExtendedV_one_eq_zero_of_cube_le S hyD, zero_add, hsum]
  ring


end MathlibNt.SieveTheory
