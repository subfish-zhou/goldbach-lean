import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLowerDepthFourMass

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open SwitchingPrinciple

private theorem suzukiSupportedBelow_ssubset_of_mem
    {S : BoundingSieve} {z p : ℕ} (hp : p ∈ suzukiSupportedBelow S z) :
    suzukiSupportedBelow S p ⊂ suzukiSupportedBelow S z := by
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro q hq
    simp only [suzukiSupportedBelow, Finset.mem_filter] at hp hq ⊢
    exact ⟨hq.1, hq.2.trans hp.2⟩
  · intro heq
    have hpp : p ∈ suzukiSupportedBelow S p := heq.symm ▸ hp
    exact (Finset.mem_filter.mp hpp).2.false

private theorem suzukiSupportedBelow_card_lt_of_mem
    {S : BoundingSieve} {z p : ℕ} (hp : p ∈ suzukiSupportedBelow S z) :
    (suzukiSupportedBelow S p).card < (suzukiSupportedBelow S z).card :=
  Finset.card_lt_card (suzukiSupportedBelow_ssubset_of_mem hp)

/-- A boundary layer longer than the finite prime support below `z` vanishes.
Each recursive step chooses a strictly smaller prime, so it strictly decreases
that support. -/
theorem lowerRosserBoundaryLayerMass_eq_zero_of_card_lt
    (S : BoundingSieve) (n D z : ℕ)
    (hcard : (suzukiSupportedBelow S z).card < n) :
    lowerRosserBoundaryLayerMass S n D z = 0 := by
  induction n using Nat.strong_induction_on generalizing D z with
  | h n ih =>
      cases n with
      | zero => omega
      | succ n =>
          cases n with
          | zero =>
              have hempty : suzukiSupportedBelow S z = ∅ :=
                Finset.card_eq_zero.mp (by omega)
              simp [lowerRosserBoundaryLayerMass, hempty]
          | succ n =>
              simp only [lowerRosserBoundaryLayerMass]
              apply Finset.sum_eq_zero
              intro p hp
              have hpSupport : p ∈ suzukiSupportedBelow S z := by
                split at hp
                · exact (Finset.mem_filter.mp hp).1
                · exact hp
              have hinner : (suzukiSupportedBelow S p).card < n + 1 := by
                have hstrict := suzukiSupportedBelow_card_lt_of_mem hpSupport
                omega
              rw [ih (n + 1) (by omega) (D ⌈/⌉ p) p hinner, mul_zero]

/-- In particular, every even layer whose depth exceeds the finite support
cardinality is zero. -/
theorem lowerRosserEvenBoundaryLayerMass_eq_zero_of_support_card_lt
    (S : BoundingSieve) (k D z : ℕ)
    (hcard : (suzukiSupportedBelow S z).card < 2 * (k + 1)) :
    lowerRosserEvenBoundaryLayerMass S k D z = 0 := by
  exact lowerRosserBoundaryLayerMass_eq_zero_of_card_lt S _ D z hcard




end MathlibNt.SieveTheory
