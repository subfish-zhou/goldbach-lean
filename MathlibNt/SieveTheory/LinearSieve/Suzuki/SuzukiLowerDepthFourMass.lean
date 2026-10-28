import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ActualRecurrence
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection14LegalDomainBridge

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open SwitchingPrinciple


private theorem supportedBelow_pos {S : BoundingSieve} {z p : ℕ}
    (hp : p ∈ suzukiSupportedBelow S z) : 0 < p := by
  have hpP : p ∈ S.prodPrimes.primeFactors :=
    (Finset.mem_filter.mp hp).1
  exact (Nat.prime_of_mem_primeFactors hpP).pos


/-- At every odd outer depth, the source lower cutoff is redundant: whenever
it fails, the remaining even layer vanishes.  The odd cubic upper cutoff is the
only active outer condition. -/
theorem suzukiSourceV_odd_succ_eq_upper_only
    (S : BoundingSieve) {n D z : ℕ} (hn : 0 < n) (hodd : Odd (n + 1)) :
    suzukiSourceV S (n + 1) D z =
      ∑ p ∈ (suzukiSupportedBelow S z).filter (fun p => p ^ 3 < D),
        S.nu p * suzukiSourceV S n (D ⌈/⌉ p) p := by
  rw [suzukiSourceV_succ_of_pos S hn]
  apply Finset.sum_subset
  · intro p hp
    simp only [suzukiSourceOuterCarrier, Finset.mem_filter] at hp ⊢
    refine ⟨?_, hp.2.2 hodd⟩
    simpa [suzukiSupportedBelow] using hp.1
  · intro p hpUpper hpNotCarrier
    have hpSupport : p ∈ suzukiSupportedBelow S z :=
      (Finset.mem_filter.mp hpUpper).1
    have hpPos := supportedBelow_pos hpSupport
    have hUpper : p ^ 3 < D := (Finset.mem_filter.mp hpUpper).2
    have hLowerFails : ¬ D ≤ p ^ ((n + 1) + 2) := by
      intro hLower
      apply hpNotCarrier
      simp only [suzukiSourceOuterCarrier, Finset.mem_filter]
      exact ⟨Finset.mem_filter.mp hpSupport, hLower, fun _ => hUpper⟩
    have hvanish : p ^ (n + 2) ≤ D ⌈/⌉ p := by
      by_contra h
      have hceil : D ⌈/⌉ p < p ^ (n + 2) := Nat.lt_of_not_ge h
      have hmul : p * (D ⌈/⌉ p) < p * p ^ (n + 2) :=
        (Nat.mul_lt_mul_left hpPos).2 hceil
      have hDceil : D ≤ p * (D ⌈/⌉ p) :=
        (ceilDiv_le_iff_le_mul hpPos).1 le_rfl
      have hpowsucc : p * p ^ (n + 2) = p ^ ((n + 1) + 2) := by
        calc
          p * p ^ (n + 2) = p ^ (n + 2) * p := Nat.mul_comm _ _
          _ = p ^ ((n + 2) + 1) := (pow_succ _ _).symm
          _ = p ^ ((n + 1) + 2) := rfl
      rw [hpowsucc] at hmul
      exact hLowerFails (hDceil.trans hmul.le)
    rw [suzukiSourceV_eq_zero_of_pow_le S hn hvanish, mul_zero]


/-- The boundary layer at arbitrary recursion depth.  Depth one is the terminal
odd crossing.  Every later odd layer records the active cubic upper test, while
every even layer only extends the decreasing prime chain.  Thus a layer carries
exactly the alternating-prefix invariant visible at depths four and six. -/
noncomputable def lowerRosserBoundaryLayerMass (S : BoundingSieve) :
    ℕ → ℕ → ℕ → ℝ
  | 0, _, _ => 0
  | 1, D, z =>
      ∑ q ∈ (suzukiSupportedBelow S z).filter (fun q => D ≤ q ^ 3),
        S.nu q * sourceDiscreteEuler S q
  | n + 2, D, z =>
      ∑ p ∈ if Odd (n + 2) then
          (suzukiSupportedBelow S z).filter (fun p => p ^ 3 < D)
        else suzukiSupportedBelow S z,
        S.nu p * lowerRosserBoundaryLayerMass S (n + 1) (D ⌈/⌉ p) p

/-- General Suzuki/lower-Rosser layer correspondence.  The inductive invariant
is that the current divided level is retained literally; odd outer depths add
`p³ < D`, even outer depths add no test, and depth one closes with `D ≤ q³`. -/
theorem suzukiSourceV_eq_lowerRosserBoundaryLayerMass
    (S : BoundingSieve) (n D z : ℕ) (hn : 0 < n) :
    suzukiSourceV S n D z = lowerRosserBoundaryLayerMass S n D z := by
  induction n using Nat.strong_induction_on generalizing D z with
  | h n ih =>
      cases n with
      | zero => omega
      | succ n =>
          cases n with
          | zero => simp [lowerRosserBoundaryLayerMass, suzukiSourceV_one]
          | succ n =>
              have hstep (prime : ℕ) :
                  suzukiSourceV S (n + 1) (D ⌈/⌉ prime) prime =
                    lowerRosserBoundaryLayerMass S (n + 1) (D ⌈/⌉ prime) prime :=
                ih (n + 1) (by omega) (D ⌈/⌉ prime) prime (by omega)
              by_cases hodd : Odd (n + 2)
              · rw [suzukiSourceV_odd_succ_eq_upper_only S (by omega) hodd]
                simp only [lowerRosserBoundaryLayerMass, if_pos hodd, hstep]
              · rw [suzukiSourceV_succ_eq_unrestricted S (by omega)
                    (fun h => (hodd h).elim)]
                simp only [lowerRosserBoundaryLayerMass, if_neg hodd, hstep]

/-- The `m`-th (one-indexed mathematically, zero-indexed here) even boundary
layer has Suzuki depth `2(m+1)`. -/
noncomputable def lowerRosserEvenBoundaryLayerMass
    (S : BoundingSieve) (m D z : ℕ) : ℝ :=
  lowerRosserBoundaryLayerMass S (2 * (m + 1)) D z

/-- Every positive even Suzuki layer is the corresponding lower-Rosser boundary
layer. -/
theorem suzukiSourceV_even_eq_lowerRosserEvenBoundaryLayerMass
    (S : BoundingSieve) (m D z : ℕ) :
    suzukiSourceV S (2 * (m + 1)) D z =
      lowerRosserEvenBoundaryLayerMass S m D z := by
  unfold lowerRosserEvenBoundaryLayerMass
  exact suzukiSourceV_eq_lowerRosserBoundaryLayerMass S _ D z (by omega)


/-- At arbitrary even truncation, `suzukiActualT` is exactly the finite sum of
all lower-Rosser boundary layers through depth `2m`. -/
theorem suzukiActualT_even_eq_sum_lowerRosserEvenBoundaryLayerMass
    (S : BoundingSieve) (m D z : ℕ) :
    suzukiActualT S (2 * m) D z =
      ∑ k ∈ Finset.range m, lowerRosserEvenBoundaryLayerMass S k D z := by
  induction m with
  | zero => simp [suzukiActualT]
  | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 2 by omega,
        suzukiActualT_add_two,
        show 2 * m + 2 = 2 * (m + 1) by omega,
        suzukiSourceV_even_eq_lowerRosserEvenBoundaryLayerMass,
        ih]
      simp [Finset.sum_range_succ, add_comm]


end MathlibNt.SieveTheory
