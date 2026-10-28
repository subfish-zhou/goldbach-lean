import MathlibNt.SieveTheory.Switching.SuzukiPrimeSums
import MathlibNt.SieveTheory.LinearSieve.RosserChains

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple

/-- The odd stored-chain mass which remains after Suzuki's terminal prime `q`
is externalized.  Pair depth `k` means stored length `2*k+1`; after restoring
`q`, the full source index is therefore `2*k+2`.  The strict filter is essential:
`q` is not one of the stored primes. -/
noncomputable def lowerSuzukiDiscreteKernel
    (S : BoundingSieve) (D z k q : ℕ) : ℝ :=
  lowerRosserBoundaryChainsFixedPairDepth0Density S.nu D q
    ((suzukiSupportedBelow S z).filter (fun p => q < p)) k

/-- The finite normalized lower layer corresponding to Suzuki's
`V_{2k+2}(D,z)/V(z)`.  The terminal prime is external: its contribution is the
Suzuki atom `ν(q) V(q)/V(z)`, while the odd chain behind it is the kernel. -/
noncomputable def lowerSuzukiNormalizedLayer
    (S : BoundingSieve) (D w z k : ℕ) : ℝ :=
  suzukiPrimeSumNat S w z (lowerSuzukiDiscreteKernel S D z k)


/-- Exact terminal-prime externalization.  This is Suzuki's finite prime sum,
not merely an upper bound or an asymptotic identification. -/
theorem lowerSuzukiNormalizedLayer_eq_primeSum
    (S : BoundingSieve) (D w z k : ℕ) :
    lowerSuzukiNormalizedLayer S D w z k =
      ∑ q ∈ (suzukiSupportedBelow S z).filter (fun q => w ≤ q),
        S.nu q * suzukiSuffixRatio S z q *
          lowerSuzukiDiscreteKernel S D z k q := by
  rfl


/-- The exact carrier left after peeling the two largest stored primes. -/
private theorem lowerSuzuki_residualCarrier
    (S : BoundingSieve) {z q p₁ : ℕ} (hp₁z : p₁ < z) :
    ((suzukiSupportedBelow S z).filter (fun p => q < p)).filter
        (fun p => p < p₁) =
      (suzukiSupportedBelow S p₁).filter (fun p => q < p) := by
  ext p
  simp only [suzukiSupportedBelow, mem_filter]
  constructor
  · rintro ⟨⟨⟨hpS, hpz⟩, hqp⟩, hpp₁⟩
    exact ⟨⟨hpS, hpp₁⟩, hqp⟩
  · rintro ⟨⟨hpS, hpp₁⟩, hqp⟩
    exact ⟨⟨⟨hpS, hpp₁.trans hp₁z⟩, hqp⟩, hpp₁⟩

/-- Exact one-pair recurrence for the discrete kernel.  No analytic assumption
is used.  Notice that the residual cutoff is `p₁`, not `z`; this is the finite
carrier refinement hidden by continuous notation. -/
theorem lowerSuzukiDiscreteKernel_succ
    (S : BoundingSieve) {D z q : ℕ}
    (hq : q ∈ suzukiSupportedBelow S z) (k : ℕ) :
    lowerSuzukiDiscreteKernel S D z (k + 1) q =
      ∑ p₀ ∈ (suzukiSupportedBelow S z).filter (fun p => q < p),
        ∑ p₁ ∈ ((suzukiSupportedBelow S z).filter (fun p => q < p)).filter
            (fun p₁ => p₁ < p₀ ∧ p₀ * p₁ ^ 3 < D),
          S.nu p₀ * S.nu p₁ *
            lowerSuzukiDiscreteKernel S (D ⌈/⌉ (p₀ * p₁)) p₁ k q := by
  classical
  let P := (suzukiSupportedBelow S z).filter (fun p => q < p)
  have hqS : q ∈ S.prodPrimes.primeFactors := (mem_filter.mp hq).1
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hqS
  have hqnot : q ∉ P := by simp [P]
  have hprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors (mem_filter.mp (mem_filter.mp hp).1).1
  have hqmin : ∀ p ∈ P, q ≤ p := by
    intro p hp
    exact (mem_filter.mp hp).2.le
  rw [lowerSuzukiDiscreteKernel]
  rw [lowerRosserBoundaryChainsFixedPairDepth0Density_succ
    S.nu hqnot hqprime hprime hqmin k]
  apply sum_congr rfl
  intro p₀ hp₀
  apply sum_congr rfl
  intro p₁ hp₁
  have hp₁P : p₁ ∈ P := (mem_filter.mp hp₁).1
  have hp₁z : p₁ < z := (mem_filter.mp (mem_filter.mp hp₁P).1).2
  rw [lowerSuzukiDiscreteKernel, lowerSuzuki_residualCarrier S hp₁z]


end MathlibNt.SieveTheory
