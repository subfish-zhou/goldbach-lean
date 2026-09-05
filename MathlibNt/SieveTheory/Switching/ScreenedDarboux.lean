import MathlibNt.SieveTheory.Switching.ResidualComparison

/-!
# Screened Darboux comparisons for peeled prime pairs

Common fixed-depth meshes compare discrete peeled-pair sums with designated
corner Darboux sums and continuous inner integrals, uniformly on positive screens.

All declarations retain the `MathlibNt.SieveTheory.SwitchingPrinciple` namespace.
-/

open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta

set_option maxHeartbeats 6000000

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open Real Finset
open MeasureTheory intervalIntegral

open scoped Classical
open scoped Asymptotics

namespace Internal
end Internal

open Internal

/-- A common fixed-depth mesh turns every finite peeled-pair sum into its
designated-corner Darboux sum.  The continuity loss is paid once through the
two-prime mass bound, rather than once for each pair of primes. -/
theorem
    exists_sum_pair_mul_upperRosserBoundaryMassAux_succ_le_meshCorners_add
    (k : ℕ) {s₀ s₁ c ε : ℝ} (hc : 0 < c) (hc1 : c < 1) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m, N ≤ m →
      ∀ {S : BoundingSieve} {K z s a : ℝ} {D : ℕ} {P : Finset ℕ}
          (h : Fin (m + 1)) (cell : ℕ → Fin (m + 1)),
        s ∈ Set.Icc s₀ s₁ →
        a ∈ Set.Icc (upperRosserFixedDepthMeshLeft c m h)
          (upperRosserFixedDepthMeshRight c m h) →
        HasDimensionOneLocalProductBound S K →
        1 < z → 2 ≤ z ^ c →
        P ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ P, (p : ℝ) ≤ z) →
        (∀ p ∈ P, c ≤ Real.log p / Real.log z) →
        (∀ p ∈ P, Real.log p / Real.log z ∈
          Set.Icc (upperRosserFixedDepthMeshLeft c m (cell p))
            (upperRosserFixedDepthMeshRight c m (cell p))) →
        ∑ p₀ ∈ P,
            ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
              (S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) *
                LinearSieve.upperRosserBoundaryMassAux (k + 1)
                  (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
                  a (Real.log p₁ / Real.log z) ≤
          (∑ p₀ ∈ P,
            ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
              (S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) *
                LinearSieve.upperRosserBoundaryMassAux (k + 1)
                  (s - upperRosserFixedDepthMeshRight c m (cell p₀) -
                    upperRosserFixedDepthMeshRight c m (cell p₁))
                  (upperRosserFixedDepthMeshLeft c m h)
                  (upperRosserFixedDepthMeshRight c m (cell p₁))) +
            ε * (Real.log (z + 1) / Real.log (z ^ c) *
              (1 + K / Real.log (z ^ c)) - 1) ^ 2 := by
  obtain ⟨N, hN⟩ :=
    exists_upperRosserFixedDepthMesh_mass_majorant_succ_uniform_cutoffs
      k (s₀ := s₀) (s₁ := s₁) hc hc1 hε
  refine ⟨N, ?_⟩
  intro m hm S K z s a D P h cell hs ha hlocal hz hzc hP hcut hscreen hcell
  have hcorner : ∀ p₀ ∈ P,
      ∀ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
        LinearSieve.upperRosserBoundaryMassAux (k + 1)
            (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
            a (Real.log p₁ / Real.log z) ≤
          LinearSieve.upperRosserBoundaryMassAux (k + 1)
            (s - upperRosserFixedDepthMeshRight c m (cell p₀) -
              upperRosserFixedDepthMeshRight c m (cell p₁))
            (upperRosserFixedDepthMeshLeft c m h)
            (upperRosserFixedDepthMeshRight c m (cell p₁)) + ε := by
    intro p₀ hp₀ p₁ hp₁
    exact hN m hm s hs h (cell p₁) (cell p₀) a
      (Real.log p₀ / Real.log z) (Real.log p₁ / Real.log z) ha
      (hcell p₀ hp₀) (hcell p₁ (Finset.mem_filter.mp hp₁).1)
  have hsum :
      (∑ p₀ ∈ P,
        ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
          (S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) *
            LinearSieve.upperRosserBoundaryMassAux (k + 1)
              (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
              a (Real.log p₁ / Real.log z)) ≤
        ∑ p₀ ∈ P,
          ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
            (S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) *
              (LinearSieve.upperRosserBoundaryMassAux (k + 1)
                (s - upperRosserFixedDepthMeshRight c m (cell p₀) -
                  upperRosserFixedDepthMeshRight c m (cell p₁))
                (upperRosserFixedDepthMeshLeft c m h)
                (upperRosserFixedDepthMeshRight c m (cell p₁)) + ε) := by
    apply Finset.sum_le_sum
    intro p₀ hp₀
    apply Finset.sum_le_sum
    intro p₁ hp₁
    apply mul_le_mul_of_nonneg_left (hcorner p₀ hp₀ p₁ hp₁)
    exact mul_nonneg
      (nu_div_one_sub_nonneg_of_mem (hP hp₀))
      (nu_div_one_sub_nonneg_of_mem (hP (Finset.mem_filter.mp hp₁).1))
  have herr :=
    sum_pair_mul_residual_error_le_of_uniform (D := D) (fun _ _ => ε)
      hlocal hz hc1.le hzc hε.le hP hcut hscreen
      (by
        intro p₀ hp₀ p₁ hp₁
        exact ⟨hε.le, le_rfl⟩)
  calc
    ∑ p₀ ∈ P,
        ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
          (S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) *
            LinearSieve.upperRosserBoundaryMassAux (k + 1)
              (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
              a (Real.log p₁ / Real.log z) ≤
        ∑ p₀ ∈ P,
          ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
            (S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) *
              (LinearSieve.upperRosserBoundaryMassAux (k + 1)
                (s - upperRosserFixedDepthMeshRight c m (cell p₀) -
                  upperRosserFixedDepthMeshRight c m (cell p₁))
                (upperRosserFixedDepthMeshLeft c m h)
                (upperRosserFixedDepthMeshRight c m (cell p₁)) + ε) := hsum
    _ = (∑ p₀ ∈ P,
          ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
            (S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) *
              LinearSieve.upperRosserBoundaryMassAux (k + 1)
                (s - upperRosserFixedDepthMeshRight c m (cell p₀) -
                  upperRosserFixedDepthMeshRight c m (cell p₁))
                (upperRosserFixedDepthMeshLeft c m h)
                (upperRosserFixedDepthMeshRight c m (cell p₁))) +
          ∑ p₀ ∈ P,
            ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
              (S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) * ε := by
      simp_rw [mul_add, Finset.sum_add_distrib]
    _ ≤ (∑ p₀ ∈ P,
          ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
            (S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) *
              LinearSieve.upperRosserBoundaryMassAux (k + 1)
                (s - upperRosserFixedDepthMeshRight c m (cell p₀) -
                  upperRosserFixedDepthMeshRight c m (cell p₁))
                (upperRosserFixedDepthMeshLeft c m h)
                (upperRosserFixedDepthMeshRight c m (cell p₁))) +
          ε * (Real.log (z + 1) / Real.log (z ^ c) *
            (1 + K / Real.log (z ^ c)) - 1) ^ 2 := by
      exact add_le_add_right herr _

/-- Exact pair-recursion bound for a fixed distinguished prime, conditional on
a residual comparison that preserves ambient support and the inherited upper
face.  This does not prove the residual comparison at successor depth: it
substitutes the comparison after each peeled pair and explicitly aggregates its
uniform pointwise error through the two prime sums. -/
theorem
    upperRosserBoundaryChainsFixedDepthDensity_succ_le_residualBoundaryMassAux_add_screened
    (k : ℕ) {S : BoundingSieve} {K z c c₀ Δ s ε s₁ : ℝ}
    {q : ℕ} {P : Finset ℕ}
    (hcomparison :
      UpperRosserBoundaryScreenedResidualComparison S z q k ε c₀ s₁)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hz : 1 < z) (hc1 : c ≤ 1) (hzc : 2 ≤ z ^ c) (hε : 0 ≤ ε)
    (hΔ : 0 < Δ) (hs : s = Real.log Δ / Real.log z) (hsUpper : s ≤ s₁)
    (hqprime : q.Prime) (hqs : q ∉ P)
    (hP : P ⊆ S.prodPrimes.primeFactors)
    (hqmin : ∀ p ∈ P, q ≤ p)
    (hcut : ∀ p ∈ P, (p : ℝ) ≤ z)
    (hscreen : ∀ p ∈ P, c ≤ Real.log p / Real.log z)
    (hqscreen : c₀ ≤ Real.log q / Real.log z) :
    LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
        (fun p => S.nu p / (1 - S.nu p))
        (Nat.floor Δ + 1) q P (k + 1) ≤
      (∑ p₀ ∈ P,
        ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
          (S.nu p₀ / (1 - S.nu p₀)) *
            (S.nu p₁ / (1 - S.nu p₁)) *
              LinearSieve.upperRosserBoundaryMassAux k
                (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
                (Real.log q / Real.log z) (Real.log p₁ / Real.log z)) +
        ε * (Real.log (z + 1) / Real.log (z ^ c) *
          (1 + K / Real.log (z ^ c)) - 1) ^ 2 := by
  have hprime : ∀ p ∈ P, p.Prime :=
    fun p hp => Nat.prime_of_mem_primeFactors (hP hp)
  rw [LinearSieve.upperRosserBoundaryChainsFixedDepthDensity_succ
    (fun p => S.nu p / (1 - S.nu p)) hqs hqprime hprime hqmin k]
  calc
    ∑ p₀ ∈ P,
        ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
          (S.nu p₀ / (1 - S.nu p₀)) *
            (S.nu p₁ / (1 - S.nu p₁)) *
              LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
                (fun p => S.nu p / (1 - S.nu p))
                ((Nat.floor Δ + 1) ⌈/⌉ (p₀ * p₁)) q
                (P.filter (fun p => p < p₁)) k ≤
        ∑ p₀ ∈ P,
          ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
            (S.nu p₀ / (1 - S.nu p₀)) *
              (S.nu p₁ / (1 - S.nu p₁)) *
                (LinearSieve.upperRosserBoundaryMassAux k
                    (s - Real.log p₀ / Real.log z -
                      Real.log p₁ / Real.log z)
                    (Real.log q / Real.log z)
                    (Real.log p₁ / Real.log z) + ε) := by
      apply Finset.sum_le_sum
      intro p₀ hp₀
      apply Finset.sum_le_sum
      intro p₁ hp₁
      have hp₁' := Finset.mem_filter.mp hp₁
      apply mul_le_mul_of_nonneg_left
        (hcomparison.ceilDiv hz hΔ hs hsUpper hqprime
          (hprime p₀ hp₀) (hprime p₁ hp₁'.1) hp₁'.2.1 hp₁'.2.2
          (hcut p₁ hp₁'.1)
          (fun p hp => hP (Finset.mem_filter.mp hp).1)
          (by simp [hqs])
          (fun p hp => hprime p (Finset.mem_filter.mp hp).1)
          (fun p hp => hqmin p (Finset.mem_filter.mp hp).1)
          (fun p hp => (Finset.mem_filter.mp hp).2) hqscreen)
      exact mul_nonneg
        (nu_div_one_sub_nonneg_of_mem (hP hp₀))
        (nu_div_one_sub_nonneg_of_mem (hP hp₁'.1))
    _ = (∑ p₀ ∈ P,
          ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
            (S.nu p₀ / (1 - S.nu p₀)) *
              (S.nu p₁ / (1 - S.nu p₁)) *
                LinearSieve.upperRosserBoundaryMassAux k
                  (s - Real.log p₀ / Real.log z -
                    Real.log p₁ / Real.log z)
                  (Real.log q / Real.log z)
                  (Real.log p₁ / Real.log z)) +
          ∑ p₀ ∈ P,
            ∑ p₁ ∈ P.filter
                (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
              (S.nu p₀ / (1 - S.nu p₀)) *
                (S.nu p₁ / (1 - S.nu p₁)) * ε := by
      simp_rw [mul_add, Finset.sum_add_distrib]
    _ ≤ (∑ p₀ ∈ P,
          ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
            (S.nu p₀ / (1 - S.nu p₀)) *
              (S.nu p₁ / (1 - S.nu p₁)) *
                LinearSieve.upperRosserBoundaryMassAux k
                  (s - Real.log p₀ / Real.log z -
                    Real.log p₁ / Real.log z)
                  (Real.log q / Real.log z)
                  (Real.log p₁ / Real.log z)) +
          ε * (Real.log (z + 1) / Real.log (z ^ c) *
            (1 + K / Real.log (z ^ c)) - 1) ^ 2 := by
      apply add_le_add_right
      exact sum_pair_mul_residual_error_le_of_uniform
        (fun _ _ => ε) hlocal hz hc1 hzc hε hP hcut hscreen
        (by intro p₀ hp₀ p₁ hp₁; exact ⟨hε, le_rfl⟩)

/-- Exact pair-recursion bound with an unrestricted residual comparison.
This is the compatibility form of the theorem; the screened induction uses
`upperRosserBoundaryChainsFixedDepthDensity_succ_le_residualBoundaryMassAux_add_screened`. -/
theorem
    upperRosserBoundaryChainsFixedDepthDensity_succ_le_residualBoundaryMassAux_add
    (k : ℕ) {S : BoundingSieve} {K z c Δ s ε : ℝ}
    {q : ℕ} {P : Finset ℕ}
    (hcomparison : UpperRosserBoundaryResidualComparison S z q k ε)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hz : 1 < z) (hc1 : c ≤ 1) (hzc : 2 ≤ z ^ c) (hε : 0 ≤ ε)
    (hΔ : 0 < Δ) (hs : s = Real.log Δ / Real.log z)
    (hqprime : q.Prime) (hqs : q ∉ P)
    (hP : P ⊆ S.prodPrimes.primeFactors)
    (hqmin : ∀ p ∈ P, q ≤ p)
    (hcut : ∀ p ∈ P, (p : ℝ) ≤ z)
    (hscreen : ∀ p ∈ P, c ≤ Real.log p / Real.log z) :
    LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
        (fun p => S.nu p / (1 - S.nu p))
        (Nat.floor Δ + 1) q P (k + 1) ≤
      (∑ p₀ ∈ P,
        ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
          (S.nu p₀ / (1 - S.nu p₀)) *
            (S.nu p₁ / (1 - S.nu p₁)) *
              LinearSieve.upperRosserBoundaryMassAux k
                (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
                (Real.log q / Real.log z) (Real.log p₁ / Real.log z)) +
        ε * (Real.log (z + 1) / Real.log (z ^ c) *
          (1 + K / Real.log (z ^ c)) - 1) ^ 2 := by
  exact
    upperRosserBoundaryChainsFixedDepthDensity_succ_le_residualBoundaryMassAux_add_screened
      k (c₀ := Real.log q / Real.log z) (s₁ := s) hcomparison.screened
        hlocal hz hc1 hzc hε hΔ hs le_rfl hqprime hqs hP hqmin hcut hscreen le_rfl

/-- The first (inner-prime) Stieltjes stage of the fixed-depth Rosser
successor.  A finite upper Darboux majorant for the actual residual mass turns
the exact two-prime recursion into a sum over the remaining outer prime.  The
closed-cell loss is summed once against the positive-screen prime-mass bound,
while the residual-comparison error retains its quadratic mass bound.  Thus
only the outer Stieltjes stage and the construction of these finite majorants
remain at arbitrary depth. -/
theorem
    exists_upperRosserBoundaryChainsFixedDepthDensity_succ_le_innerPartition_add_screened
    (k : ℕ) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (K ρ B c : ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) (hB : 0 ≤ B)
    (hc : 0 < c) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z Δ s ε c₀ s₁ : ℝ) (q : ℕ) (P : Finset ℕ)
          (cell : ℕ → ℕ → ι) (u v : ι → ℝ) (M : ℕ → ι → ℝ),
        z₀ ≤ z → 0 < Δ → HasDimensionOneLocalProductBound S K →
        s = Real.log Δ / Real.log z → s ≤ s₁ →
        q.Prime → q ∉ P → P ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ P, q ≤ p) → (∀ p ∈ P, (p : ℝ) ≤ z) →
        c ≤ 1 → 2 ≤ z ^ c → 0 ≤ ε →
        (∀ p ∈ P, c ≤ Real.log p / Real.log z) →
        c₀ ≤ Real.log q / Real.log z →
        UpperRosserBoundaryScreenedResidualComparison S z q k ε c₀ s₁ →
        (∀ i, c ≤ u i) → (∀ i, u i ≤ v i) →
        (∀ p₀ ∈ P, ∀ p₁ ∈
            P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
          z ^ (u (cell p₀ p₁)) ≤ (p₁ : ℝ) ∧
            (p₁ : ℝ) ≤ z ^ (v (cell p₀ p₁))) →
        (∀ p₀ ∈ P, ∀ i, 0 ≤ M p₀ i) →
        (∀ p₀ ∈ P, ∀ p₁ ∈
            P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
          LinearSieve.upperRosserBoundaryMassAux k
              (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
              (Real.log q / Real.log z) (Real.log p₁ / Real.log z) ≤
            M p₀ (cell p₀ p₁)) →
        (∀ p₀ ∈ P, ∀ p₁ ∈
            P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
          LinearSieve.upperRosserBoundaryMassAux k
              (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
              (Real.log q / Real.log z) (Real.log p₁ / Real.log z) ≤ B) →
        LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
            (fun p => S.nu p / (1 - S.nu p))
            (Nat.floor Δ + 1) q P (k + 1) ≤
          (∑ p₀ ∈ P, (S.nu p₀ / (1 - S.nu p₀)) *
            (∑ i, M p₀ i *
              (v i / u i * (1 + K / (u i * Real.log z)) - 1))) +
            ρ * (Real.log (z + 1) / Real.log (z ^ c) *
              (1 + K / Real.log (z ^ c)) - 1) +
            ε * (Real.log (z + 1) / Real.log (z ^ c) *
              (1 + K / Real.log (z ^ c)) - 1) ^ 2 := by
  obtain ⟨z₀, hz₀, hstieltjes⟩ :=
    exists_weighted_sum_nu_div_one_sub_le_rpow_partition_Icc_add
      ι K ρ B c hK hρ hB hc
  refine ⟨z₀, hz₀, ?_⟩
  intro S z Δ s ε c₀ s₁ q P cell u v M hz₀z hΔ hlocal hs hsUpper hqprime hqs hP hqmin
    hcut hc1 hzc hε hscreen hqscreen hcomparison hcu huv hinterval hM hmajorant
    hbound
  have hz : 1 < z := lt_of_lt_of_le (by norm_num) (hz₀.trans hz₀z)
  have hlogz : 0 < Real.log z := Real.log_pos hz
  have hqlog : 0 ≤ Real.log q := Real.log_nonneg (by
    exact_mod_cast hqprime.one_lt.le)
  have hqcoord : 0 ≤ Real.log q / Real.log z :=
    div_nonneg hqlog hlogz.le
  have hinner :
      ∀ p₀ ∈ P,
        ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
          (S.nu p₁ / (1 - S.nu p₁)) *
            LinearSieve.upperRosserBoundaryMassAux k
              (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
              (Real.log q / Real.log z) (Real.log p₁ / Real.log z) ≤
          (∑ i, M p₀ i *
            (v i / u i * (1 + K / (u i * Real.log z)) - 1)) + ρ := by
    intro p₀ hp₀
    simpa [mul_comm] using
      hstieltjes S z
        (P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1))
        (fun p₁ =>
          LinearSieve.upperRosserBoundaryMassAux k
            (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
            (Real.log q / Real.log z) (Real.log p₁ / Real.log z))
        (cell p₀) u v (M p₀) hz₀z hlocal hcu huv
        ((Finset.filter_subset _ _).trans hP)
        (hinterval p₀ hp₀) (hM p₀ hp₀)
        (by
          intro p₁ hp₁
          exact ⟨LinearSieve.upperRosserBoundaryMassAux_nonneg k hqcoord,
            hmajorant p₀ hp₀ p₁ hp₁⟩)
        (by
          intro p₁ hp₁
          exact hbound p₀ hp₀ p₁ hp₁)
  have hrec :=
    upperRosserBoundaryChainsFixedDepthDensity_succ_le_residualBoundaryMassAux_add_screened
      k hcomparison hlocal hz hc1 hzc hε hΔ hs hsUpper hqprime hqs hP hqmin hcut
        hscreen hqscreen
  have hmass :
      ∑ p ∈ P, S.nu p / (1 - S.nu p) ≤
        Real.log (z + 1) / Real.log (z ^ c) *
            (1 + K / Real.log (z ^ c)) - 1 :=
    sum_nu_div_one_sub_le_of_log_coordinate_lower
      hlocal hz hc1 hzc hP hcut hscreen
  have hmassScaled :
      (∑ p ∈ P, S.nu p / (1 - S.nu p)) * ρ ≤
        ρ * (Real.log (z + 1) / Real.log (z ^ c) *
          (1 + K / Real.log (z ^ c)) - 1) := by
    rw [mul_comm (∑ p ∈ P, S.nu p / (1 - S.nu p)) ρ]
    exact mul_le_mul_of_nonneg_left hmass hρ.le
  calc
    LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
          (fun p => S.nu p / (1 - S.nu p))
          (Nat.floor Δ + 1) q P (k + 1) ≤
        (∑ p₀ ∈ P,
          ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
            (S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) *
              LinearSieve.upperRosserBoundaryMassAux k
                (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
                (Real.log q / Real.log z) (Real.log p₁ / Real.log z)) +
          ε * (Real.log (z + 1) / Real.log (z ^ c) *
            (1 + K / Real.log (z ^ c)) - 1) ^ 2 := hrec
    _ ≤ (∑ p₀ ∈ P, (S.nu p₀ / (1 - S.nu p₀)) *
          ((∑ i, M p₀ i *
            (v i / u i * (1 + K / (u i * Real.log z)) - 1)) + ρ)) +
          ε * (Real.log (z + 1) / Real.log (z ^ c) *
            (1 + K / Real.log (z ^ c)) - 1) ^ 2 := by
      apply add_le_add_left
      apply Finset.sum_le_sum
      intro p₀ hp₀
      calc
        ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
            (S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) *
              LinearSieve.upperRosserBoundaryMassAux k
                (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
                (Real.log q / Real.log z) (Real.log p₁ / Real.log z) =
            (S.nu p₀ / (1 - S.nu p₀)) *
              ∑ p₁ ∈ P.filter
                  (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
                (S.nu p₁ / (1 - S.nu p₁)) *
                  LinearSieve.upperRosserBoundaryMassAux k
                    (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
                    (Real.log q / Real.log z) (Real.log p₁ / Real.log z) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro p₁ hp₁
              ring
        _ ≤ (S.nu p₀ / (1 - S.nu p₀)) *
            ((∑ i, M p₀ i *
              (v i / u i * (1 + K / (u i * Real.log z)) - 1)) + ρ) :=
          mul_le_mul_of_nonneg_left (hinner p₀ hp₀)
            (nu_div_one_sub_nonneg_of_mem (hP hp₀))
    _ = (∑ p₀ ∈ P, (S.nu p₀ / (1 - S.nu p₀)) *
          (∑ i, M p₀ i *
            (v i / u i * (1 + K / (u i * Real.log z)) - 1))) +
          (∑ p ∈ P, S.nu p / (1 - S.nu p)) * ρ +
          ε * (Real.log (z + 1) / Real.log (z ^ c) *
            (1 + K / Real.log (z ^ c)) - 1) ^ 2 := by
      simp_rw [mul_add, Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ (∑ p₀ ∈ P, (S.nu p₀ / (1 - S.nu p₀)) *
          (∑ i, M p₀ i *
            (v i / u i * (1 + K / (u i * Real.log z)) - 1))) +
          ρ * (Real.log (z + 1) / Real.log (z ^ c) *
            (1 + K / Real.log (z ^ c)) - 1) +
          ε * (Real.log (z + 1) / Real.log (z ^ c) *
            (1 + K / Real.log (z ^ c)) - 1) ^ 2 := by
      linarith

/-- The unrestricted compatibility form of the inner-partition successor. -/
theorem
    exists_upperRosserBoundaryChainsFixedDepthDensity_succ_le_innerPartition_add
    (k : ℕ) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (K ρ B c : ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) (hB : 0 ≤ B) (hc : 0 < c) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z Δ s ε : ℝ) (q : ℕ) (P : Finset ℕ)
          (cell : ℕ → ℕ → ι) (u v : ι → ℝ) (M : ℕ → ι → ℝ),
        z₀ ≤ z → 0 < Δ → HasDimensionOneLocalProductBound S K →
        s = Real.log Δ / Real.log z →
        q.Prime → q ∉ P → P ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ P, q ≤ p) → (∀ p ∈ P, (p : ℝ) ≤ z) →
        c ≤ 1 → 2 ≤ z ^ c → 0 ≤ ε →
        (∀ p ∈ P, c ≤ Real.log p / Real.log z) →
        UpperRosserBoundaryResidualComparison S z q k ε →
        (∀ i, c ≤ u i) → (∀ i, u i ≤ v i) →
        (∀ p₀ ∈ P, ∀ p₁ ∈
            P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
          z ^ (u (cell p₀ p₁)) ≤ (p₁ : ℝ) ∧
            (p₁ : ℝ) ≤ z ^ (v (cell p₀ p₁))) →
        (∀ p₀ ∈ P, ∀ i, 0 ≤ M p₀ i) →
        (∀ p₀ ∈ P, ∀ p₁ ∈
            P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
          LinearSieve.upperRosserBoundaryMassAux k
              (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
              (Real.log q / Real.log z) (Real.log p₁ / Real.log z) ≤
            M p₀ (cell p₀ p₁)) →
        (∀ p₀ ∈ P, ∀ p₁ ∈
            P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
          LinearSieve.upperRosserBoundaryMassAux k
              (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
              (Real.log q / Real.log z) (Real.log p₁ / Real.log z) ≤ B) →
        LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
            (fun p => S.nu p / (1 - S.nu p))
            (Nat.floor Δ + 1) q P (k + 1) ≤
          (∑ p₀ ∈ P, (S.nu p₀ / (1 - S.nu p₀)) *
            (∑ i, M p₀ i *
              (v i / u i * (1 + K / (u i * Real.log z)) - 1))) +
            ρ * (Real.log (z + 1) / Real.log (z ^ c) *
              (1 + K / Real.log (z ^ c)) - 1) +
            ε * (Real.log (z + 1) / Real.log (z ^ c) *
              (1 + K / Real.log (z ^ c)) - 1) ^ 2 := by
  obtain ⟨z₀, hz₀, hscreened⟩ :=
    exists_upperRosserBoundaryChainsFixedDepthDensity_succ_le_innerPartition_add_screened
      k ι K ρ B c hK hρ hB hc
  refine ⟨z₀, hz₀, ?_⟩
  intro S z Δ s ε q P cell u v M hz hΔ hlocal hs hqprime hqs hP hqmin hcut
    hc1 hzc hε hscreen hcomparison hcu huv hinterval hM hmajorant hbound
  exact hscreened S z Δ s ε (Real.log q / Real.log z) s q P cell u v M
    hz hΔ hlocal hs le_rfl hqprime hqs hP hqmin hcut hc1 hzc hε hscreen le_rfl
    hcomparison.screened hcu huv hinterval hM hmajorant hbound

/-- The complete two-prime Stieltjes stage of the fixed-depth Rosser successor.
Finite Darboux majorants for the residual mass and for the resulting inner
upper sum reduce the discrete successor density to one outer logarithmic
Darboux sum.  All local-product, closed-face, and residual-induction errors
remain explicit. -/
theorem
    exists_upperRosserBoundaryChainsFixedDepthDensity_succ_le_twoPartitions_add_screened
    (k : ℕ) (ι κ : Type*) [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (K ρ BInner BOuter c : ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (hBInner : 0 ≤ BInner)
    (hBOuter : 0 ≤ BOuter) (hc : 0 < c) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z Δ s ε c₀ s₁ : ℝ) (q : ℕ) (P : Finset ℕ)
          (innerCell : ℕ → ℕ → ι) (innerLeft innerRight : ι → ℝ)
          (innerMajorant : ℕ → ι → ℝ)
          (outerCell : ℕ → κ) (outerLeft outerRight outerMajorant : κ → ℝ),
        z₀ ≤ z → 0 < Δ → HasDimensionOneLocalProductBound S K →
        s = Real.log Δ / Real.log z → s ≤ s₁ →
        q.Prime → q ∉ P → P ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ P, q ≤ p) → (∀ p ∈ P, (p : ℝ) ≤ z) →
        c ≤ 1 → 2 ≤ z ^ c → 0 ≤ ε →
        (∀ p ∈ P, c ≤ Real.log p / Real.log z) →
        c₀ ≤ Real.log q / Real.log z →
        UpperRosserBoundaryScreenedResidualComparison S z q k ε c₀ s₁ →
        (∀ i, c ≤ innerLeft i) →
        (∀ i, innerLeft i ≤ innerRight i) →
        (∀ p₀ ∈ P, ∀ p₁ ∈
            P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
          z ^ (innerLeft (innerCell p₀ p₁)) ≤ (p₁ : ℝ) ∧
            (p₁ : ℝ) ≤ z ^ (innerRight (innerCell p₀ p₁))) →
        (∀ p₀ ∈ P, ∀ i, 0 ≤ innerMajorant p₀ i) →
        (∀ p₀ ∈ P, ∀ p₁ ∈
            P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
          LinearSieve.upperRosserBoundaryMassAux k
              (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
              (Real.log q / Real.log z) (Real.log p₁ / Real.log z) ≤
            innerMajorant p₀ (innerCell p₀ p₁)) →
        (∀ p₀ ∈ P, ∀ p₁ ∈
            P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
          LinearSieve.upperRosserBoundaryMassAux k
              (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
              (Real.log q / Real.log z) (Real.log p₁ / Real.log z) ≤ BInner) →
        (∀ j, c ≤ outerLeft j) →
        (∀ j, outerLeft j ≤ outerRight j) →
        (∀ p₀ ∈ P,
          z ^ (outerLeft (outerCell p₀)) ≤ (p₀ : ℝ) ∧
            (p₀ : ℝ) ≤ z ^ (outerRight (outerCell p₀))) →
        (∀ j, 0 ≤ outerMajorant j) →
        (∀ p₀ ∈ P,
          0 ≤ ∑ i, innerMajorant p₀ i *
              (innerRight i / innerLeft i *
                (1 + K / (innerLeft i * Real.log z)) - 1) ∧
          (∑ i, innerMajorant p₀ i *
              (innerRight i / innerLeft i *
                (1 + K / (innerLeft i * Real.log z)) - 1)) ≤
            outerMajorant (outerCell p₀)) →
        (∀ p₀ ∈ P,
          (∑ i, innerMajorant p₀ i *
              (innerRight i / innerLeft i *
                (1 + K / (innerLeft i * Real.log z)) - 1)) ≤ BOuter) →
        LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
            (fun p => S.nu p / (1 - S.nu p))
            (Nat.floor Δ + 1) q P (k + 1) ≤
          (∑ j, outerMajorant j *
            (outerRight j / outerLeft j *
              (1 + K / (outerLeft j * Real.log z)) - 1)) + ρ +
            ρ * (Real.log (z + 1) / Real.log (z ^ c) *
              (1 + K / Real.log (z ^ c)) - 1) +
            ε * (Real.log (z + 1) / Real.log (z ^ c) *
              (1 + K / Real.log (z ^ c)) - 1) ^ 2 := by
  obtain ⟨zInner, hzInner, hinner⟩ :=
    exists_upperRosserBoundaryChainsFixedDepthDensity_succ_le_innerPartition_add_screened
      k ι K ρ BInner c hK hρ hBInner hc
  obtain ⟨zOuter, hzOuter, houter⟩ :=
    exists_weighted_sum_nu_div_one_sub_le_rpow_partition_Icc_add
      κ K ρ BOuter c hK hρ hBOuter hc
  let z₀ := max zInner zOuter
  refine ⟨z₀, hzInner.trans (le_max_left _ _), ?_⟩
  intro S z Δ s ε c₀ s₁ q P innerCell innerLeft innerRight innerMajorant
    outerCell outerLeft outerRight outerMajorant hz₀z hΔ hlocal hs hsUpper hqprime
    hqs hP hqmin hcut hc1 hzc hε hscreen hqscreen hcomparison hInnerLeft
    hInnerIntervals hInnerCoordinates hInnerNonneg hInnerMajorant hInnerBound
    hOuterLeft hOuterIntervals hOuterCoordinates hOuterNonneg hOuterMajorant
    hOuterBound
  have hzInnerz : zInner ≤ z := (le_max_left _ _).trans hz₀z
  have hzOuterz : zOuter ≤ z := (le_max_right _ _).trans hz₀z
  let innerSum : ℕ → ℝ := fun p₀ =>
    ∑ i, innerMajorant p₀ i *
      (innerRight i / innerLeft i *
        (1 + K / (innerLeft i * Real.log z)) - 1)
  have hinner' :=
    hinner S z Δ s ε c₀ s₁ q P innerCell innerLeft innerRight innerMajorant
      hzInnerz hΔ hlocal hs hsUpper hqprime hqs hP hqmin hcut hc1 hzc hε hscreen
      hqscreen hcomparison hInnerLeft hInnerIntervals hInnerCoordinates
      hInnerNonneg hInnerMajorant hInnerBound
  have houter' :
      ∑ p₀ ∈ P, (S.nu p₀ / (1 - S.nu p₀)) * innerSum p₀ ≤
        (∑ j, outerMajorant j *
          (outerRight j / outerLeft j *
            (1 + K / (outerLeft j * Real.log z)) - 1)) + ρ := by
    simpa [innerSum, mul_comm] using
      houter S z P innerSum outerCell outerLeft outerRight outerMajorant
        hzOuterz hlocal hOuterLeft hOuterIntervals hP hOuterCoordinates
        hOuterNonneg hOuterMajorant hOuterBound
  calc
    LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
          (fun p => S.nu p / (1 - S.nu p))
          (Nat.floor Δ + 1) q P (k + 1) ≤
        (∑ p₀ ∈ P, (S.nu p₀ / (1 - S.nu p₀)) * innerSum p₀) +
          ρ * (Real.log (z + 1) / Real.log (z ^ c) *
            (1 + K / Real.log (z ^ c)) - 1) +
          ε * (Real.log (z + 1) / Real.log (z ^ c) *
            (1 + K / Real.log (z ^ c)) - 1) ^ 2 := by
      simpa [innerSum] using hinner'
    _ ≤ ((∑ j, outerMajorant j *
          (outerRight j / outerLeft j *
            (1 + K / (outerLeft j * Real.log z)) - 1)) + ρ) +
          ρ * (Real.log (z + 1) / Real.log (z ^ c) *
            (1 + K / Real.log (z ^ c)) - 1) +
          ε * (Real.log (z + 1) / Real.log (z ^ c) *
            (1 + K / Real.log (z ^ c)) - 1) ^ 2 :=
      by linarith

/-- The unrestricted compatibility form of the two-partition successor. -/
theorem
    exists_upperRosserBoundaryChainsFixedDepthDensity_succ_le_twoPartitions_add
    (k : ℕ) (ι κ : Type*) [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (K ρ BInner BOuter c : ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (hBInner : 0 ≤ BInner)
    (hBOuter : 0 ≤ BOuter) (hc : 0 < c) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z Δ s ε : ℝ) (q : ℕ) (P : Finset ℕ)
          (innerCell : ℕ → ℕ → ι) (innerLeft innerRight : ι → ℝ)
          (innerMajorant : ℕ → ι → ℝ)
          (outerCell : ℕ → κ) (outerLeft outerRight outerMajorant : κ → ℝ),
        z₀ ≤ z → 0 < Δ → HasDimensionOneLocalProductBound S K →
        s = Real.log Δ / Real.log z →
        q.Prime → q ∉ P → P ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ P, q ≤ p) → (∀ p ∈ P, (p : ℝ) ≤ z) →
        c ≤ 1 → 2 ≤ z ^ c → 0 ≤ ε →
        (∀ p ∈ P, c ≤ Real.log p / Real.log z) →
        UpperRosserBoundaryResidualComparison S z q k ε →
        (∀ i, c ≤ innerLeft i) →
        (∀ i, innerLeft i ≤ innerRight i) →
        (∀ p₀ ∈ P, ∀ p₁ ∈
            P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
          z ^ (innerLeft (innerCell p₀ p₁)) ≤ (p₁ : ℝ) ∧
            (p₁ : ℝ) ≤ z ^ (innerRight (innerCell p₀ p₁))) →
        (∀ p₀ ∈ P, ∀ i, 0 ≤ innerMajorant p₀ i) →
        (∀ p₀ ∈ P, ∀ p₁ ∈
            P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
          LinearSieve.upperRosserBoundaryMassAux k
              (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
              (Real.log q / Real.log z) (Real.log p₁ / Real.log z) ≤
            innerMajorant p₀ (innerCell p₀ p₁)) →
        (∀ p₀ ∈ P, ∀ p₁ ∈
            P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
          LinearSieve.upperRosserBoundaryMassAux k
              (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
              (Real.log q / Real.log z) (Real.log p₁ / Real.log z) ≤ BInner) →
        (∀ j, c ≤ outerLeft j) →
        (∀ j, outerLeft j ≤ outerRight j) →
        (∀ p₀ ∈ P,
          z ^ (outerLeft (outerCell p₀)) ≤ (p₀ : ℝ) ∧
            (p₀ : ℝ) ≤ z ^ (outerRight (outerCell p₀))) →
        (∀ j, 0 ≤ outerMajorant j) →
        (∀ p₀ ∈ P,
          0 ≤ ∑ i, innerMajorant p₀ i *
              (innerRight i / innerLeft i *
                (1 + K / (innerLeft i * Real.log z)) - 1) ∧
          (∑ i, innerMajorant p₀ i *
              (innerRight i / innerLeft i *
                (1 + K / (innerLeft i * Real.log z)) - 1)) ≤
            outerMajorant (outerCell p₀)) →
        (∀ p₀ ∈ P,
          (∑ i, innerMajorant p₀ i *
              (innerRight i / innerLeft i *
                (1 + K / (innerLeft i * Real.log z)) - 1)) ≤ BOuter) →
        LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
            (fun p => S.nu p / (1 - S.nu p))
            (Nat.floor Δ + 1) q P (k + 1) ≤
          (∑ j, outerMajorant j *
            (outerRight j / outerLeft j *
              (1 + K / (outerLeft j * Real.log z)) - 1)) + ρ +
            ρ * (Real.log (z + 1) / Real.log (z ^ c) *
              (1 + K / Real.log (z ^ c)) - 1) +
            ε * (Real.log (z + 1) / Real.log (z ^ c) *
              (1 + K / Real.log (z ^ c)) - 1) ^ 2 := by
  obtain ⟨z₀, hz₀, hscreened⟩ :=
    exists_upperRosserBoundaryChainsFixedDepthDensity_succ_le_twoPartitions_add_screened
      k ι κ K ρ BInner BOuter c hK hρ hBInner hBOuter hc
  refine ⟨z₀, hz₀, ?_⟩
  intro S z Δ s ε q P innerCell innerLeft innerRight innerMajorant
    outerCell outerLeft outerRight outerMajorant hz hΔ hlocal hs hqprime hqs hP
    hqmin hcut hc1 hzc hε hscreen hcomparison hInnerLeft hInnerIntervals
    hInnerCoordinates hInnerNonneg hInnerMajorant hInnerBound hOuterLeft
    hOuterIntervals hOuterCoordinates hOuterNonneg hOuterMajorant hOuterBound
  exact hscreened S z Δ s ε (Real.log q / Real.log z) s q P
    innerCell innerLeft innerRight innerMajorant outerCell outerLeft outerRight
    outerMajorant hz hΔ hlocal hs le_rfl hqprime hqs hP hqmin hcut hc1 hzc hε
    hscreen le_rfl hcomparison.screened hInnerLeft hInnerIntervals hInnerCoordinates
    hInnerNonneg hInnerMajorant hInnerBound hOuterLeft hOuterIntervals
    hOuterCoordinates hOuterNonneg hOuterMajorant hOuterBound

/-- The two-prime Stieltjes successor on a fixed logarithmic mesh.  The inner
corner majorants are the recursive continuous boundary masses themselves; the
remaining outer majorant is therefore a finite Darboux upper sum for those
explicit corner values. -/
theorem
    exists_upperRosserBoundaryChainsFixedDepthDensity_succ_le_fixedDepthMesh_add_screened
    (k : ℕ) {s₀ s₁ c ε ρ BInner BOuter : ℝ}
    (hc : 0 < c) (hc1 : c < 1) (hε : 0 < ε) (hρ : 0 < ρ)
    (hBInner : 0 ≤ BInner) (hBOuter : 0 ≤ BOuter) :
    ∃ N : ℕ, ∀ K, 1 ≤ K → ∀ m, N ≤ m → ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z Δ s c₀ : ℝ) (q : ℕ) (P : Finset ℕ)
          (h : Fin (m + 1)) (M : Fin (m + 1) → ℝ),
        z₀ ≤ z → 0 < Δ →
        HasDimensionOneLocalProductBound S K →
        s = Real.log Δ / Real.log z →
        s ∈ Set.Icc s₀ s₁ →
        q.Prime → q ∉ P → P ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ P, q ≤ p) → (∀ p ∈ P, (p : ℝ) ≤ z) →
        2 ≤ z ^ c →
        (∀ p ∈ P, c ≤ Real.log p / Real.log z) →
        c₀ ≤ Real.log q / Real.log z →
        UpperRosserBoundaryScreenedResidualComparison S z q (k + 1) ε c₀ s₁ →
        Real.log q / Real.log z ∈ Set.Icc
          (upperRosserFixedDepthMeshLeft c m h)
          (upperRosserFixedDepthMeshRight c m h) →
        (∀ p ∈ P, Real.log p / Real.log z ∈ Set.Icc
          (upperRosserFixedDepthMeshLeft c m
            (upperRosserFixedDepthMeshCell c m (Real.log p / Real.log z)))
          (upperRosserFixedDepthMeshRight c m
            (upperRosserFixedDepthMeshCell c m (Real.log p / Real.log z)))) →
        (∀ i j : Fin (m + 1),
          LinearSieve.upperRosserBoundaryMassAux (k + 1)
              (s - upperRosserFixedDepthMeshRight c m j -
                upperRosserFixedDepthMeshRight c m i)
              (upperRosserFixedDepthMeshLeft c m h)
              (upperRosserFixedDepthMeshRight c m i) + ε ≤ BInner) →
        (∀ i, 0 ≤ M i) →
        (∀ p₀ ∈ P,
          (∑ i, (if upperRosserFixedDepthMeshLeft c m i <
                upperRosserFixedDepthMeshRight c m
                  (upperRosserFixedDepthMeshCell c m
                    (Real.log p₀ / Real.log z)) then
              LinearSieve.upperRosserBoundaryMassAux (k + 1)
                (s - upperRosserFixedDepthMeshRight c m
                  (upperRosserFixedDepthMeshCell c m
                    (Real.log p₀ / Real.log z)) -
                  upperRosserFixedDepthMeshRight c m i)
                (upperRosserFixedDepthMeshLeft c m h)
                (upperRosserFixedDepthMeshRight c m i) + ε
            else 0) *
            (upperRosserFixedDepthMeshRight c m i /
                upperRosserFixedDepthMeshLeft c m i *
              (1 + K / (upperRosserFixedDepthMeshLeft c m i *
                Real.log z)) - 1)) ≤
            M (upperRosserFixedDepthMeshCell c m
              (Real.log p₀ / Real.log z))) →
        (∀ p ∈ P, M (upperRosserFixedDepthMeshCell c m
          (Real.log p / Real.log z)) ≤ BOuter) →
        LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
            (fun p => S.nu p / (1 - S.nu p))
            (Nat.floor Δ + 1) q P (k + 2) ≤
          (∑ i, M i *
            (upperRosserFixedDepthMeshRight c m i /
                upperRosserFixedDepthMeshLeft c m i *
              (1 + K / (upperRosserFixedDepthMeshLeft c m i *
                Real.log z)) - 1)) + ρ +
            ρ * (Real.log (z + 1) / Real.log (z ^ c) *
              (1 + K / Real.log (z ^ c)) - 1) +
            ε * (Real.log (z + 1) / Real.log (z ^ c) *
              (1 + K / Real.log (z ^ c)) - 1) ^ 2 := by
  obtain ⟨N, hN⟩ :=
    exists_upperRosserFixedDepthMesh_mass_majorant_succ_uniform_cutoffs
      k (s₀ := s₀) (s₁ := s₁) hc hc1 hε
  refine ⟨N, ?_⟩
  intro K hK m hm
  obtain ⟨z₀, hz₀, htwo⟩ :=
    exists_upperRosserBoundaryChainsFixedDepthDensity_succ_le_twoPartitions_add_screened
      (k + 1) (Fin (m + 1)) (Fin (m + 1)) K ρ BInner BOuter c hK hρ
        hBInner hBOuter hc
  refine ⟨z₀, hz₀, ?_⟩
  intro S z Δ s c₀ q P h M hz₀z hΔ hlocal hs hsRange hqprime hqs hP hqmin
    hcut hzc hscreen hqscreen hcomparison hqcoord hcell hcornerBound hMnonneg
    hMmajorant hMbound
  have hz : 1 < z := lt_of_lt_of_le (by norm_num) (hz₀.trans hz₀z)
  have hpow : ∀ p ∈ P, z ^ (Real.log p / Real.log z) = (p : ℝ) := by
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors (hP hp)
    have hppos : 0 < (p : ℝ) := by exact_mod_cast hpprime.pos
    simpa [Real.logb] using
      (Real.rpow_logb (x := (p : ℝ)) (by linarith : 0 < z)
        (ne_of_gt hz) hppos)
  have hcell_order : ∀ p₀ ∈ P,
      ∀ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1),
        upperRosserFixedDepthMeshLeft c m
            (upperRosserFixedDepthMeshCell c m (Real.log p₁ / Real.log z)) <
          upperRosserFixedDepthMeshRight c m
            (upperRosserFixedDepthMeshCell c m (Real.log p₀ / Real.log z)) := by
    intro p₀ hp₀ p₁ hp₁
    have hp₁data := Finset.mem_filter.mp hp₁
    have hp₀prime : p₀.Prime := Nat.prime_of_mem_primeFactors (hP hp₀)
    have hp₁prime : p₁.Prime :=
      Nat.prime_of_mem_primeFactors (hP hp₁data.1)
    have hlogz : 0 < Real.log z := Real.log_pos hz
    have hp₀pos : (0 : ℝ) < p₀ := by exact_mod_cast hp₀prime.pos
    have hp₁pos : (0 : ℝ) < p₁ := by exact_mod_cast hp₁prime.pos
    have hcoord : Real.log p₁ / Real.log z < Real.log p₀ / Real.log z := by
      apply (div_lt_div_iff_of_pos_right hlogz).2
      exact (Real.strictMonoOn_log.lt_iff_lt hp₁pos hp₀pos).2
        (by exact_mod_cast hp₁data.2.1)
    exact calc
      upperRosserFixedDepthMeshLeft c m
          (upperRosserFixedDepthMeshCell c m (Real.log p₁ / Real.log z)) ≤
          Real.log p₁ / Real.log z :=
        (hcell p₁ hp₁data.1).1
      _ < Real.log p₀ / Real.log z := hcoord
      _ ≤ upperRosserFixedDepthMeshRight c m
          (upperRosserFixedDepthMeshCell c m (Real.log p₀ / Real.log z)) :=
        (hcell p₀ hp₀).2
  simpa using
    htwo S z Δ s ε c₀ s₁ q P
      (fun _ p₁ => upperRosserFixedDepthMeshCell c m
        (Real.log p₁ / Real.log z))
      (upperRosserFixedDepthMeshLeft c m)
      (upperRosserFixedDepthMeshRight c m)
      (fun p₀ i =>
        if upperRosserFixedDepthMeshLeft c m i <
            upperRosserFixedDepthMeshRight c m
              (upperRosserFixedDepthMeshCell c m
                (Real.log p₀ / Real.log z)) then
          LinearSieve.upperRosserBoundaryMassAux (k + 1)
            (s - upperRosserFixedDepthMeshRight c m
              (upperRosserFixedDepthMeshCell c m (Real.log p₀ / Real.log z)) -
              upperRosserFixedDepthMeshRight c m i)
            (upperRosserFixedDepthMeshLeft c m h)
            (upperRosserFixedDepthMeshRight c m i) + ε
        else 0)
      (fun p => upperRosserFixedDepthMeshCell c m (Real.log p / Real.log z))
      (upperRosserFixedDepthMeshLeft c m)
      (upperRosserFixedDepthMeshRight c m) M
      hz₀z hΔ hlocal hs hsRange.2 hqprime hqs hP hqmin hcut hc1.le hzc hε.le
      hscreen hqscreen hcomparison
      (fun i => (upperRosserFixedDepthMeshLeft_mem hc1 m i).1)
      (fun i => upperRosserFixedDepthMeshLeft_le_right hc1 m i)
      (by
        intro p₀ hp₀ p₁ hp₁
        have hp₁P : p₁ ∈ P := (Finset.mem_filter.mp hp₁).1
        constructor
        · calc
            z ^ upperRosserFixedDepthMeshLeft c m
                (upperRosserFixedDepthMeshCell c m
                  (Real.log p₁ / Real.log z)) ≤
                z ^ (Real.log p₁ / Real.log z) :=
              Real.rpow_le_rpow_of_exponent_le hz.le (hcell p₁ hp₁P).1
            _ = (p₁ : ℝ) := hpow p₁ hp₁P
        · calc
            (p₁ : ℝ) = z ^ (Real.log p₁ / Real.log z) := (hpow p₁ hp₁P).symm
            _ ≤ z ^ upperRosserFixedDepthMeshRight c m
                (upperRosserFixedDepthMeshCell c m
                  (Real.log p₁ / Real.log z)) :=
              Real.rpow_le_rpow_of_exponent_le hz.le (hcell p₁ hp₁P).2)
      (by
        intro p₀ hp₀ i
        by_cases hi : upperRosserFixedDepthMeshLeft c m i <
            upperRosserFixedDepthMeshRight c m
              (upperRosserFixedDepthMeshCell c m
                (Real.log p₀ / Real.log z))
        · rw [if_pos hi]
          exact add_nonneg
            (LinearSieve.upperRosserBoundaryMassAux_nonneg (k + 1)
              (hc.le.trans (upperRosserFixedDepthMeshLeft_mem hc1 m h).1))
            hε.le
        · simp [hi])
      (by
        intro p₀ hp₀ p₁ hp₁
        simpa [hcell_order p₀ hp₀ p₁ hp₁] using hN m hm s hsRange
          h
          (upperRosserFixedDepthMeshCell c m (Real.log p₁ / Real.log z))
          (upperRosserFixedDepthMeshCell c m (Real.log p₀ / Real.log z))
          (Real.log q / Real.log z) (Real.log p₀ / Real.log z)
          (Real.log p₁ / Real.log z) hqcoord (hcell p₀ hp₀)
          (hcell p₁ (Finset.mem_filter.mp hp₁).1))
      (by
        intro p₀ hp₀ p₁ hp₁
        simpa [hcell_order p₀ hp₀ p₁ hp₁] using (hN m hm s hsRange
          h
          (upperRosserFixedDepthMeshCell c m (Real.log p₁ / Real.log z))
          (upperRosserFixedDepthMeshCell c m (Real.log p₀ / Real.log z))
          (Real.log q / Real.log z) (Real.log p₀ / Real.log z)
          (Real.log p₁ / Real.log z) hqcoord (hcell p₀ hp₀)
          (hcell p₁ (Finset.mem_filter.mp hp₁).1)).trans
          (hcornerBound
            (upperRosserFixedDepthMeshCell c m (Real.log p₁ / Real.log z))
            (upperRosserFixedDepthMeshCell c m (Real.log p₀ / Real.log z))))
      (fun i => (upperRosserFixedDepthMeshLeft_mem hc1 m i).1)
      (fun i => upperRosserFixedDepthMeshLeft_le_right hc1 m i)
      (by
        intro p hp
        constructor
        · calc
            z ^ upperRosserFixedDepthMeshLeft c m
                (upperRosserFixedDepthMeshCell c m
                  (Real.log p / Real.log z)) ≤
                z ^ (Real.log p / Real.log z) :=
              Real.rpow_le_rpow_of_exponent_le hz.le (hcell p hp).1
            _ = (p : ℝ) := hpow p hp
        · calc
            (p : ℝ) = z ^ (Real.log p / Real.log z) := (hpow p hp).symm
            _ ≤ z ^ upperRosserFixedDepthMeshRight c m
                (upperRosserFixedDepthMeshCell c m
                  (Real.log p / Real.log z)) :=
              Real.rpow_le_rpow_of_exponent_le hz.le (hcell p hp).2)
      hMnonneg
      (by
        intro p hp
        exact ⟨by
          apply Finset.sum_nonneg
          intro i hi
          apply mul_nonneg
          · by_cases hi : upperRosserFixedDepthMeshLeft c m i <
                upperRosserFixedDepthMeshRight c m
                  (upperRosserFixedDepthMeshCell c m
                    (Real.log p / Real.log z))
            · rw [if_pos hi]
              exact add_nonneg
                (LinearSieve.upperRosserBoundaryMassAux_nonneg (k + 1)
                  (hc.le.trans (upperRosserFixedDepthMeshLeft_mem hc1 m h).1))
                hε.le
            · simp [hi]
          · exact sub_nonneg.mpr (by
              have hleft : 0 < upperRosserFixedDepthMeshLeft c m i :=
                hc.trans_le (upperRosserFixedDepthMeshLeft_mem hc1 m i).1
              have hlogz : 0 < Real.log z := Real.log_pos hz
              have hratio : 1 ≤
                  upperRosserFixedDepthMeshRight c m i /
                    upperRosserFixedDepthMeshLeft c m i :=
                (le_div_iff₀ hleft).2
                  (by simpa using
                    upperRosserFixedDepthMeshLeft_le_right hc1 m i)
              have hcorr : 1 ≤ 1 + K /
                  (upperRosserFixedDepthMeshLeft c m i * Real.log z) := by
                apply le_add_of_nonneg_right
                exact div_nonneg (zero_le_one.trans hK)
                  (mul_pos hleft hlogz).le
              nlinarith [mul_le_mul hratio hcorr zero_le_one
                (zero_le_one.trans hratio)])
            , hMmajorant p hp⟩)
      (by
        intro p hp
        exact (hMmajorant p hp).trans (hMbound p hp))

/-- The unrestricted compatibility form of the fixed-mesh successor. -/
theorem
    exists_upperRosserBoundaryChainsFixedDepthDensity_succ_le_fixedDepthMesh_add
    (k : ℕ) {s₀ s₁ c ε ρ BInner BOuter : ℝ}
    (hc : 0 < c) (hc1 : c < 1) (hε : 0 < ε) (hρ : 0 < ρ)
    (hBInner : 0 ≤ BInner) (hBOuter : 0 ≤ BOuter) :
    ∃ N : ℕ, ∀ K, 1 ≤ K → ∀ m, N ≤ m → ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z Δ s : ℝ) (q : ℕ) (P : Finset ℕ)
          (h : Fin (m + 1)) (M : Fin (m + 1) → ℝ),
        z₀ ≤ z → 0 < Δ →
        HasDimensionOneLocalProductBound S K →
        s = Real.log Δ / Real.log z →
        s ∈ Set.Icc s₀ s₁ →
        q.Prime → q ∉ P → P ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ P, q ≤ p) → (∀ p ∈ P, (p : ℝ) ≤ z) →
        2 ≤ z ^ c →
        (∀ p ∈ P, c ≤ Real.log p / Real.log z) →
        UpperRosserBoundaryResidualComparison S z q (k + 1) ε →
        Real.log q / Real.log z ∈ Set.Icc
          (upperRosserFixedDepthMeshLeft c m h)
          (upperRosserFixedDepthMeshRight c m h) →
        (∀ p ∈ P, Real.log p / Real.log z ∈ Set.Icc
          (upperRosserFixedDepthMeshLeft c m
            (upperRosserFixedDepthMeshCell c m (Real.log p / Real.log z)))
          (upperRosserFixedDepthMeshRight c m
            (upperRosserFixedDepthMeshCell c m (Real.log p / Real.log z)))) →
        (∀ i j : Fin (m + 1),
          LinearSieve.upperRosserBoundaryMassAux (k + 1)
              (s - upperRosserFixedDepthMeshRight c m j -
                upperRosserFixedDepthMeshRight c m i)
              (upperRosserFixedDepthMeshLeft c m h)
              (upperRosserFixedDepthMeshRight c m i) + ε ≤ BInner) →
        (∀ i, 0 ≤ M i) →
        (∀ p₀ ∈ P,
          (∑ i, (if upperRosserFixedDepthMeshLeft c m i <
                upperRosserFixedDepthMeshRight c m
                  (upperRosserFixedDepthMeshCell c m
                    (Real.log p₀ / Real.log z)) then
              LinearSieve.upperRosserBoundaryMassAux (k + 1)
                (s - upperRosserFixedDepthMeshRight c m
                  (upperRosserFixedDepthMeshCell c m
                    (Real.log p₀ / Real.log z)) -
                  upperRosserFixedDepthMeshRight c m i)
                (upperRosserFixedDepthMeshLeft c m h)
                (upperRosserFixedDepthMeshRight c m i) + ε
            else 0) *
            (upperRosserFixedDepthMeshRight c m i /
                upperRosserFixedDepthMeshLeft c m i *
              (1 + K / (upperRosserFixedDepthMeshLeft c m i *
                Real.log z)) - 1)) ≤
            M (upperRosserFixedDepthMeshCell c m
              (Real.log p₀ / Real.log z))) →
        (∀ p ∈ P, M (upperRosserFixedDepthMeshCell c m
          (Real.log p / Real.log z)) ≤ BOuter) →
        LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
            (fun p => S.nu p / (1 - S.nu p))
            (Nat.floor Δ + 1) q P (k + 2) ≤
          (∑ i, M i *
            (upperRosserFixedDepthMeshRight c m i /
                upperRosserFixedDepthMeshLeft c m i *
              (1 + K / (upperRosserFixedDepthMeshLeft c m i *
                Real.log z)) - 1)) + ρ +
            ρ * (Real.log (z + 1) / Real.log (z ^ c) *
              (1 + K / Real.log (z ^ c)) - 1) +
            ε * (Real.log (z + 1) / Real.log (z ^ c) *
              (1 + K / Real.log (z ^ c)) - 1) ^ 2 := by
  obtain ⟨N, hN⟩ :=
    exists_upperRosserBoundaryChainsFixedDepthDensity_succ_le_fixedDepthMesh_add_screened
      k hc hc1 hε hρ hBInner hBOuter
  refine ⟨N, ?_⟩
  intro K hK m hm
  obtain ⟨z₀, hz₀, hscreened⟩ := hN K hK m hm
  refine ⟨z₀, hz₀, ?_⟩
  intro S z Δ s q P h M hz hΔ hlocal hs hsRange hqprime hqs hP hqmin hcut
    hzc hscreen hcomparison hqcoord hcell hcornerBound hMnonneg hMmajorant hMbound
  exact hscreened S z Δ s (Real.log q / Real.log z) q P h M hz hΔ hlocal hs
    hsRange hqprime hqs hP hqmin hcut hzc hscreen le_rfl hcomparison.screened
    hqcoord hcell hcornerBound hMnonneg hMmajorant hMbound

/-- On a sufficiently fine fixed-depth mesh, the explicitly screened inner
corner sum is a Darboux upper sum for the continuous residual mass.  The screen
extends the triangular face by one mesh width, so every cell which can contain
an ordered inner prime is retained. -/
theorem exists_upperRosserFixedDepthMesh_screenedInnerDarboux_succ_le_integral_add
    (k : ℕ) {s₀ s₁ c ε η : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (hε : 0 ≤ ε) (hη : 0 < η) :
    ∃ N : ℕ, ∀ m, N ≤ m → ∀ s ∈ Set.Icc s₀ s₁,
      ∀ h j : Fin (m + 1),
        (∑ i : Fin (m + 1),
          (if upperRosserFixedDepthMeshLeft c m i <
                upperRosserFixedDepthMeshRight c m j then
              LinearSieve.upperRosserBoundaryMassAux (k + 1)
                (s - upperRosserFixedDepthMeshRight c m j -
                  upperRosserFixedDepthMeshRight c m i)
                (upperRosserFixedDepthMeshLeft c m h)
                (upperRosserFixedDepthMeshRight c m i) + ε
            else 0) *
            (upperRosserFixedDepthMeshRight c m i /
                upperRosserFixedDepthMeshLeft c m i - 1)) ≤
          (∫ x in Set.Ioo c 1, x⁻¹ *
            (if x < upperRosserFixedDepthMeshRight c m j +
                upperRosserFixedDepthMeshWidth c m then
              LinearSieve.upperRosserBoundaryMassAux (k + 1)
                (s - upperRosserFixedDepthMeshRight c m j - x)
                (upperRosserFixedDepthMeshLeft c m h) x
            else 0)) +
            (η + ε) / c +
              (c⁻¹ * c⁻¹) ^ (k + 1) *
                upperRosserFixedDepthMeshWidth c m / c ^ 2 := by
  obtain ⟨δ, hδ, hmod⟩ :=
    LinearSieve.exists_upperRosserBoundaryMassAux_level_lower_upper_modulus_succ
      k (r₀ := s₀ - 2) (r₁ := s₁ - 2 * c) hc hη
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 - c) / δ < N := exists_nat_gt _
  refine ⟨N, ?_⟩
  intro m hNm s hs h j
  let a := upperRosserFixedDepthMeshLeft c m h
  let rj := upperRosserFixedDepthMeshRight c m j
  let w := upperRosserFixedDepthMeshWidth c m
  let B := (c⁻¹ * c⁻¹) ^ (k + 1)
  let f : ℝ → ℝ := fun x =>
    if x < rj + w then
      LinearSieve.upperRosserBoundaryMassAux (k + 1) (s - rj - x) a x
    else 0
  let M : Fin (m + 1) → ℝ := fun i =>
    if upperRosserFixedDepthMeshLeft c m i < rj then
      LinearSieve.upperRosserBoundaryMassAux (k + 1)
        (s - rj - upperRosserFixedDepthMeshRight c m i) a
        (upperRosserFixedDepthMeshRight c m i) + ε
    else 0
  have hw : w < δ := by
    have hm : (1 - c) / δ < (m : ℝ) :=
      hN.trans_le (by exact_mod_cast hNm)
    have hcross : 1 - c < δ * (m : ℝ) :=
      by simpa [mul_comm] using (div_lt_iff₀ hδ).1 hm
    dsimp [w, upperRosserFixedDepthMeshWidth]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
    nlinarith
  have ha : a ∈ Set.Icc c 1 := by
    simpa [a] using upperRosserFixedDepthMeshLeft_mem hc1 m h
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hfB : ∀ x ∈ Set.Icc c 1, f x ≤ B := by
    intro x hx
    by_cases hxscreen : x < rj + w
    · rw [show f x =
          LinearSieve.upperRosserBoundaryMassAux (k + 1) (s - rj - x) a x by
            simp [f, hxscreen]]
      exact LinearSieve.upperRosserBoundaryMassAux_le_of_lower_bound
        (k + 1) hc ha.1 hx.2
    · simp [f, hxscreen, hB]
  have hmajorant : ∀ i : Fin (m + 1),
      ∀ x ∈ Set.Ioo (upperRosserFixedDepthMeshLeft c m i)
        (upperRosserFixedDepthMeshRight c m i), M i ≤ f x + (η + ε) := by
    intro i x hx
    by_cases hiscreen : upperRosserFixedDepthMeshLeft c m i < rj
    · have hli := upperRosserFixedDepthMeshLeft_mem hc1 m i
      have hri := upperRosserFixedDepthMeshRight_mem hc1 m i
      have hriw : upperRosserFixedDepthMeshRight c m i =
          upperRosserFixedDepthMeshLeft c m i + w := by
        dsimp [w, upperRosserFixedDepthMeshRight]
      have hxscreen : x < rj + w := by
        calc
          x < upperRosserFixedDepthMeshRight c m i := hx.2
          _ = upperRosserFixedDepthMeshLeft c m i + w := hriw
          _ < rj + w := by linarith
      have hxmem : x ∈ Set.Icc c 1 :=
        ⟨hli.1.trans hx.1.le, hx.2.le.trans hri.2⟩
      have hcorner :
          ((s - rj - upperRosserFixedDepthMeshRight c m i, a),
              upperRosserFixedDepthMeshRight c m i) ∈
            (Set.Icc (s₀ - 2) (s₁ - 2 * c) ×ˢ Set.Icc c 1) ×ˢ
              Set.Icc c 1 := by
        refine ⟨⟨?_, ha⟩, hri⟩
        constructor
        · linarith [hs.1, (upperRosserFixedDepthMeshRight_mem hc1 m j).2, hri.2]
        · linarith [hs.2, (upperRosserFixedDepthMeshRight_mem hc1 m j).1, hri.1]
      have hactual :
          ((s - rj - x, a), x) ∈
            (Set.Icc (s₀ - 2) (s₁ - 2 * c) ×ˢ Set.Icc c 1) ×ˢ
              Set.Icc c 1 := by
        refine ⟨⟨?_, ha⟩, hxmem⟩
        constructor
        · linarith [hs.1, (upperRosserFixedDepthMeshRight_mem hc1 m j).2, hxmem.2]
        · linarith [hs.2, (upperRosserFixedDepthMeshRight_mem hc1 m j).1, hxmem.1]
      have hgap : 0 ≤ upperRosserFixedDepthMeshRight c m i - x ∧
          upperRosserFixedDepthMeshRight c m i - x < w := by
        constructor
        · linarith [hx.2]
        · rw [hriw]
          linarith [hx.1]
      have hdist :
          dist ((s - rj - upperRosserFixedDepthMeshRight c m i, a),
              upperRosserFixedDepthMeshRight c m i)
            ((s - rj - x, a), x) < δ := by
        simp only [Prod.dist_eq, Real.dist_eq, max_lt_iff]
        constructor
        · constructor
          · rw [show (s - rj - upperRosserFixedDepthMeshRight c m i) -
                (s - rj - x) =
                x - upperRosserFixedDepthMeshRight c m i by ring,
              abs_of_nonpos (by linarith [hgap.1])]
            linarith [hgap.2.trans hw]
          · simp [hδ]
        · rw [abs_of_nonneg hgap.1]
          exact hgap.2.trans hw
      have hclose := hmod _ hcorner _ hactual hdist
      have hle := le_abs_self
        (LinearSieve.upperRosserBoundaryMassAux (k + 1)
            (s - rj - upperRosserFixedDepthMeshRight c m i) a
            (upperRosserFixedDepthMeshRight c m i) -
          LinearSieve.upperRosserBoundaryMassAux (k + 1) (s - rj - x) a x)
      have hmass :
          LinearSieve.upperRosserBoundaryMassAux (k + 1)
              (s - rj - upperRosserFixedDepthMeshRight c m i) a
              (upperRosserFixedDepthMeshRight c m i) ≤
            LinearSieve.upperRosserBoundaryMassAux (k + 1)
              (s - rj - x) a x + η := by
        linarith
      rw [show M i =
          LinearSieve.upperRosserBoundaryMassAux (k + 1)
              (s - rj - upperRosserFixedDepthMeshRight c m i) a
              (upperRosserFixedDepthMeshRight c m i) + ε by
            simp [M, hiscreen]]
      rw [show f x =
          LinearSieve.upperRosserBoundaryMassAux (k + 1) (s - rj - x) a x by
            simp [f, hxscreen]]
      linarith
    · have hnonneg : 0 ≤ f x := by
        by_cases hxscreen : x < rj + w
        · simp [f, hxscreen,
            LinearSieve.upperRosserBoundaryMassAux_nonneg (k + 1)
              (hc.le.trans ha.1)]
        · simp [f, hxscreen]
      rw [show M i = 0 by simp [M, hiscreen]]
      exact add_nonneg hnonneg (add_nonneg hη.le hε)
  have hg : MeasureTheory.IntegrableOn
      (fun x => x⁻¹ *
        LinearSieve.upperRosserBoundaryMassAux (k + 1) (s - rj - x) a x)
      (Set.Ioo c 1) := by
    have hfinite : MeasureTheory.volume (Set.Ioo c 1) < ⊤ := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_lt_top
    have hmassMeas : MeasureTheory.StronglyMeasurable
        (fun x => LinearSieve.upperRosserBoundaryMassAux
          (k + 1) (s - rj - x) a x) := by
      have hmeas :=
        (LinearSieve.stronglyMeasurable_upperRosserBoundaryMassAux
          (k + 1)).comp_measurable
            (show Measurable (fun x : ℝ => ((s - rj - x, a), x)) by fun_prop)
      convert hmeas using 1
      funext x
      rfl
    have hmeas : MeasureTheory.StronglyMeasurable
        (fun x => x⁻¹ *
          LinearSieve.upperRosserBoundaryMassAux (k + 1) (s - rj - x) a x) :=
      measurable_id.inv.stronglyMeasurable.mul hmassMeas
    apply MeasureTheory.IntegrableOn.of_bound hfinite hmeas.aestronglyMeasurable
      (c⁻¹ * B)
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    have hxpos : 0 < x := hc.trans hx.1
    have hxinv : x⁻¹ ≤ c⁻¹ := (inv_le_inv₀ hxpos hc).2 hx.1.le
    have hmass := LinearSieve.upperRosserBoundaryMassAux_le_of_lower_bound
      (k + 1) (s := s - rj - x) (a := a) (b := x) hc ha.1 hx.2.le
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (inv_nonneg.mpr hxpos.le)
        (LinearSieve.upperRosserBoundaryMassAux_nonneg (k + 1)
          (hc.le.trans ha.1)))]
    calc
      x⁻¹ * LinearSieve.upperRosserBoundaryMassAux (k + 1) (s - rj - x) a x ≤
          c⁻¹ * LinearSieve.upperRosserBoundaryMassAux
            (k + 1) (s - rj - x) a x :=
        mul_le_mul_of_nonneg_right hxinv
          (LinearSieve.upperRosserBoundaryMassAux_nonneg (k + 1)
            (hc.le.trans ha.1))
      _ ≤ c⁻¹ * B :=
        mul_le_mul_of_nonneg_left hmass (inv_nonneg.mpr hc.le)
  have hint : MeasureTheory.IntegrableOn (fun x => x⁻¹ * f x)
      (Set.Ioo c 1) := by
    have hfun : (fun x => x⁻¹ * f x) =
        (Set.Iio (rj + w)).indicator
          (fun x => x⁻¹ *
            LinearSieve.upperRosserBoundaryMassAux (k + 1) (s - rj - x) a x) := by
      funext x
      by_cases hxscreen : x < rj + w <;> simp [f, hxscreen]
    rw [hfun]
    exact hg.indicator (measurableSet_Iio : MeasurableSet (Set.Iio (rj + w)))
  simpa [M, f, B, rj, w, a] using
    upperRosserFixedDepthMesh_darbouxSum_le_integral_add
      m hc hc1 (add_nonneg hη.le hε) hB hfB hmajorant hint

/-- Uniform weighted Stieltjes comparison on the fixed screened mesh.  The
cutoff absorbs all closed right-face atoms at once; its dependence is only on
the mesh, the local-product constant, the weight bound, and the requested
error. -/
theorem exists_weighted_sum_nu_div_one_sub_le_upperRosserDepthTwoMesh
    (m : ℕ) (K ρ B : ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) (hB : 0 ≤ B) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
        ∀ (S : BoundingSieve) (z : ℝ) (T : Finset ℕ) (w : ℕ → ℝ)
            (M : Fin (m + 1) → ℝ),
          z₀ ≤ z → HasDimensionOneLocalProductBound S K →
          T ⊆ S.prodPrimes.primeFactors →
          (∀ p ∈ T, Real.log p / Real.log z ∈ Set.Icc (1 / 6 : ℝ) 1) →
          (∀ i, 0 ≤ M i) →
          (∀ p ∈ T,
            0 ≤ w p ∧
              w p ≤ M (upperRosserDepthTwoMeshCell m
                (Real.log p / Real.log z))) →
          (∀ p ∈ T, w p ≤ B) →
          ∑ p ∈ T, w p * (S.nu p / (1 - S.nu p)) ≤
            (∑ i : Fin (m + 1), M i *
              (upperRosserDepthTwoMeshRight m i /
                  upperRosserDepthTwoMeshLeft m i *
                (1 + K / (upperRosserDepthTwoMeshLeft m i * Real.log z)) - 1)) +
              ρ := by
  let ρface := ρ / (B + 1)
  have hB1 : 0 < B + 1 := by linarith
  have hρface : 0 < ρface := div_pos hρ hB1
  obtain ⟨zA, hzA, hfaces⟩ :=
    exists_rpow_partition_right_faces_mass_le
        (Fin (m + 1)) K ρface (1 / 6) hK hρface (by norm_num)
  let z₀ := max zA ((2 : ℝ) ^ (6 : ℝ))
  refine ⟨z₀, hzA.trans (le_max_left _ _), ?_⟩
  intro S z T w M hz hlocal hT hcoord hM hw hwB
  have hzA_le : zA ≤ z := (le_max_left _ _).trans hz
  have hz2pow : (2 : ℝ) ^ (6 : ℝ) ≤ z :=
    (le_max_right _ _).trans hz
  have hz2 : 2 ≤ z := hzA.trans hzA_le
  have hz1 : 1 < z := by linarith
  have hzpos : 0 < z := by linarith
  let cell : ℕ → Fin (m + 1) :=
    fun p => upperRosserDepthTwoMeshCell m (Real.log p / Real.log z)
  let u : Fin (m + 1) → ℝ := upperRosserDepthTwoMeshLeft m
  let v : Fin (m + 1) → ℝ := upperRosserDepthTwoMeshRight m
  have hinterval : ∀ p ∈ T,
        z ^ (u (cell p)) ≤ (p : ℝ) ∧ (p : ℝ) ≤ z ^ (v (cell p)) := by
    intro p hp
    have hpS := hT hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpS
    have hpPos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    have hbounds := upperRosserDepthTwoMeshCell_bounds m (hcoord p hp)
    have heq : z ^ (Real.log p / Real.log z) = (p : ℝ) := by
        simpa [Real.logb] using
          (Real.rpow_logb (x := (p : ℝ)) hzpos (ne_of_gt hz1) hpPos)
    constructor
    · calc
          z ^ (u (cell p)) ≤ z ^ (Real.log p / Real.log z) :=
            Real.rpow_le_rpow_of_exponent_le hz1.le hbounds.1
          _ = (p : ℝ) := heq
    · calc
          (p : ℝ) = z ^ (Real.log p / Real.log z) := heq.symm
          _ ≤ z ^ (v (cell p)) :=
            Real.rpow_le_rpow_of_exponent_le hz1.le hbounds.2
  have hzc : 2 ≤ z ^ (1 / 6 : ℝ) := by
    calc
        (2 : ℝ) = ((2 : ℝ) ^ (6 : ℝ)) ^ (1 / 6 : ℝ) := by
          rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
        _ ≤ z ^ (1 / 6 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hz2pow (by norm_num)
  have hfaceMass :
        ∑ p ∈ T.filter (fun p : ℕ => ¬(p : ℝ) < z ^ (v (cell p))),
            S.nu p / (1 - S.nu p) ≤ ρface := by
    exact hfaces S z T cell v hzA_le hlocal hT
        (fun p hp => (Real.rpow_le_rpow_of_exponent_le hz1.le (by
            dsimp [u, upperRosserDepthTwoMeshLeft]
            have hi : (0 : ℝ) ≤ (upperRosserDepthTwoMeshCell m
                (Real.log p / Real.log z) : ℝ) := by positivity
            have hh := upperRosserDepthTwoMeshWidth_pos m
            nlinarith)).trans (hinterval p hp).1)
        (fun p hp => (hinterval p hp).2)
  have hweightedFaces :
        ∑ p ∈ T.filter (fun p : ℕ => ¬(p : ℝ) < z ^ (v (cell p))),
            w p * (S.nu p / (1 - S.nu p)) ≤ ρ := by
    calc
        ∑ p ∈ T.filter (fun p : ℕ => ¬(p : ℝ) < z ^ (v (cell p))),
            w p * (S.nu p / (1 - S.nu p)) ≤
            ∑ p ∈ T.filter (fun p : ℕ => ¬(p : ℝ) < z ^ (v (cell p))),
              B * (S.nu p / (1 - S.nu p)) := by
          apply Finset.sum_le_sum
          intro p hp
          apply mul_le_mul_of_nonneg_right
            (hwB p (Finset.mem_filter.mp hp).1)
          exact nu_div_one_sub_nonneg_of_mem (hT (Finset.mem_filter.mp hp).1)
        _ = B * ∑ p ∈ T.filter
            (fun p : ℕ => ¬(p : ℝ) < z ^ (v (cell p))),
              S.nu p / (1 - S.nu p) := by rw [Finset.mul_sum]
        _ ≤ B * ρface := mul_le_mul_of_nonneg_left hfaceMass hB
        _ ≤ ρ := by
          calc
            B * ρface ≤ (B + 1) * ρface :=
              mul_le_mul_of_nonneg_right (by linarith) hρface.le
            _ = ρ := by
              dsimp [ρface]
              field_simp
  apply weighted_sum_nu_div_one_sub_le_rpow_partition_Icc_add_global_atoms
    (S := S) (K := K) (z := z) (T := T) (cell := cell)
    (a := u) (b := v) (M := M) (w := w) hlocal hz1
  · intro i
    exact upperRosserDepthTwoMeshLeft_pos m i
  · intro i
    exact upperRosserDepthTwoMeshLeft_le_right m i
  · intro i
    exact hzc.trans
        (Real.rpow_le_rpow_of_exponent_le hz1.le (by
          dsimp [u, upperRosserDepthTwoMeshLeft]
          have hi : (0 : ℝ) ≤ (i : ℝ) := by positivity
          have hh := upperRosserDepthTwoMeshWidth_pos m
          nlinarith))
  · exact hT
  · exact hinterval
  · exact hM
  · exact hw
  · exact hweightedFaces

/-- The same fixed-mesh comparison with both the closed-face loss and every
`K / log z` correction absorbed into one prescribed error.  Its main term is
the genuine logarithmic Darboux sum `Mᵢ (vᵢ / uᵢ - 1)`. -/
theorem
    exists_weighted_sum_nu_div_one_sub_le_upperRosserDepthTwoMeshMain
    (m : ℕ) (K ρ B : ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) (hB : 0 ≤ B) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z : ℝ) (T : Finset ℕ) (w : ℕ → ℝ)
          (M : Fin (m + 1) → ℝ),
        z₀ ≤ z → HasDimensionOneLocalProductBound S K →
        T ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ T, Real.log p / Real.log z ∈ Set.Icc (1 / 6 : ℝ) 1) →
        (∀ i, 0 ≤ M i ∧ M i ≤ B) →
        (∀ p ∈ T,
          0 ≤ w p ∧
            w p ≤ M (upperRosserDepthTwoMeshCell m
              (Real.log p / Real.log z))) →
        (∀ p ∈ T, w p ≤ B) →
        ∑ p ∈ T, w p * (S.nu p / (1 - S.nu p)) ≤
          (∑ i : Fin (m + 1), M i *
            (upperRosserDepthTwoMeshRight m i /
              upperRosserDepthTwoMeshLeft m i - 1)) + ρ := by
  let η := ρ /
    (12 * (((m : ℝ) + 1) * (B + 1)))
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hB1 : 0 < B + 1 := by linarith
  have hden : 0 < 12 * (((m : ℝ) + 1) * (B + 1)) := by positivity
  have hη : 0 < η := div_pos hρ hden
  obtain ⟨zA, hzA, hmesh⟩ :=
    exists_weighted_sum_nu_div_one_sub_le_upperRosserDepthTwoMesh
      m K (ρ / 2) B hK (half_pos hρ) hB
  obtain ⟨zE, hzE, herror⟩ :=
    exists_localProduct_error_cutoff
      (K := K) (η := η) (c := 1 / 6) hη (by norm_num)
  let z₀ := max zA zE
  refine ⟨z₀, hzA.trans (le_max_left _ _), ?_⟩
  intro S z T w M hz hlocal hT hcoord hM hw hwB
  have hzA_le : zA ≤ z := (le_max_left _ _).trans hz
  have hzE_le : zE ≤ z := (le_max_right _ _).trans hz
  have hz2 : 2 ≤ z := hzA.trans hzA_le
  have hz1 : 1 < z := by linarith
  have hraw := hmesh S z T w M hzA_le hlocal hT hcoord
    (fun i => (hM i).1) hw hwB
  have hcell : ∀ i : Fin (m + 1),
      M i * (upperRosserDepthTwoMeshRight m i /
          upperRosserDepthTwoMeshLeft m i *
            (1 + K /
              (upperRosserDepthTwoMeshLeft m i * Real.log z)) - 1) ≤
        M i * (upperRosserDepthTwoMeshRight m i /
          upperRosserDepthTwoMeshLeft m i - 1) + 6 * B * η := by
    intro i
    let u := upperRosserDepthTwoMeshLeft m i
    let v := upperRosserDepthTwoMeshRight m i
    have hu : 0 < u := upperRosserDepthTwoMeshLeft_pos m i
    have hcu : (1 / 6 : ℝ) ≤ u := by
      dsimp [u, upperRosserDepthTwoMeshLeft]
      have hi : (0 : ℝ) ≤ (i : ℝ) := by positivity
      have hh := upperRosserDepthTwoMeshWidth_pos m
      nlinarith
    have hv : v ≤ 1 := upperRosserDepthTwoMeshRight_le_one m i
    have hratio : v / u ≤ 6 := by
      apply (div_le_iff₀ hu).2
      nlinarith
    have hratioNonneg : 0 ≤ v / u :=
      div_nonneg (hu.le.trans (upperRosserDepthTwoMeshLeft_le_right m i)) hu.le
    have herrorCell :
        K / (u * Real.log z) ≤ η :=
      (localProduct_error_le_of_log_coordinate_lower
        (zero_le_one.trans hK) hz1 (by norm_num) hcu).trans
          (herror z hzE_le)
    have herrorNonneg : 0 ≤ K / (u * Real.log z) :=
      div_nonneg (zero_le_one.trans hK)
        (mul_nonneg hu.le (Real.log_pos hz1).le)
    have hprod :
        M i * (v / u) * (K / (u * Real.log z)) ≤ 6 * B * η := by
      have hMr : M i * (v / u) ≤ B * 6 :=
        mul_le_mul (hM i).2 hratio hratioNonneg hB
      exact (mul_le_mul hMr herrorCell herrorNonneg
        (mul_nonneg hB (by norm_num))).trans_eq (by ring)
    dsimp [u, v] at hprod ⊢
    nlinarith
  have hsum :
      (∑ i : Fin (m + 1), M i *
        (upperRosserDepthTwoMeshRight m i /
            upperRosserDepthTwoMeshLeft m i *
          (1 + K /
            (upperRosserDepthTwoMeshLeft m i * Real.log z)) - 1)) ≤
        (∑ i : Fin (m + 1), M i *
          (upperRosserDepthTwoMeshRight m i /
            upperRosserDepthTwoMeshLeft m i - 1)) +
          ((m : ℝ) + 1) * (6 * B * η) := by
    calc
      (∑ i : Fin (m + 1), M i *
        (upperRosserDepthTwoMeshRight m i /
            upperRosserDepthTwoMeshLeft m i *
          (1 + K /
            (upperRosserDepthTwoMeshLeft m i * Real.log z)) - 1)) ≤
          ∑ i : Fin (m + 1),
            (M i * (upperRosserDepthTwoMeshRight m i /
              upperRosserDepthTwoMeshLeft m i - 1) + 6 * B * η) :=
        Finset.sum_le_sum fun i _ => hcell i
      _ = (∑ i : Fin (m + 1), M i *
          (upperRosserDepthTwoMeshRight m i /
            upperRosserDepthTwoMeshLeft m i - 1)) +
          ((m : ℝ) + 1) * (6 * B * η) := by
        rw [Finset.sum_add_distrib]
        simp
  have hηtotal : ((m : ℝ) + 1) * (6 * B * η) ≤ ρ / 2 := by
    calc
      ((m : ℝ) + 1) * (6 * B * η) ≤
          ((m : ℝ) + 1) * (6 * (B + 1) * η) := by
        gcongr
        linarith
      _ = ρ / 2 := by
        dsimp [η]
        field_simp
        ring
  calc
    ∑ p ∈ T, w p * (S.nu p / (1 - S.nu p)) ≤
        (∑ i : Fin (m + 1), M i *
          (upperRosserDepthTwoMeshRight m i /
              upperRosserDepthTwoMeshLeft m i *
            (1 + K /
              (upperRosserDepthTwoMeshLeft m i * Real.log z)) - 1)) +
          ρ / 2 := hraw
    _ ≤ ((∑ i : Fin (m + 1), M i *
          (upperRosserDepthTwoMeshRight m i /
            upperRosserDepthTwoMeshLeft m i - 1)) +
          ((m : ℝ) + 1) * (6 * B * η)) + ρ / 2 :=
      by simpa [add_assoc, add_comm, add_left_comm] using
        add_le_add_right hsum (ρ / 2)
    _ ≤ (∑ i : Fin (m + 1), M i *
          (upperRosserDepthTwoMeshRight m i /
            upperRosserDepthTwoMeshLeft m i - 1)) + ρ := by
      linarith

/-- A fixed screened mesh compares every uniformly bounded Lipschitz prime
weight with its logarithmic integral.  All dimension-one product errors and
closed right-face atoms are absorbed in the cutoff. -/
theorem exists_weighted_sum_nu_div_one_sub_le_integral_add_of_depthTwoMesh
    (m : ℕ) (K ρ B L : ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hmesh :
      (12 * L + 36 * B) * upperRosserDepthTwoMeshWidth m ≤ ρ / 2) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z : ℝ) (T : Finset ℕ) (w : ℕ → ℝ)
          (f : ℝ → ℝ),
        z₀ ≤ z → HasDimensionOneLocalProductBound S K →
        T ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ T, Real.log p / Real.log z ∈ Set.Icc (1 / 6 : ℝ) 1) →
        (∀ x ∈ Set.Icc (1 / 6 : ℝ) 1, 0 ≤ f x) →
        (∀ x ∈ Set.Icc (1 / 6 : ℝ) 1, f x ≤ B) →
        (∀ x ∈ Set.Icc (1 / 6 : ℝ) 1,
          ∀ y ∈ Set.Icc (1 / 6 : ℝ) 1,
            |f x - f y| ≤ L * |x - y|) →
        MeasureTheory.IntegrableOn
          (fun x => x⁻¹ * f x) (Set.Ioo (1 / 6) 1) →
        (∀ p ∈ T, 0 ≤ w p ∧ w p ≤ f (Real.log p / Real.log z)) →
        ∑ p ∈ T, w p * (S.nu p / (1 - S.nu p)) ≤
          (∫ x in Set.Ioo (1 / 6) 1, x⁻¹ * f x) + ρ := by
  let h := upperRosserDepthTwoMeshWidth m
  have hh : 0 < h := upperRosserDepthTwoMeshWidth_pos m
  have hhOne : h ≤ 1 := by
    dsimp [h, upperRosserDepthTwoMeshWidth]
    have hmpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    apply (div_le_iff₀ hmpos).2
    nlinarith
  have hBL : 0 ≤ B + L := add_nonneg hB hL
  obtain ⟨z₀, hz₀, hweighted⟩ :=
    exists_weighted_sum_nu_div_one_sub_le_upperRosserDepthTwoMeshMain
      m K (ρ / 2) (B + L) hK (half_pos hρ) hBL
  refine ⟨z₀, hz₀, ?_⟩
  intro S z T w f hz hlocal hT hcoord hf hfB hfLip hint hw
  let M : Fin (m + 1) → ℝ :=
    fun i => f (upperRosserDepthTwoMeshLeft m i) + L * h
  have hleftMem : ∀ i : Fin (m + 1),
      upperRosserDepthTwoMeshLeft m i ∈ Set.Icc (1 / 6 : ℝ) 1 := by
    intro i
    constructor
    · dsimp [upperRosserDepthTwoMeshLeft]
      have hi : (0 : ℝ) ≤ (i : ℝ) := by positivity
      nlinarith
    · exact (upperRosserDepthTwoMeshLeft_le_right m i).trans
        (upperRosserDepthTwoMeshRight_le_one m i)
  have hM : ∀ i, 0 ≤ M i ∧ M i ≤ B + L := by
    intro i
    constructor
    · exact add_nonneg (hf _ (hleftMem i)) (mul_nonneg hL hh.le)
    · dsimp [M]
      have hfleft := hfB _ (hleftMem i)
      have hLh : L * h ≤ L := mul_le_of_le_one_right hL hhOne
      linarith
  have hwM : ∀ p ∈ T,
      0 ≤ w p ∧
        w p ≤ M (upperRosserDepthTwoMeshCell m
          (Real.log p / Real.log z)) := by
    intro p hp
    refine ⟨(hw p hp).1, ?_⟩
    let x := Real.log p / Real.log z
    let i := upperRosserDepthTwoMeshCell m x
    have hbounds := upperRosserDepthTwoMeshCell_bounds m (hcoord p hp)
    have hdist :
        |x - upperRosserDepthTwoMeshLeft m i| ≤ h := by
      rw [abs_of_nonneg (sub_nonneg.mpr hbounds.1)]
      calc
        x - upperRosserDepthTwoMeshLeft m i ≤
            upperRosserDepthTwoMeshRight m i -
              upperRosserDepthTwoMeshLeft m i := by linarith [hbounds.2]
        _ = h := by
          dsimp [h, upperRosserDepthTwoMeshRight]
          ring
    have hdiff :=
      (hfLip x (hcoord p hp) (upperRosserDepthTwoMeshLeft m i)
        (hleftMem i)).trans
        (mul_le_mul_of_nonneg_left hdist hL)
    have hupper :
        f x ≤ f (upperRosserDepthTwoMeshLeft m i) + L * h := by
      have := (le_abs_self
        (f x - f (upperRosserDepthTwoMeshLeft m i))).trans hdiff
      linarith
    exact (hw p hp).2.trans (by simpa [M, i, x] using hupper)
  have hwBound : ∀ p ∈ T, w p ≤ B + L := by
    intro p hp
    exact (hw p hp).2.trans ((hfB _ (hcoord p hp)).trans (le_add_of_nonneg_right hL))
  have hdiscrete :=
    hweighted S z T w M hz hlocal hT hcoord hM hwM hwBound
  have hdarboux :=
    upperRosserDepthTwoMesh_darbouxSum_le_integral_add
      m hB hL hf hfB hfLip hint
  calc
    ∑ p ∈ T, w p * (S.nu p / (1 - S.nu p)) ≤
        (∑ i : Fin (m + 1), M i *
          (upperRosserDepthTwoMeshRight m i /
            upperRosserDepthTwoMeshLeft m i - 1)) + ρ / 2 := hdiscrete
    _ ≤ ((∫ x in Set.Ioo (1 / 6) 1, x⁻¹ * f x) +
          (12 * L + 36 * B) * upperRosserDepthTwoMeshWidth m) +
          ρ / 2 := by
      simpa [M, h] using add_le_add hdarboux (le_refl (ρ / 2))
    _ ≤ (∫ x in Set.Ioo (1 / 6) 1, x⁻¹ * f x) + ρ := by
      linarith

/-- Uniform screened Stieltjes comparison for bounded nonnegative Lipschitz
weights.  The mesh and the local-product cutoff depend only on the displayed
uniform constants and the requested error. -/
theorem exists_weighted_sum_nu_div_one_sub_le_integral_add
    (K ρ B L : ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (hB : 0 ≤ B) (hL : 0 ≤ L) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z : ℝ) (T : Finset ℕ) (w : ℕ → ℝ)
          (f : ℝ → ℝ),
        z₀ ≤ z → HasDimensionOneLocalProductBound S K →
        T ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ T, Real.log p / Real.log z ∈ Set.Icc (1 / 6 : ℝ) 1) →
        (∀ x ∈ Set.Icc (1 / 6 : ℝ) 1, 0 ≤ f x) →
        (∀ x ∈ Set.Icc (1 / 6 : ℝ) 1, f x ≤ B) →
        (∀ x ∈ Set.Icc (1 / 6 : ℝ) 1,
          ∀ y ∈ Set.Icc (1 / 6 : ℝ) 1,
            |f x - f y| ≤ L * |x - y|) →
        MeasureTheory.IntegrableOn
          (fun x => x⁻¹ * f x) (Set.Ioo (1 / 6) 1) →
        (∀ p ∈ T, 0 ≤ w p ∧ w p ≤ f (Real.log p / Real.log z)) →
        ∑ p ∈ T, w p * (S.nu p / (1 - S.nu p)) ≤
          (∫ x in Set.Ioo (1 / 6) 1, x⁻¹ * f x) + ρ := by
  let C := 12 * L + 36 * B
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 5 * C / (3 * ρ) < m := exists_nat_gt _
  have hmpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hcross : 5 * C < (m : ℝ) * (3 * ρ) := by
    exact (div_lt_iff₀ (mul_pos (by norm_num) hρ)).1 hm
  have hmesh :
      (12 * L + 36 * B) * upperRosserDepthTwoMeshWidth m ≤ ρ / 2 := by
    change C * ((5 / 6 : ℝ) / ((m : ℝ) + 1)) ≤ ρ / 2
    rw [show C * ((5 / 6 : ℝ) / ((m : ℝ) + 1)) =
      (5 * C) / (6 * ((m : ℝ) + 1)) by
        field_simp [hmpos.ne']]
    apply (div_le_iff₀ (mul_pos (by norm_num) hmpos)).2
    nlinarith
  exact exists_weighted_sum_nu_div_one_sub_le_integral_add_of_depthTwoMesh
    m K ρ B L hK hρ hB hL hmesh

end MathlibNt.SieveTheory.SwitchingPrinciple
