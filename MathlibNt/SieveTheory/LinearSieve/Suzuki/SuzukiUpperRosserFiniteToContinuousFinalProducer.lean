import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperRosserBoundarySourceSuccLayer

/-!
# Unconditional upper Rosser finite-to-continuous producers

The boundary/source successor identity is now produced internally, so the
finite-prefix comparison no longer exposes it as an input.
-/

namespace MathlibNt.SieveTheory.SwitchingPrinciple

noncomputable section

/-- Finite continuous upper Rosser boundary factors are bounded by Suzuki's
continuous upper factor, with the layer identity supplied internally. -/
theorem upperRosserFiniteBoundaryFactor_le_suzukiContinuousUpperFactor_of_source
    (H : SuzukiLemma144KappaOne.Section13HatLayers)
    (hH : SuzukiLemma144KappaOne.Section13HatSourceContract H)
    (L : ℕ) {s : ℝ} (hslo : 3 / 2 ≤ s) (hshi : s ≤ 4) :
    LinearSieve.upperRosserFiniteBoundaryFactor L s ≤
      suzukiContinuousUpperFactor s :=
  upperRosserFiniteBoundaryFactor_le_suzukiContinuousUpperFactor
    H hH LinearSieve.suzukiUpperRosserBoundarySourceSuccLayerIdentity
    L hslo hshi

/-- Fixed-depth mesh comparison landing below the genuine Suzuki upper factor;
the source-layer producer is no longer a caller premise. -/
theorem exists_upperRosserBoundaryPrefix_le_suzukiContinuousUpperFactor_sub_one_add_of_source
    (H : SuzukiLemma144KappaOne.Section13HatLayers)
    (hH : SuzukiLemma144KappaOne.Section13HatSourceContract H)
    (L : ℕ) (K ρ : ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z Δ s : ℝ),
        z₀ ≤ z → 0 < Δ → HasDimensionOneLocalProductBound S K →
        (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
        s = Real.log Δ / Real.log z → 3 / 2 ≤ s → s ≤ 4 →
        ∑ k ∈ Finset.range L,
            ∑ q ∈ S.prodPrimes.primeFactors,
              (S.nu q / (1 - S.nu q)) *
                LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
                  (fun p => S.nu p / (1 - S.nu p)) (Nat.floor Δ + 1) q
                  (S.prodPrimes.primeFactors.filter (fun p => q < p)) k ≤
          suzukiContinuousUpperFactor s - 1 + ρ :=
  exists_upperRosserBoundaryPrefix_le_suzukiContinuousUpperFactor_sub_one_add
    H hH LinearSieve.suzukiUpperRosserBoundarySourceSuccLayerIdentity
    L K ρ hK hρ

/-- Jurkat--Richert rewrite of the unconditional finite-prefix producer. -/
theorem exists_upperRosserBoundaryPrefix_le_jurkatRichertUpperFactor_sub_one_add_of_source
    (H : SuzukiLemma144KappaOne.Section13HatLayers)
    (hH : SuzukiLemma144KappaOne.Section13HatSourceContract H)
    (L : ℕ) (K ρ : ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z Δ s : ℝ),
        z₀ ≤ z → 0 < Δ → HasDimensionOneLocalProductBound S K →
        (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
        s = Real.log Δ / Real.log z → 3 / 2 ≤ s → s ≤ 4 →
        ∑ k ∈ Finset.range L,
            ∑ q ∈ S.prodPrimes.primeFactors,
              (S.nu q / (1 - S.nu q)) *
                LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
                  (fun p => S.nu p / (1 - S.nu p)) (Nat.floor Δ + 1) q
                  (S.prodPrimes.primeFactors.filter (fun p => q < p)) k ≤
          jurkatRichertUpperLinearSieveFactor s - 1 + ρ :=
  exists_upperRosserBoundaryPrefix_le_jurkatRichertUpperFactor_sub_one_add
    H hH LinearSieve.suzukiUpperRosserBoundarySourceSuccLayerIdentity
    L K ρ hK hρ

end

end MathlibNt.SieveTheory.SwitchingPrinciple
