import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperRosserDensityFinalBridge

/-!
# Scale-faithful quantitative joint diagonal for the upper Rosser density

This module records the minimal quantifier-correct strengthening of the current
fixed-depth mesh and absolute aggregate-tail producers.  Both estimates retain
the ambient Euler product.  In particular, no cancellation or division by that
product is used.

The current fixed-depth proof does not itself provide the two contracts below.
Its depth-`k+1` screen is `c = 1 / (2 * 3^(k+1))`, its displayed majorant is
`B = c⁻¹ * (c⁻¹ * c⁻¹)^(k+1)`, and its uniform-continuity modulus is selected
nonquantitatively.  Thus the source currently exposes no bound for `z₀(k, ε)`
that can be checked at a moving depth such as `k ≍ log log z`.
-/

namespace MathlibNt.SieveTheory.SwitchingPrinciple

noncomputable section

def upperRosserRelativePrefix
    (S : BoundingSieve) (Δ : ℝ) (T : ℕ) : ℝ :=
  ∑ q ∈ S.prodPrimes.primeFactors,
    (S.nu q / (1 - S.nu q)) *
      ∑ k ∈ Finset.range T,
        LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
          S.nu (Nat.floor Δ + 1) q
          (S.prodPrimes.primeFactors.filter (fun p => q < p)) k

def upperRosserRelativeTail
    (S : BoundingSieve) (Δ : ℝ) (T : ℕ) : ℝ :=
  ∑ q ∈ S.prodPrimes.primeFactors,
    (S.nu q / (1 - S.nu q)) *
      ∑ j ∈ Finset.range
          (S.prodPrimes.primeFactors.card + 1 - T),
        LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
          S.nu (Nat.floor Δ + 1) q
          (S.prodPrimes.primeFactors.filter (fun p => q < p)) (T + j)

def upperRosserEulerScale (S : BoundingSieve) : ℝ :=
  AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S

/-- Fixed-depth prefix comparison in the exact relative coordinates of the
finite decomposition.  The threshold may depend on the selected depth, but is
chosen before the varying sieve and endpoint. -/
def UpperRosserScaledFixedDepthPrefixProducer
    (H : SuzukiLemma144KappaOne.Section13HatLayers)
    (_hH : SuzukiLemma144KappaOne.Section13HatSourceContract H) : Prop :=
  ∀ K ε : ℝ, 1 < K → 0 < ε → ∀ T : ℕ,
    ∃ z₀ : ℝ, ∀ (S : BoundingSieve) (z Δ s : ℝ),
      z₀ ≤ z → 2 ≤ z → 0 < Δ →
      HasDimensionOneLocalProductBound S K →
      (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
      s = Real.log Δ / Real.log z → 3 / 2 ≤ s → s ≤ 4 →
      let T' := min T (S.prodPrimes.primeFactors.card + 1)
      (1 + upperRosserRelativePrefix S Δ T') * upperRosserEulerScale S ≤
        (jurkatRichertUpperLinearSieveFactor s + ε) * upperRosserEulerScale S

/-- Uniform relative-tail producer.  Unlike the existing absolute estimate
`tail * V ≤ τ(T)`, this conclusion is already at the required `ε * V` scale.
The same fixed depth works for every later sieve and endpoint. -/
def UpperRosserScaledRelativeTailProducer : Prop :=
  ∀ K ε : ℝ, 1 < K → 0 < ε →
    ∃ T : ℕ, ∃ z₀ : ℝ, ∀ (S : BoundingSieve) (z Δ s : ℝ),
      z₀ ≤ z → 2 ≤ z → 0 < Δ →
      HasDimensionOneLocalProductBound S K →
      (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
      s = Real.log Δ / Real.log z → 3 / 2 ≤ s → s ≤ 4 →
      let T' := min T (S.prodPrimes.primeFactors.card + 1)
      upperRosserRelativeTail S Δ T' * upperRosserEulerScale S ≤
        ε * upperRosserEulerScale S

/-- The two scale-faithful producers close the frozen final interface.  The tail
chooses the depth first; the fixed-depth prefix theorem is then invoked at that
same depth, and the two endpoint thresholds are joined by a maximum. -/
theorem UpperRosserScaledPrefixTailComparison.of_scaleFaithfulProducers
    (H : SuzukiLemma144KappaOne.Section13HatLayers)
    (hH : SuzukiLemma144KappaOne.Section13HatSourceContract H)
    (hprefix : UpperRosserScaledFixedDepthPrefixProducer H hH)
    (htail : UpperRosserScaledRelativeTailProducer) :
    UpperRosserScaledPrefixTailComparison H hH := by
  intro K ρ hK hρ
  have hρ2 : 0 < ρ / 2 := half_pos hρ
  obtain ⟨T, zTail, hTail⟩ := htail K (ρ / 2) hK hρ2
  obtain ⟨zPrefix, hPrefix⟩ := hprefix K (ρ / 2) hK hρ2 T
  refine ⟨T, max zTail zPrefix, ?_⟩
  intro S z Δ s hz₀ hz hΔ hlocal hcut hs hslo hshi
  let T' := min T (S.prodPrimes.primeFactors.card + 1)
  have hp := hPrefix S z Δ s ((le_max_right _ _).trans hz₀)
    hz hΔ hlocal hcut hs hslo hshi
  have ht := hTail S z Δ s ((le_max_left _ _).trans hz₀)
    hz hΔ hlocal hcut hs hslo hshi
  simp only [upperRosserRelativePrefix, upperRosserRelativeTail,
    upperRosserEulerScale] at hp ht ⊢
  rw [add_mul]
  have hsum := add_le_add hp ht
  nlinarith

/-- An arbitrarily small absolute error does not pay the same relative error at
an independently shrinking positive scale.  Taking `V = τ/2` and `E = τ`
models exactly why `E ≤ τ` cannot be promoted to `E ≤ V` uniformly. -/
theorem absoluteTailBound_does_not_imply_relativeScale :
    ∀ τ : ℝ, 0 < τ →
      ∃ V E : ℝ, 0 < V ∧ 0 ≤ E ∧ E ≤ τ ∧ ¬ E ≤ V := by
  intro τ hτ
  refine ⟨τ / 2, τ, half_pos hτ, hτ.le, le_rfl, ?_⟩
  linarith


end

end MathlibNt.SieveTheory.SwitchingPrinciple
