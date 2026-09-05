/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperRosserDensityProducer

/-!
# Finite-to-continuous upper Rosser producer

This module isolates the normalization bridge between the finite continuous
boundary factors already used by the upper Rosser mesh argument and Suzuki's
actual odd source series.  It does not assume an upper-density conclusion.
-/

namespace MathlibNt.SieveTheory

open MeasureTheory Set
open SuzukiFiniteContinuousLayers

noncomputable section

/-- Exact layerwise normalization required to identify the continuous Rosser
boundary recursion with Suzuki's odd source layers.  This is strictly a source
identity: it mentions neither a `BoundingSieve` nor a Rosser-density bound. -/
def SuzukiUpperRosserBoundarySourceLayerIdentity : Prop :=
  ∀ (k : ℕ) (s : ℝ), 3 / 2 ≤ s → s ≤ 4 →
    (∫ a in Set.Ioo 0 1,
      a⁻¹ * a⁻¹ * LinearSieve.upperRosserBoundaryMass k s a) =
      suzukiLayer 1 2 (2 * k + 1) s

/-- The genuinely recursive residual after the first odd source layer has been
identified.  Its indexing starts at Rosser pair-depth one / Suzuki source index
three, so the already closed depth-zero shell is not hidden in the interface. -/
def SuzukiUpperRosserBoundarySourceSuccLayerIdentity : Prop :=
  ∀ (k : ℕ) (s : ℝ), 3 / 2 ≤ s → s ≤ 4 →
    (∫ a in Set.Ioo 0 1,
      a⁻¹ * a⁻¹ * LinearSieve.upperRosserBoundaryMass (k + 1) s a) =
      suzukiLayer 1 2 (2 * (k + 1) + 1) s

/-- The outer cubic shell is exactly Suzuki's first odd source layer. -/
theorem upperRosserBoundarySourceLayerIdentity_zero
    {s : ℝ} (hs : 0 < s) :
    (∫ a in Set.Ioo 0 1,
      a⁻¹ * a⁻¹ * LinearSieve.upperRosserBoundaryMass 0 s a) =
      suzukiLayer 1 2 1 s := by
  by_cases hs3 : s < 3
  · rw [LinearSieve.integral_upperRosserBoundaryMass_zero hs hs3,
      suzukiLayer_one]
    rw [show baseLower 2 s = s by
      unfold baseLower
      exact min_eq_left (by norm_num; linarith)]
    simp [dPowDensity]
    field_simp [hs.ne']
    ring
  · have h3s : (3 : ℝ) ≤ s := le_of_not_gt hs3
    rw [LinearSieve.integral_upperRosserBoundaryMass_eq_zero_of_pow_le 0 (by
      norm_num at h3s ⊢
      exact h3s),
      suzukiLayer_eq_zero_of_le 1 2 1 (by norm_num at h3s ⊢; exact h3s)]

/-- Closing the positive pair-depth recursion is now exactly sufficient for the
full layerwise identity; depth zero is discharged by the cubic-shell theorem. -/
theorem SuzukiUpperRosserBoundarySourceLayerIdentity.of_succ
    (h : SuzukiUpperRosserBoundarySourceSuccLayerIdentity) :
    SuzukiUpperRosserBoundarySourceLayerIdentity := by
  intro k s hslo hshi
  cases k with
  | zero =>
      exact upperRosserBoundarySourceLayerIdentity_zero (by linarith)
  | succ k =>
      simpa [Nat.succ_eq_add_one] using h k s hslo hshi

namespace SwitchingPrinciple

/-- Every finite continuous boundary prefix is bounded by Suzuki's genuine
continuous upper factor.  The proof uses the actual summability supplied by the
Section-13 source contract and leaves the adaptive discrete depth untouched. -/
theorem upperRosserFiniteBoundaryFactor_le_suzukiContinuousUpperFactor
    (H : SuzukiLemma144KappaOne.Section13HatLayers)
    (hH : SuzukiLemma144KappaOne.Section13HatSourceContract H)
    (hlayerSucc : SuzukiUpperRosserBoundarySourceSuccLayerIdentity)
    (L : ℕ) {s : ℝ} (hslo : 3 / 2 ≤ s) (hshi : s ≤ 4) :
    LinearSieve.upperRosserFiniteBoundaryFactor L s ≤
      suzukiContinuousUpperFactor s := by
  have hlayer : SuzukiUpperRosserBoundarySourceLayerIdentity :=
    SuzukiUpperRosserBoundarySourceLayerIdentity.of_succ hlayerSucc
  have hs1 : 1 < s := by linarith
  have hsum :=
    summable_suzukiProposition118SourceTPlus_of_sourceContract hH hs1
  have hpartial :
      (∑ k ∈ Finset.range L,
        ∫ a in Set.Ioo 0 1,
          a⁻¹ * a⁻¹ * LinearSieve.upperRosserBoundaryMass k s a) ≤
        suzukiProposition118SourceTPlus s := by
    rw [show (∑ k ∈ Finset.range L,
        ∫ a in Set.Ioo 0 1,
          a⁻¹ * a⁻¹ * LinearSieve.upperRosserBoundaryMass k s a) =
      ∑ k ∈ Finset.range L, suzukiLayer 1 2 (2 * k + 1) s by
        apply Finset.sum_congr rfl
        intro k hk
        exact hlayer k s hslo hshi]
    unfold suzukiProposition118SourceTPlus
    exact hsum.sum_le_tsum (Finset.range L)
      (fun k hk => suzukiLayer_one_two_odd_nonneg hs1 k)
  unfold LinearSieve.upperRosserFiniteBoundaryFactor
    suzukiContinuousUpperFactor
  linarith

/-- The existing fixed-depth mesh estimates therefore land directly below the
actual continuous upper source factor, with one cutoff selected before the
sieve.  No density fundamental lemma is used as an input. -/
theorem
    exists_upperRosserBoundaryPrefix_le_suzukiContinuousUpperFactor_sub_one_add
    (H : SuzukiLemma144KappaOne.Section13HatLayers)
    (hH : SuzukiLemma144KappaOne.Section13HatSourceContract H)
    (hlayerSucc : SuzukiUpperRosserBoundarySourceSuccLayerIdentity)
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
          suzukiContinuousUpperFactor s - 1 + ρ := by
  obtain ⟨z₀, hz₀, hprefix⟩ :=
    exists_sum_range_sum_mul_upperRosserBoundaryChainsFixedDepthDensity_le_upperRosserFiniteBoundaryFactor_sub_one_add
      L K ρ hK hρ
  refine ⟨z₀, hz₀, ?_⟩
  intro S z Δ s hz hΔ hlocal hcut hs hslo hshi
  have hfinite := hprefix S z Δ s hz hΔ hlocal hcut hs hslo hshi
  have hcontinuous :=
    upperRosserFiniteBoundaryFactor_le_suzukiContinuousUpperFactor
      H hH hlayerSucc L hslo hshi
  linarith

/-- Jurkat--Richert rewrite of the finite-prefix producer.  The genuine source
contract now supplies both the source-factor identity and its amplitude. -/
theorem
    exists_upperRosserBoundaryPrefix_le_jurkatRichertUpperFactor_sub_one_add
    (H : SuzukiLemma144KappaOne.Section13HatLayers)
    (hH : SuzukiLemma144KappaOne.Section13HatSourceContract H)
    (hlayerSucc : SuzukiUpperRosserBoundarySourceSuccLayerIdentity)
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
          jurkatRichertUpperLinearSieveFactor s - 1 + ρ := by
  obtain ⟨z₀, hz₀, hprefix⟩ :=
    exists_upperRosserBoundaryPrefix_le_suzukiContinuousUpperFactor_sub_one_add
      H hH hlayerSucc L K ρ hK hρ
  refine ⟨z₀, hz₀, ?_⟩
  intro S z Δ s hz hΔ hlocal hcut hs hslo hshi
  rw [← suzukiContinuousUpperFactor_eq_jurkatRichertUpperLinearSieveFactor_of_sourceContract
    H hH hslo hshi]
  exact hprefix S z Δ s hz hΔ hlocal hcut hs hslo hshi

end SwitchingPrinciple
end


end MathlibNt.SieveTheory
