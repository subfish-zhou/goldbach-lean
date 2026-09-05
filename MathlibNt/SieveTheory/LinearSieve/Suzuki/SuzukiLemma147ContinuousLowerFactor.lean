import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLowerSieveFactorFirstIntervalIdentity

/-!
# Suzuki Lemma 14.7: continuous lower factor on the first interval

This module upgrades the finite-factor lower Rosser density estimate to the
actual first-interval continuous factor.  It uses only the one-sided fact that
the carrier-adaptive finite even source sum is bounded by the full summable
source series.  In particular, it makes no claim that an adaptive finite depth
is itself a limit.
-/

open scoped Classical BigOperators Interval
open Finset

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false

/-- Every carrier-adaptive finite even source layer is bounded by the genuine
summable lower source series `T⁻(s)`. -/
theorem finiteSourceLayer_adaptive_le_suzukiProposition118SourceTMinus
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {α : Type*} (carrier : Finset α) {s : ℝ} (hs : 2 ≤ s) :
    finiteSourceLayer 1 2 (2 * (carrier.card + 1)) s ≤
      suzukiProposition118SourceTMinus s := by
  rw [finiteSourceLayer_two_mul_eq_sum_evenLayers]
  unfold suzukiProposition118SourceTMinus
  exact
    (summable_suzukiProposition118SourceTMinus_of_sourceContract hH hs).sum_le_tsum
      (Finset.range (carrier.card + 1))
      (fun k _ => suzukiLayer_one_two_even_nonneg hs k)

/-- On `2 ≤ s ≤ 4`, the actual first-interval continuous lower factor is no
larger than every carrier-adaptive finite lower factor. -/
theorem suzukiLowerSieveFactorFirstInterval_le_adaptive_finiteLowerFactor
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {α : Type*} (carrier : Finset α) {s : ℝ}
    (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    suzukiLowerSieveFactorFirstInterval s ≤
      suzukiFiniteLowerFactor (2 * (carrier.card + 1)) s := by
  have htail :=
    finiteSourceLayer_adaptive_le_suzukiProposition118SourceTMinus
      hH carrier hs2
  rw [suzukiFiniteLowerFactor]
  rw [← one_sub_suzukiProposition118SourceTMinus_eq_lowerSieveFactorFirstInterval
    hH hs2 hs4]
  linarith

/-- Lemma 14.7 on its first lower interval, in the production lower-Rosser
quantifier order.  Relative to the finite theorem, only the factor is replaced:
`suzukiFiniteLowerFactor N s` becomes the genuine explicit continuous factor
`suzukiLowerSieveFactorFirstInterval s`; the error term and adaptive depth `N`
are unchanged. -/
theorem exists_lowerRosserDensity_continuousLowerFactorFirstInterval_of_suzuki_literal_allDepth
    (S : BoundingSieve) (H : Section13HatLayers)
    {d Δ Θ : ℝ}
    (hH : Section13HatSourceContract H)
    (hsrc : SuzukiClaim145SourceParameters d Δ Θ) :
    ∃ C1min : ℝ, 0 < C1min ∧
      ∀ C1 : ℝ, C1min ≤ C1 →
        ∃ C145 Clow C : ℝ,
          0 < C145 ∧ 0 ≤ Clow ∧ 3 ≤ C ∧
          ∀ K : ℝ, 2 ≤ K → HasDimensionOneLocalProductBound S K →
            ∀ D : ℕ, 2 ≤ D →
              ∀ s : ℝ, 2 ≤ s → s ≤ 4 →
                s ≤ sourceSigma (D : ℝ) d →
                2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊ →
                let z := ⌈(D : ℝ) ^ (1 / s)⌉₊
                let N := 2 * ((suzukiSupportedBelow S z).card + 1)
                suzukiVProduct S (z : ℝ) *
                    (suzukiLowerSieveFactorFirstInterval s -
                      C * Real.exp (Real.sqrt K) *
                        errorEnvelope H N (D : ℝ) d s *
                          (Real.log (D : ℝ)) ^ (-Δ)) ≤
                  lowerRosserSetDensitySum S.nu D (suzukiSupportedBelow S z) := by
  obtain ⟨C1min, hC1min, hbound⟩ :=
    exists_lowerRosserDensity_finiteLowerFactor_of_suzuki_literal_allDepth
      S H hH hsrc
  refine ⟨C1min, hC1min, ?_⟩
  intro C1 hC1
  obtain ⟨C145, Clow, C, hC145, hClow, hC, hall⟩ := hbound C1 hC1
  refine ⟨C145, Clow, C, hC145, hClow, hC, ?_⟩
  intro K hK hlocal D hD s hs2 hs4 hsSigma hz2
  let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
  let N : ℕ := 2 * ((suzukiSupportedBelow S z).card + 1)
  have hfinite := hall K hK hlocal D hD s hs2 hsSigma hz2
  have hfactor :
      suzukiLowerSieveFactorFirstInterval s ≤ suzukiFiniteLowerFactor N s := by
    dsimp only [N]
    exact suzukiLowerSieveFactorFirstInterval_le_adaptive_finiteLowerFactor
      hH (suzukiSupportedBelow S z) hs2 hs4
  have hV : 0 ≤ suzukiVProduct S (z : ℝ) :=
    (suzukiVProduct_pos S (z : ℝ)).le
  dsimp only [z, N] at hfinite ⊢
  have hbracket := sub_le_sub_right hfactor
    (C * Real.exp (Real.sqrt K) *
      errorEnvelope H (2 * ((suzukiSupportedBelow S z).card + 1))
        (D : ℝ) d s * (Real.log (D : ℝ)) ^ (-Δ))
  exact (mul_le_mul_of_nonneg_left hbracket hV).trans hfinite


end MathlibNt.SieveTheory
