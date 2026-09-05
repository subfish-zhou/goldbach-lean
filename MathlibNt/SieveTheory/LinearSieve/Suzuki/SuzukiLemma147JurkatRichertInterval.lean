import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperSourcePTail
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma147LowerFiniteFactor
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144LiteralAllDepthUniformInS

/-!
# Suzuki Lemma 14.7 on the Jurkat--Richert interval

This module passes from the exact finite lower factor supplied by the literal
all-depth theorem to Suzuki's canonical continuous factor.  The comparison uses
only nonnegativity and summability of the even source layers, so it is valid on
the full legal range `2 ≤ s`.  On `4 ≤ s ≤ 6`, the source normalization theorem
then identifies that factor with the standard dimension-one Jurkat--Richert
factor.  The adaptive depth and the complete error term are unchanged.
-/

open scoped Classical BigOperators Interval
open Finset

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false

/-- On the full legal source range, Suzuki's canonical continuous lower factor
is bounded above by every carrier-adaptive finite lower factor. -/
theorem suzukiContinuousLowerFactor_le_adaptive_finiteLowerFactor
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {α : Type*} (carrier : Finset α) {s : ℝ} (hs : 2 ≤ s) :
    suzukiContinuousLowerFactor s ≤
      suzukiFiniteLowerFactor (2 * (carrier.card + 1)) s := by
  have htail :=
    finiteSourceLayer_adaptive_le_suzukiProposition118SourceTMinus
      hH carrier hs
  rw [suzukiContinuousLowerFactor, suzukiContinuousLowerTail,
    suzukiFiniteLowerFactor]
  linarith

/-- Uniform-in-sieve form of Lemma 14.7 with Suzuki's canonical continuous
lower factor.  In particular, all four constants are selected before `S`.
The proof consumes the uniform literal all-depth Lemma 14.4 directly. -/
theorem exists_lowerRosserDensity_continuousLowerFactor_of_suzuki_literal_allDepth_uniform_in_S_of_source
    (H : Section13HatLayers)
    {d Δ Θ : ℝ}
    (hH : Section13HatSourceContract H)
    (hsrc : SuzukiClaim145SourceParameters d Δ Θ) :
    ∃ C1min : ℝ, 0 < C1min ∧
      ∀ C1 : ℝ, C1min ≤ C1 →
        ∃ C145 Clow C : ℝ,
          0 < C145 ∧ 0 ≤ Clow ∧ 3 ≤ C ∧
          ∀ (S : BoundingSieve) (K : ℝ),
            2 ≤ K → HasDimensionOneLocalProductBound S K →
            ∀ D : ℕ, 2 ≤ D →
              ∀ s : ℝ, 2 ≤ s → s ≤ sourceSigma (D : ℝ) d →
                2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊ →
                let z := ⌈(D : ℝ) ^ (1 / s)⌉₊
                let N := 2 * ((suzukiSupportedBelow S z).card + 1)
                suzukiVProduct S (z : ℝ) *
                    (suzukiContinuousLowerFactor s -
                      C * Real.exp (Real.sqrt K) *
                        errorEnvelope H N (D : ℝ) d s *
                          (Real.log (D : ℝ)) ^ (-Δ)) ≤
                  lowerRosserSetDensitySum S.nu D (suzukiSupportedBelow S z) := by
  obtain ⟨C1min, hC1min, hheadline⟩ :=
    exists_lemma14_4_movingRange_rounded_allDepth_uniform_in_S_of_source
      H hH hsrc
  refine ⟨C1min, hC1min, ?_⟩
  intro C1 hC1
  obtain ⟨C145, Clow, C, hC145, hClow, hC3, hall⟩ := hheadline C1 hC1
  refine ⟨C145, Clow, C, hC145, hClow, hC3, ?_⟩
  intro S K hK hlocal D hD s hs hsSigma hz2
  let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
  let N : ℕ := 2 * ((suzukiSupportedBelow S z).card + 1)
  have hNeven : Even N := by
    dsimp [N]
    exact even_two_mul _
  have hN1 : 1 ≤ N := by
    dsimp [N]
    omega
  have hsdom : s ∈ KappaOneModel.parityDomain 2 N := by
    simp [KappaOneModel.parityDomain, Nat.even_iff.mp hNeven, hs]
  have hzD : z ≤ D := by
    dsimp [z]
    exact natCeil_rpow_le_self_on_parityDomain hD hsdom
  have hSuzuki := hall S K hK hlocal N hN1 D (by omega) hD s hsdom hsSigma hz2
  have hdensity := lowerRosserSetDensitySum_eq_euler_sub_suzukiActualT_all_supported
    S (show 1 < D by omega) hzD
  have hEuler := sourceDiscreteEuler_eq_suzukiVProduct_nat S z
  have hfactor :
      suzukiContinuousLowerFactor s ≤ suzukiFiniteLowerFactor N s := by
    dsimp only [N]
    exact suzukiContinuousLowerFactor_le_adaptive_finiteLowerFactor
      hH (suzukiSupportedBelow S z) hs
  have hV : 0 ≤ suzukiVProduct S (z : ℝ) :=
    (suzukiVProduct_pos S (z : ℝ)).le
  have hfactorV := mul_le_mul_of_nonneg_left hfactor hV
  dsimp only [z, N] at hSuzuki hdensity hEuler hfactorV ⊢
  rw [suzukiFiniteLowerFactor] at hfactorV
  rw [hdensity, hEuler]
  linarith

/-- Uniform-in-sieve Suzuki Lemma 14.7 on `4 ≤ s ≤ 6`, with the standard
dimension-one Jurkat--Richert lower factor. -/
theorem exists_lowerRosserDensity_dimensionOneLowerFactor_of_suzuki_literal_allDepth_uniform_in_S_of_source
    (H : Section13HatLayers)
    {d Δ Θ : ℝ}
    (hH : Section13HatSourceContract H)
    (hsrc : SuzukiClaim145SourceParameters d Δ Θ) :
    ∃ C1min : ℝ, 0 < C1min ∧
      ∀ C1 : ℝ, C1min ≤ C1 →
        ∃ C145 Clow C : ℝ,
          0 < C145 ∧ 0 ≤ Clow ∧ 3 ≤ C ∧
          ∀ (S : BoundingSieve) (K : ℝ),
            2 ≤ K → HasDimensionOneLocalProductBound S K →
            ∀ D : ℕ, 2 ≤ D →
              ∀ s : ℝ, 4 ≤ s → s ≤ 6 →
                s ≤ sourceSigma (D : ℝ) d →
                2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊ →
                let z := ⌈(D : ℝ) ^ (1 / s)⌉₊
                let N := 2 * ((suzukiSupportedBelow S z).card + 1)
                suzukiVProduct S (z : ℝ) *
                    (SwitchingPrinciple.dimensionOneLowerLinearSieveFactor s -
                      C * Real.exp (Real.sqrt K) *
                        errorEnvelope H N (D : ℝ) d s *
                          (Real.log (D : ℝ)) ^ (-Δ)) ≤
                  lowerRosserSetDensitySum S.nu D (suzukiSupportedBelow S z) := by
  obtain ⟨C1min, hC1min, hbound⟩ :=
    exists_lowerRosserDensity_continuousLowerFactor_of_suzuki_literal_allDepth_uniform_in_S_of_source
      H hH hsrc
  refine ⟨C1min, hC1min, ?_⟩
  intro C1 hC1
  obtain ⟨C145, Clow, C, hC145, hClow, hC, hall⟩ := hbound C1 hC1
  refine ⟨C145, Clow, C, hC145, hClow, hC, ?_⟩
  intro S K hK hlocal D hD s hs4 hs6 hsSigma hz2
  have h := hall S K hK hlocal D hD s (by linarith) hsSigma hz2
  rw [suzukiContinuousLowerFactor_eq_dimensionOne_of_sourceContract
    hH hs4 hs6] at h
  exact h

/-- Lemma 14.7 with the canonical continuous lower factor on every legal source
coordinate.  Relative to the finite theorem, only the factor is strengthened;
the quantifier order, adaptive depth, and error envelope are preserved exactly. -/
theorem exists_lowerRosserDensity_continuousLowerFactor_of_suzuki_literal_allDepth
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
              ∀ s : ℝ, 2 ≤ s → s ≤ sourceSigma (D : ℝ) d →
                2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊ →
                let z := ⌈(D : ℝ) ^ (1 / s)⌉₊
                let N := 2 * ((suzukiSupportedBelow S z).card + 1)
                suzukiVProduct S (z : ℝ) *
                    (suzukiContinuousLowerFactor s -
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
  intro K hK hlocal D hD s hs hsSigma hz2
  let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
  let N : ℕ := 2 * ((suzukiSupportedBelow S z).card + 1)
  have hfinite := hall K hK hlocal D hD s hs hsSigma hz2
  have hfactor :
      suzukiContinuousLowerFactor s ≤ suzukiFiniteLowerFactor N s := by
    dsimp only [N]
    exact suzukiContinuousLowerFactor_le_adaptive_finiteLowerFactor
      hH (suzukiSupportedBelow S z) hs
  have hV : 0 ≤ suzukiVProduct S (z : ℝ) :=
    (suzukiVProduct_pos S (z : ℝ)).le
  dsimp only [z, N] at hfinite ⊢
  have hbracket := sub_le_sub_right hfactor
    (C * Real.exp (Real.sqrt K) *
      errorEnvelope H (2 * ((suzukiSupportedBelow S z).card + 1))
        (D : ℝ) d s * (Real.log (D : ℝ)) ^ (-Δ))
  exact (mul_le_mul_of_nonneg_left hbracket hV).trans hfinite

/-- Suzuki Lemma 14.7 on the Chen/Jurkat--Richert interval `4 ≤ s ≤ 6`.
The conclusion has the standard dimension-one lower factor, with precisely the
same constants, adaptive depth, and error term as the all-depth finite theorem. -/
theorem exists_lowerRosserDensity_dimensionOneLowerFactor_of_suzuki_literal_allDepth
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
              ∀ s : ℝ, 4 ≤ s → s ≤ 6 →
                s ≤ sourceSigma (D : ℝ) d →
                2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊ →
                let z := ⌈(D : ℝ) ^ (1 / s)⌉₊
                let N := 2 * ((suzukiSupportedBelow S z).card + 1)
                suzukiVProduct S (z : ℝ) *
                    (SwitchingPrinciple.dimensionOneLowerLinearSieveFactor s -
                      C * Real.exp (Real.sqrt K) *
                        errorEnvelope H N (D : ℝ) d s *
                          (Real.log (D : ℝ)) ^ (-Δ)) ≤
                  lowerRosserSetDensitySum S.nu D (suzukiSupportedBelow S z) := by
  obtain ⟨C1min, hC1min, hbound⟩ :=
    exists_lowerRosserDensity_continuousLowerFactor_of_suzuki_literal_allDepth
      S H hH hsrc
  refine ⟨C1min, hC1min, ?_⟩
  intro C1 hC1
  obtain ⟨C145, Clow, C, hC145, hClow, hC, hall⟩ := hbound C1 hC1
  refine ⟨C145, Clow, C, hC145, hClow, hC, ?_⟩
  intro K hK hlocal D hD s hs4 hs6 hsSigma hz2
  have h := hall K hK hlocal D hD s (by linarith) hsSigma hz2
  rw [suzukiContinuousLowerFactor_eq_dimensionOne_of_sourceContract
    hH hs4 hs6] at h
  exact h


end MathlibNt.SieveTheory
