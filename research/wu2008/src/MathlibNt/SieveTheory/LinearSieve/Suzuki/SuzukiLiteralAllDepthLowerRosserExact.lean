import MathlibNt.SieveTheory.LinearSieve.Rosser.LowerRosserAccumulatorNormalization
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSourceToLowerRosserDensityTransport
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144LiteralAllDepth

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

/-- Once the even depth contains every supported pair-depth, the lower-Rosser
density is exactly the finite Euler product minus Suzuki's actual parity sum.
The depth depends on the finite carrier, but the identity has no limiting or
fixed-depth approximation. -/
theorem lowerRosserSetDensitySum_eq_euler_sub_suzukiActualT_all_supported
    (S : BoundingSieve) {D z : ℕ} (hD1 : 1 < D) (hzD : z ≤ D) :
    lowerRosserSetDensitySum S.nu D (suzukiSupportedBelow S z) =
      sourceDiscreteEuler S z -
        suzukiActualT S (2 * ((suzukiSupportedBelow S z).card + 1)) D z := by
  let qs := suzukiSupportedBelowList S z
  have hcarrier : qs.toFinset = suzukiSupportedBelow S z := by
    exact suzukiSupportedBelowList_toFinset S z
  have hprime : ∀ q ∈ qs, q.Prime := by
    intro q hq
    have hq' : q ∈ suzukiSupportedBelow S z := by
      rw [← hcarrier]
      exact List.mem_toFinset.mpr hq
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq').1
  have hqD : ∀ q ∈ qs, q < D := by
    intro q hq
    have hq' : q ∈ suzukiSupportedBelow S z := by
      rw [← hcarrier]
      exact List.mem_toFinset.mpr hq
    exact (Finset.mem_filter.mp hq').2.trans_le hzD
  have hordered : qs.Pairwise (· < ·) := by
    exact (Finset.sortedLT_sort (suzukiSupportedBelow S z)).pairwise
  rw [lowerRosserSetDensitySum_eq_euler_sub_boundaryAccum S qs hcarrier
    hprime hqD hordered hD1]
  rw [← suzukiActualT_all_supported_depths_eq_lowerRosserBoundaryAccum
    S D z hzD]

/-- Direct lower-Rosser density consequence of the literal all-depth Suzuki
headline.  The adaptive even depth is legal because the headline's constants
are uniform over every natural depth.  No discrepancy or depth limit remains. -/
theorem exists_lowerRosserDensity_exact_bound_of_suzuki_literal_allDepth
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
                sourceDiscreteEuler S z -
                    suzukiVProduct S (z : ℝ) *
                      (finiteSourceLayer 1 2 N s +
                        C * Real.exp (Real.sqrt K) *
                          errorEnvelope H N (D : ℝ) d s *
                            (Real.log (D : ℝ)) ^ (-Δ)) ≤
                  lowerRosserSetDensitySum S.nu D (suzukiSupportedBelow S z) := by
  obtain ⟨C1min, hC1min, hheadline⟩ :=
    exists_lemma14_4_literal_allDepth_with_lowStrip_extension S H hH hsrc
  refine ⟨C1min, hC1min, ?_⟩
  intro C1 hC1
  obtain ⟨C145, Clow, C, hC145, hClow, hC3, hall⟩ := hheadline C1 hC1
  refine ⟨C145, Clow, C, hC145, hClow, hC3, ?_⟩
  intro K hK hlocal D hD s hs hsSigma hz2
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
  have hSuzuki := hall K hK hlocal N hN1 D (by omega) hD s hsdom hsSigma hz2
  have hdensity := lowerRosserSetDensitySum_eq_euler_sub_suzukiActualT_all_supported
    S (show 1 < D by omega) hzD
  dsimp only [z, N] at hSuzuki ⊢
  rw [hdensity]
  linarith


end MathlibNt.SieveTheory
