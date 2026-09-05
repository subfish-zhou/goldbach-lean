import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLiteralAllDepthLowerRosserExact

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

/-- The honest finite lower factor attached to an even Suzuki truncation.
This is not the limiting Rosser--Iwaniec factor `F⁻(s)`: identifying the two
requires the even-depth limit in Suzuki (14.29). -/
noncomputable def suzukiFiniteLowerFactor (N : ℕ) (s : ℝ) : ℝ :=
  1 - finiteSourceLayer 1 2 N s

/-- At depth `2*m`, the continuous source layer is exactly the first `m` even
Suzuki layers.  This is the finite normalization preceding the `N → ∞`,
`N ≡ 0 (mod 2)` passage in Suzuki (14.29). -/
theorem finiteSourceLayer_two_mul_eq_sum_evenLayers (m : ℕ) (s : ℝ) :
    finiteSourceLayer 1 2 (2 * m) s =
      ∑ k ∈ Finset.range m, suzukiLayer 1 2 (2 * (k + 1)) s := by
  classical
  have hcarrier :
      (Finset.Icc 1 (2 * m)).filter (fun n => n % 2 = 0) =
        (Finset.range m).image (fun k => 2 * (k + 1)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image,
      Finset.mem_range]
    constructor
    · rintro ⟨⟨hn1, hnm⟩, hnEven⟩
      refine ⟨n / 2 - 1, ?_, ?_⟩
      · omega
      · omega
    · rintro ⟨k, hk, rfl⟩
      constructor <;> omega
  unfold finiteSourceLayer
  rw [Nat.even_iff.mp (even_two_mul m)]
  rw [← Finset.sum_filter]
  rw [hcarrier, Finset.sum_image]
  intro a ha b hb hab
  change 2 * (a + 1) = 2 * (b + 1) at hab
  omega

/-- The finite lower factor is therefore one minus the exact finite sum of the
first `m` even continuous layers. -/
theorem suzukiFiniteLowerFactor_two_mul (m : ℕ) (s : ℝ) :
    suzukiFiniteLowerFactor (2 * m) s =
      1 - ∑ k ∈ Finset.range m, suzukiLayer 1 2 (2 * (k + 1)) s := by
  rw [suzukiFiniteLowerFactor, finiteSourceLayer_two_mul_eq_sum_evenLayers]

/-- On a natural cutoff, Suzuki's `V(z)` product is the discrete Euler product
used by the exact lower-Rosser identity. -/
theorem sourceDiscreteEuler_eq_suzukiVProduct_nat
    (S : BoundingSieve) (z : ℕ) :
    sourceDiscreteEuler S z = suzukiVProduct S (z : ℝ) := by
  unfold sourceDiscreteEuler suzukiVProduct suzukiSupportedBelow
  congr 1
  ext p
  simp

/-- The already closed all-supported lower-Rosser identity and Lemma 14.4 give
an actual finite lower factor, with no discrepancy.  The adaptive depth is used
only for the finite discrete support; the conclusion deliberately retains
`suzukiFiniteLowerFactor N s` and does not identify it with the `N → ∞` factor
`F⁻(s)` from Lemma 14.7. -/
theorem exists_lowerRosserDensity_finiteLowerFactor_of_suzuki_literal_allDepth
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
                    (suzukiFiniteLowerFactor N s -
                      C * Real.exp (Real.sqrt K) *
                        errorEnvelope H N (D : ℝ) d s *
                          (Real.log (D : ℝ)) ^ (-Δ)) ≤
                  lowerRosserSetDensitySum S.nu D (suzukiSupportedBelow S z) := by
  obtain ⟨C1min, hC1min, hbound⟩ :=
    exists_lowerRosserDensity_exact_bound_of_suzuki_literal_allDepth S H hH hsrc
  refine ⟨C1min, hC1min, ?_⟩
  intro C1 hC1
  obtain ⟨C145, Clow, C, hC145, hClow, hC, hall⟩ := hbound C1 hC1
  refine ⟨C145, Clow, C, hC145, hClow, hC, ?_⟩
  intro K hK hlocal D hD s hs hsSigma hz2
  let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
  let N : ℕ := 2 * ((suzukiSupportedBelow S z).card + 1)
  have h := hall K hK hlocal D hD s hs hsSigma hz2
  have hEuler := sourceDiscreteEuler_eq_suzukiVProduct_nat S z
  dsimp only [z, N] at h ⊢
  rw [suzukiFiniteLowerFactor]
  rw [hEuler] at h
  linarith


end MathlibNt.SieveTheory
