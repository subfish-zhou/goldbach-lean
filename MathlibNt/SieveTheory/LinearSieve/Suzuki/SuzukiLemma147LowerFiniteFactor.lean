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


/-- On a natural cutoff, Suzuki's `V(z)` product is the discrete Euler product
used by the exact lower-Rosser identity. -/
theorem sourceDiscreteEuler_eq_suzukiVProduct_nat
    (S : BoundingSieve) (z : ℕ) :
    sourceDiscreteEuler S z = suzukiVProduct S (z : ℝ) := by
  unfold sourceDiscreteEuler suzukiVProduct suzukiSupportedBelow
  congr 1
  ext p
  simp


end MathlibNt.SieveTheory
