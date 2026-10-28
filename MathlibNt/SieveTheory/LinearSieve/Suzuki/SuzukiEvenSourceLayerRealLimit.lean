import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiFiniteSourceLayerEvenLimit

/-!
# Real convergence of the even lower source layers

This module turns the all-depth source/hat comparison proved in the production
Lemma 13.2 development into genuine real summability.  In particular, the
`ENNReal` supremum used by `SuzukiFiniteSourceLayerEvenLimit` is finite whenever
the production Section-13 source contract is available.  No finite scan and no
caller-supplied summable sequence occurs here.
-/

open scoped Classical BigOperators ENNReal
open Finset Filter Topology Set

namespace MathlibNt.SieveTheory

open SuzukiFiniteContinuousLayers
open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false

/-- The production all-depth comparison supplies a single bound for every even
partial sum at a fixed lower-parity coordinate. -/
theorem suzukiEvenSourceLowerPartialSum_bounded_of_sourceContract
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 2 ≤ s) :
    ∃ B : ℝ, ∀ m : ℕ, suzukiEvenSourceLowerPartialSum m s ≤ B := by
  obtain ⟨C, hC, hall⟩ := lemma132_finiteLayerHatUniform_slack hH
  refine ⟨C * s * H.T .minus s, ?_⟩
  intro m
  cases m with
  | zero =>
      simp [suzukiEvenSourceLowerPartialSum]
      exact mul_nonneg
        (mul_nonneg (le_trans (by norm_num) hC) (le_trans (by norm_num) hs))
        (le_of_lt (hH.positive .minus s (by linarith)))
  | succ m =>
      have hEven : Even (2 * (m + 1)) := even_two_mul (m + 1)
      have hdom : s ∈ KappaOneModel.parityDomain 2 (2 * (m + 1)) := by
        simp [KappaOneModel.parityDomain, Nat.even_iff.mp hEven, hs]
      have hbound := hall (2 * (m + 1)) s (by omega) hdom
      rw [ErrorSign.ofDepth_of_even hEven] at hbound
      rw [suzukiEvenSourceLowerPartialSum_eq_finiteSourceLayer]
      have hspos : 0 < s := by linarith
      apply le_of_mul_le_mul_left _ hspos
      calc
        s * finiteSourceLayer 1 2 (2 * (m + 1)) s ≤
            C * s ^ 2 * H.T .minus s := hbound
        _ = s * (C * s * H.T .minus s) := by ring

/-- The actual even lower-layer sequence is summable; the majorization is
produced by the production all-depth source/hat theorem, rather than accepted as
an abstract `Summable` premise. -/
theorem summable_suzukiLayer_one_two_even_of_sourceContract
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 2 ≤ s) :
    Summable (fun k : ℕ => suzukiLayer 1 2 (2 * (k + 1)) s) := by
  obtain ⟨B, hB⟩ :=
    suzukiEvenSourceLowerPartialSum_bounded_of_sourceContract hH hs
  apply summable_of_sum_range_le (fun k => suzukiLayer_one_two_even_nonneg hs k)
  intro m
  simpa [suzukiEvenSourceLowerPartialSum] using hB m

/-- The finite real value of the even lower source-layer series. -/
noncomputable def suzukiEvenSourceLowerLayerLimit (s : ℝ) : ℝ :=
  ∑' k : ℕ, suzukiLayer 1 2 (2 * (k + 1)) s

/-- Real partial sums converge to the genuine `tsum`. -/
theorem tendsto_suzukiEvenSourceLowerPartialSum_real
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 2 ≤ s) :
    Tendsto (fun m => suzukiEvenSourceLowerPartialSum m s) atTop
      (𝓝 (suzukiEvenSourceLowerLayerLimit s)) := by
  exact (summable_suzukiLayer_one_two_even_of_sourceContract hH hs).hasSum.tendsto_sum_nat


end MathlibNt.SieveTheory
