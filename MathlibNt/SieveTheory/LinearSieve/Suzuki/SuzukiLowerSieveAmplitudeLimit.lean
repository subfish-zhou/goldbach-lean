import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiEvenSourceLayerRealLimit
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLowerSieveFactorEvenLimitBridge

/-!
# Convergence of Suzuki's finite lower amplitude

The same all-depth Lemma 13.2 source contract that bounds the even lower layers
also bounds the odd source layers at `s = 3`.  Hence their partial sums converge
to the `tsum` occurring in Suzuki's canonical first-interval amplitude.  This
closes the `A_m - A` term in the finite residual decomposition.
-/

open scoped Classical BigOperators
open Finset Filter Topology

namespace MathlibNt.SieveTheory

open SuzukiFiniteContinuousLayers
open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false

/-- Adding one term to the odd source partial sum. -/
theorem suzukiOddSourceUpperPartialSum_succ (m : ℕ) (s : ℝ) :
    suzukiOddSourceUpperPartialSum (m + 1) s =
      suzukiOddSourceUpperPartialSum m s + suzukiLayer 1 2 (2 * m + 1) s := by
  unfold suzukiOddSourceUpperPartialSum
  rw [Finset.sum_range_succ]

/-- The odd source layer at depth `2m+1` is exactly the first `m+1` odd
continuous layers. -/
theorem finiteSourceLayer_two_mul_add_one_eq_oddPartialSum
    (m : ℕ) (s : ℝ) :
    finiteSourceLayer 1 2 (2 * m + 1) s =
      suzukiOddSourceUpperPartialSum (m + 1) s := by
  induction m with
  | zero =>
      simp [finiteSourceLayer, suzukiOddSourceUpperPartialSum]
  | succ m ih =>
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega,
        finiteSourceLayer_add_two, ih]
      rw [suzukiOddSourceUpperPartialSum_succ (m + 1)]
      congr 1

/-- Lemma 13.2 gives one real upper bound for all odd partial sums at the source
endpoint `s = 3`. -/
theorem suzukiOddSourceUpperPartialSum_bounded_of_sourceContract
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    ∃ B : ℝ, ∀ m : ℕ, suzukiOddSourceUpperPartialSum m 3 ≤ B := by
  obtain ⟨C, hC, hall⟩ := lemma132_finiteLayerHatUniform_slack hH
  refine ⟨C * 3 * H.T .plus 3, ?_⟩
  intro m
  cases m with
  | zero =>
      simp [suzukiOddSourceUpperPartialSum]
      exact mul_nonneg
        (mul_nonneg (le_trans (by norm_num) hC) (by norm_num))
        (le_of_lt (hH.positive .plus 3 (by norm_num)))
  | succ m =>
      have hOdd : Odd (2 * m + 1) :=
        Nat.odd_iff.mpr (by omega)
      have hdom : (3 : ℝ) ∈ KappaOneModel.parityDomain 2 (2 * m + 1) := by
        simp [KappaOneModel.parityDomain]
        norm_num
      have hbound := hall (2 * m + 1) 3 (by omega) hdom
      rw [ErrorSign.ofDepth_of_odd hOdd] at hbound
      apply le_of_mul_le_mul_left _ (by norm_num : (0 : ℝ) < 3)
      rw [← finiteSourceLayer_two_mul_add_one_eq_oddPartialSum]
      calc
        3 * finiteSourceLayer 1 2 (2 * m + 1) 3 ≤
            C * 3 ^ 2 * H.T .plus 3 := hbound
        _ = 3 * (C * 3 * H.T .plus 3) := by ring

/-- The actual odd source-layer sequence at `s = 3` is summable, with no
caller-supplied majorant. -/
theorem summable_suzukiLayer_one_two_odd_at_three_of_sourceContract
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    Summable (fun k : ℕ => suzukiLayer 1 2 (2 * k + 1) 3) := by
  obtain ⟨B, hB⟩ :=
    suzukiOddSourceUpperPartialSum_bounded_of_sourceContract hH
  apply summable_of_sum_range_le
    SuzukiFiniteContinuousLayers.suzuki_oddLayer_at_three_nonneg
  intro m
  simpa [suzukiOddSourceUpperPartialSum] using hB m

/-- Odd finite partial sums converge to the exact `tsum` used in the canonical
amplitude. -/
theorem tendsto_suzukiOddSourceUpperPartialSum
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    Tendsto (fun m => suzukiOddSourceUpperPartialSum m 3) atTop
      (𝓝 (∑' k : ℕ, suzukiLayer 1 2 (2 * k + 1) 3)) := by
  exact
    (summable_suzukiLayer_one_two_odd_at_three_of_sourceContract hH).hasSum.tendsto_sum_nat

/-- The finite first-interval amplitudes `A_m` converge to Suzuki's canonical
amplitude `A`. -/
theorem tendsto_suzukiFiniteLowerAmplitude
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    Tendsto suzukiFiniteLowerAmplitude atTop
      (𝓝 SuzukiFiniteContinuousLayers.suzukiLowerSieveAmplitude) := by
  have hsum := tendsto_suzukiOddSourceUpperPartialSum hH
  change Tendsto
    (fun m => 3 * (1 + suzukiOddSourceUpperPartialSum m 3)) atTop
    (𝓝 (3 * (1 + ∑' k : ℕ, suzukiLayer 1 2 (2 * k + 1) 3)))
  exact (tendsto_const_nhds.add hsum).const_mul 3

/-- The `A_m-A` contribution in the first-interval residual decomposition tends
to zero (for every fixed real coordinate `s`). -/
theorem tendsto_suzukiFiniteLowerAmplitude_residual_zero
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) (s : ℝ) :
    Tendsto
      (fun m =>
        (suzukiFiniteLowerAmplitude m -
            SuzukiFiniteContinuousLayers.suzukiLowerSieveAmplitude) / s *
          (∫ t in (2 : ℝ)..s, (t - 1)⁻¹))
      atTop (𝓝 0) := by
  have hsub : Tendsto
      (fun m => suzukiFiniteLowerAmplitude m -
        SuzukiFiniteContinuousLayers.suzukiLowerSieveAmplitude)
      atTop
      (𝓝 (SuzukiFiniteContinuousLayers.suzukiLowerSieveAmplitude -
        SuzukiFiniteContinuousLayers.suzukiLowerSieveAmplitude)) :=
    (tendsto_suzukiFiniteLowerAmplitude hH).sub tendsto_const_nhds
  simpa using (hsub.div_const s).mul_const
    (∫ t in (2 : ℝ)..s, (t - 1)⁻¹)


end MathlibNt.SieveTheory
