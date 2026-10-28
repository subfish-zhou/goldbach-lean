/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiFiniteSourceLayerEvenLimit

/-!
# Suzuki's source lower factor on its first explicit interval

This module specializes Suzuki §9 to `κ = 1`, `β = 2`. Suzuki (9.5) and the
paragraph following it define `T⁺` as the odd limiting layer sum and
`F⁻ = 1 - T⁻`. Proposition 9.4(vii)--(viii), with the Section 15.2
normalization `B = 0`, gives on the first lower interval `2 ≤ s ≤ 4`

`F⁻(s) = (A / s) ∫ t in 2..s, 1 / (t - 1)`,

where `A = 3 * T⁺(3) + 3`. The definition below records this source formula;
its identification with `1 - T⁻` remains a separate theorem obligation.
It is independent of the nonstandard placeholder `LinearSieve.sieveFunctionf`.
-/

namespace MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers

open MeasureTheory intervalIntegral
open scoped Interval

noncomputable section

/-- Suzuki's constant `A` at `κ = 1`, `β = 2`, written in terms of his odd
normalized source layers. -/
noncomputable def suzukiLowerSieveAmplitude : ℝ :=
  3 * (1 + ∑' k : ℕ, suzukiLayer 1 2 (2 * k + 1) 3)

/-- The source formula for the lower limiting factor on its first interval.
Identification with the even-layer limit is intentionally not asserted here. -/
noncomputable def suzukiLowerSieveFactorFirstInterval (s : ℝ) : ℝ :=
  suzukiLowerSieveAmplitude / s * ∫ t in (2 : ℝ)..s, (t - 1)⁻¹

/-- Every odd layer entering Suzuki's amplitude is nonnegative. -/
theorem suzuki_oddLayer_at_three_nonneg (k : ℕ) :
    0 ≤ suzukiLayer 1 2 (2 * k + 1) 3 := by
  apply suzukiLayer_one_nonneg_on_parityDomain (β := (2 : ℝ)) (by norm_num)
  simp only [suzukiParityDomainOne, KappaOneModel.parityDomain]
  have hodd : (2 * k + 1) % 2 = 1 := by omega
  rw [hodd]
  norm_num


/-- Direct evaluation of (9.1) at `κ = 1`, `β = 2`. -/
theorem suzukiLayer_one_one_two {s : ℝ} (hs₀ : 0 < s) (hs₃ : s ≤ 3) :
    suzukiLayer 1 2 1 s = (3 - s) / s := by
  rw [suzukiLayer_one]
  have hmin : baseLower 2 s = s := by
    unfold baseLower
    apply min_eq_left
    norm_num at hs₃ ⊢
    exact hs₃
  rw [hmin]
  norm_num [dPowDensity, intervalIntegral.integral_const, div_eq_mul_inv]
  field_simp


@[simp] theorem suzukiLayer_one_one_two_eq_zero_of_three_le {s : ℝ} (hs : 3 ≤ s) :
    suzukiLayer 1 2 1 s = 0 := by
  exact suzukiLayer_eq_zero_of_le 1 2 1 (by norm_num at hs ⊢; exact hs)


/-- The elementary integral in Suzuki's first lower interval. -/
theorem integral_inv_sub_one_two {s : ℝ} (hs : 2 ≤ s) :
    (∫ t in (2 : ℝ)..s, (t - 1)⁻¹) = Real.log (s - 1) := by
  have hderiv : ∀ x ∈ Set.uIcc (2 : ℝ) s,
      HasDerivAt (fun y : ℝ => Real.log (y - 1)) ((x - 1)⁻¹) x := by
    intro x hx
    have hx2 : 2 ≤ x := by
      rw [Set.uIcc_of_le hs] at hx
      exact hx.1
    simpa [one_div] using
      ((hasDerivAt_id x).sub_const 1).log (by linarith : x - 1 ≠ 0)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  · norm_num
  · exact ((continuousOn_id.sub continuousOn_const).inv₀
      (fun x hx => by
        rw [Set.uIcc_of_le hs] at hx
        change x - 1 ≠ 0
        exact ne_of_gt (by linarith [hx.1]))).intervalIntegrable

/-- Suzuki's explicit first-interval formula, with both source endpoints exact. -/
theorem suzukiLowerSieveFactorFirstInterval_eq_log {s : ℝ}
    (hs₂ : 2 ≤ s) (_hs₄ : s ≤ 4) :
    suzukiLowerSieveFactorFirstInterval s =
      suzukiLowerSieveAmplitude * Real.log (s - 1) / s := by
  rw [suzukiLowerSieveFactorFirstInterval, integral_inv_sub_one_two hs₂]
  ring


end


end MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
