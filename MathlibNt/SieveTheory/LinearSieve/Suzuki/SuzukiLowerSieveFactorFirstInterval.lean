/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiFiniteSourceLayerEvenLimit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

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

/-- The source amplitude is strictly positive. -/
theorem suzukiLowerSieveAmplitude_pos : 0 < suzukiLowerSieveAmplitude := by
  have hsum : 0 ≤ ∑' k : ℕ, suzukiLayer 1 2 (2 * k + 1) 3 :=
    tsum_nonneg suzuki_oddLayer_at_three_nonneg
  unfold suzukiLowerSieveAmplitude
  nlinarith

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

/-- Direct specialization of (9.2) for the first even layer. -/
theorem suzukiLayer_two_one_two {s : ℝ} (hs₂ : 2 ≤ s) (hs₄ : s ≤ 4) :
    suzukiLayer 1 2 2 s =
      s⁻¹ * ∫ t in s..(4 : ℝ), (4 - t) / (t - 1) := by
  rw [suzukiLayer_succ_succ 1 2 s 0]
  have hlower : recursionLower 2 s 2 = s := by
    unfold recursionLower sourceEpsilon
    norm_num
    rw [max_eq_left hs₂, min_eq_left hs₄]
  rw [hlower]
  simp only [dPowDensity, sub_self, Real.rpow_zero, mul_one, Real.rpow_one,
    Nat.cast_zero, zero_add]
  norm_num only
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Set.Icc s 4 := by
    simpa [Set.uIcc_of_le hs₄] using ht
  change suzukiLayer 1 2 1 (t - 1) = (4 - t) / (t - 1)
  rw [suzukiLayer_one_one_two]
  · ring
  · linarith [ht'.1, hs₂]
  · linarith [ht'.2]

@[simp] theorem suzukiLayer_one_one_two_eq_zero_of_three_le {s : ℝ} (hs : 3 ≤ s) :
    suzukiLayer 1 2 1 s = 0 := by
  exact suzukiLayer_eq_zero_of_le 1 2 1 (by norm_num at hs ⊢; exact hs)

@[simp] theorem suzukiLayer_two_one_two_eq_zero_of_four_le {s : ℝ} (hs : 4 ≤ s) :
    suzukiLayer 1 2 2 s = 0 := by
  exact suzukiLayer_eq_zero_of_le 1 2 2 (by norm_num at hs ⊢; exact hs)

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

@[simp] theorem suzukiLowerSieveFactorFirstInterval_two :
    suzukiLowerSieveFactorFirstInterval 2 = 0 := by
  rw [suzukiLowerSieveFactorFirstInterval_eq_log (by norm_num) (by norm_num)]
  norm_num

theorem suzukiLowerSieveFactorFirstInterval_pos {s : ℝ}
    (hs₂ : 2 < s) (hs₄ : s ≤ 4) :
    0 < suzukiLowerSieveFactorFirstInterval s := by
  rw [suzukiLowerSieveFactorFirstInterval_eq_log hs₂.le hs₄]
  have hlog : 0 < Real.log (s - 1) := Real.log_pos (by linarith)
  exact div_pos (mul_pos suzukiLowerSieveAmplitude_pos hlog) (by linarith)

theorem suzukiLowerSieveFactorFirstInterval_eleven_fifths_pos :
    0 < suzukiLowerSieveFactorFirstInterval ((11 : ℝ) / 5) := by
  apply suzukiLowerSieveFactorFirstInterval_pos <;> norm_num

end


end MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
