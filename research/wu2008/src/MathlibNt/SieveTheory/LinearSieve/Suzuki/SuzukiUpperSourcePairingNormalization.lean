/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiContinuousLowerFactorSecondInterval

/-!
# Suzuki's upper-source pairing and the amplitude normalization

This module records the source-faithful front half of the normalization
`A = 2 exp γ` at `κ = 1`, `β = 2`.

Suzuki (10.2), (10.5) extends
`P = F⁺ + F⁻ = 2 + T⁺ - T⁻` by `s P(s) = A` on `1 < s < 2`.
For the standard adjoint `p = r_{1,-1}`, Section 10 gives
`p'(s) = -p(s+1)/s`.  Consequently the Iwaniec pairing at the source
threshold is exactly `A p(1)`.  Proposition 11.8(iii) makes this pairing `2`;
the independent standard-adjoint boundary evaluation `p(1)=exp(-γ)` then
gives `A=2 exp γ`.

The production tree does not yet construct `r_{1,-1}` or prove its boundary
evaluation.  Accordingly, this file does not assert the final equality.  It
constructs the genuine upper source `P`, its Section-10 pairing, proves the
threshold identity from the actual adjoint equation, and exposes the exact
final bridge.  No Section-13 hat layer occurs here.
-/

namespace MathlibNt.SieveTheory

open Filter Topology MeasureTheory intervalIntegral Set
open scoped Interval BigOperators
open SuzukiFiniteContinuousLayers

noncomputable section

/-- Suzuki's genuine upper source `P`.  Below the source threshold this is the
Section-10 initial-history extension; strictly above it this is literally
`F⁺ + F⁻ = 2 + T⁺ - T⁻` from the production parity source series.  The value at
one switching point is assigned by the initial-history convention, which does
not affect any interval integral. -/
noncomputable def suzukiUpperSourceP (s : ℝ) : ℝ :=
  if s ≤ 2 then suzukiLowerSieveAmplitude / s
  else suzukiContinuousUpperFactor s + suzukiContinuousLowerFactor s

/-- The Section-10 Iwaniec pairing for the upper equation at `κ=1`.  The plus
sign is `-b` in (10.9), because the upper source has DDE parameter `b=-1`. -/
noncomputable def suzukiUpperSourcePairing (p : ℝ → ℝ) (s : ℝ) : ℝ :=
  s * p s * suzukiUpperSourceP s +
    ∫ t in (s - 1)..s, p (t + 1) * suzukiUpperSourceP t

@[simp] theorem suzukiUpperSourceP_of_le_two {s : ℝ} (hs : s ≤ 2) :
    suzukiUpperSourceP s = suzukiLowerSieveAmplitude / s := by
  simp [suzukiUpperSourceP, hs]

theorem suzukiUpperSourceP_of_two_lt {s : ℝ} (hs : 2 < s) :
    suzukiUpperSourceP s =
      2 + suzukiProposition118SourceTPlus s - suzukiContinuousLowerTail s := by
  rw [suzukiUpperSourceP]
  simp only [if_neg (not_le_of_gt hs), suzukiContinuousUpperFactor,
    suzukiContinuousLowerFactor, suzukiContinuousLowerTail]
  ring

/-- The actual upper source has the exact Section-10 initial history
`s P(s)=A` (including the harmless chosen switching-point value). -/
theorem mul_suzukiUpperSourceP_eq_amplitude {s : ℝ}
    (hs₀ : s ≠ 0) (hs₂ : s ≤ 2) :
    s * suzukiUpperSourceP s = suzukiLowerSieveAmplitude := by
  rw [suzukiUpperSourceP_of_le_two hs₂]
  field_simp

/-- Integrating the standard upper-adjoint equation on `[1,2]` gives the exact
boundary coefficient used in Suzuki's Proposition 11.8 formula. -/
theorem integral_upperAdjoint_shift_div_eq_sub
    {p : ℝ → ℝ}
    (hp : ∀ t ∈ Set.uIcc (1 : ℝ) 2,
      HasDerivAt p (-p (t + 1) / t) t)
    (hint : IntervalIntegrable (fun t => p (t + 1) / t) volume 1 2) :
    (∫ t in (1 : ℝ)..2, p (t + 1) / t) = p 1 - p 2 := by
  have hderiv : ∀ t ∈ Set.uIcc (1 : ℝ) 2,
      HasDerivAt (-p) (p (t + 1) / t) t := by
    intro t ht
    simpa only [neg_div, neg_neg] using (hp t ht).neg
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  · change -p 2 - -p 1 = p 1 - p 2
    ring
  · exact hint

/-- Source-faithful threshold evaluation: the genuine upper-source pairing is
`A p(1)`.  This is the finite Section-10 pairing calculation, not a definition
of `A` and not an assumed normalization. -/
theorem suzukiUpperSourcePairing_two_eq_amplitude_mul_adjoint_one
    {p : ℝ → ℝ}
    (hp : ∀ t ∈ Set.uIcc (1 : ℝ) 2,
      HasDerivAt p (-p (t + 1) / t) t)
    (hint : IntervalIntegrable (fun t => p (t + 1) / t) volume 1 2) :
    suzukiUpperSourcePairing p 2 = suzukiLowerSieveAmplitude * p 1 := by
  unfold suzukiUpperSourcePairing
  rw [show (2 : ℝ) - 1 = 1 by norm_num,
    suzukiUpperSourceP_of_le_two (by norm_num : (2 : ℝ) ≤ 2)]
  have hIntegral :
      (∫ t in (1 : ℝ)..2, p (t + 1) * suzukiUpperSourceP t) =
        suzukiLowerSieveAmplitude * ∫ t in (1 : ℝ)..2, p (t + 1) / t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at ht
    rw [suzukiUpperSourceP_of_le_two ht.2]
    ring
  rw [hIntegral, integral_upperAdjoint_shift_div_eq_sub hp hint]
  ring

/-- Exact final algebraic bridge.  Its two hypotheses are precisely the two
source statements still needing producers: Proposition 11.8(iii) for the
actual upper source, and the independent standard-adjoint value
`r_{1,-1}(1)=exp(-γ)`. -/
theorem suzukiLowerSieveAmplitude_eq_two_mul_exp_eulerMascheroni_of_upperPairing
    {p : ℝ → ℝ}
    (hp : ∀ t ∈ Set.uIcc (1 : ℝ) 2,
      HasDerivAt p (-p (t + 1) / t) t)
    (hint : IntervalIntegrable (fun t => p (t + 1) / t) volume 1 2)
    (hpair : suzukiUpperSourcePairing p 2 = 2)
    (hpone : p 1 = Real.exp (-Real.eulerMascheroniConstant)) :
    suzukiLowerSieveAmplitude =
      2 * Real.exp Real.eulerMascheroniConstant := by
  rw [suzukiUpperSourcePairing_two_eq_amplitude_mul_adjoint_one hp hint,
    hpone] at hpair
  have hexp : Real.exp (-Real.eulerMascheroniConstant) ≠ 0 :=
    ne_of_gt (Real.exp_pos _)
  apply (mul_right_cancel₀ hexp)
  rw [hpair]
  rw [mul_assoc, ← Real.exp_add]
  simp

end


end MathlibNt.SieveTheory
