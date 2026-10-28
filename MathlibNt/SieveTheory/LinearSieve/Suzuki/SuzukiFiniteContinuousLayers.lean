/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Suzuki's finite continuous layers: source-correct normalized recursion

This file records Suzuki, §9, (9.1)--(9.2).  The decisive point is that the
integrand in (9.2) is the preceding *normalized* layer `f_{n-1}(t - 1)`, not its
unnormalized numerator.

The normalized layer is therefore defined first by structural recursion.  The
numerator is then defined as the right-hand side of (9.1) or (9.2), so that the
source equations are available without division.  Their normalization bridge is
valid for every `s`; cancellation in the opposite direction requires a nonzero
normalizing factor (below we expose the natural hypothesis `0 < s`).
-/

namespace MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers

open MeasureTheory intervalIntegral
open scoped Interval


def sourceEpsilon (n : ℕ) : ℕ := n % 2

@[simp] theorem sourceEpsilon_even {n : ℕ} (h : Even n) : sourceEpsilon n = 0 := by
  exact Nat.even_iff.mp h


noncomputable def dPowDensity (κ t : ℝ) : ℝ := κ * t ^ (κ - 1)

def baseLower (β s : ℝ) : ℝ := min s (β + 1)

def recursionLower (β s : ℝ) (n : ℕ) : ℝ :=
  min (max s (β + sourceEpsilon n)) (β + n)

/-- Suzuki's normalized `fₙ`.  In the recursive case the source integrand is
`f_{n-1}(t-1)`, as in (9.2). -/
noncomputable def suzukiLayer (κ β : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 0
  | 1, s => (s ^ κ)⁻¹ *
      ∫ t in baseLower β s..(β + 1), dPowDensity κ t
  | n + 2, s => (s ^ κ)⁻¹ *
      ∫ t in recursionLower β s (n + 2)..(β + (n + 2)),
        suzukiLayer κ β (n + 1) (t - 1) * dPowDensity κ t

/-- The source right-hand side `s^κ fₙ(s)` from (9.1)--(9.2).  This is kept as
an API in its own right, but its recursive integrand is the normalized preceding
layer, not the preceding numerator. -/
noncomputable def suzukiLayerNumerator (κ β : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 0
  | 1, s => ∫ t in baseLower β s..(β + 1), dPowDensity κ t
  | n + 2, s =>
      ∫ t in recursionLower β s (n + 2)..(β + (n + 2)),
        suzukiLayer κ β (n + 1) (t - 1) * dPowDensity κ t


noncomputable def finiteSourceLayer (κ β : ℝ) (N : ℕ) (s : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    if n % 2 = N % 2 then suzukiLayer κ β n s else 0


/-- Normalized form of (9.1). -/
theorem suzukiLayer_one (κ β s : ℝ) :
    suzukiLayer κ β 1 s = (s ^ κ)⁻¹ *
      ∫ t in baseLower β s..(β + 1), dPowDensity κ t := rfl

/-- Normalized form of (9.2), with the preceding normalized layer in the
integrand. -/
theorem suzukiLayer_succ_succ (κ β s : ℝ) (n : ℕ) :
    suzukiLayer κ β (n + 2) s = (s ^ κ)⁻¹ *
      ∫ t in recursionLower β s (n + 2)..(β + (n + 2)),
        suzukiLayer κ β (n + 1) (t - 1) * dPowDensity κ t := rfl

/-- Unnormalized source right-hand side in (9.1). -/
theorem suzukiLayerNumerator_one (κ β s : ℝ) :
    suzukiLayerNumerator κ β 1 s =
      ∫ t in baseLower β s..(β + 1), dPowDensity κ t := rfl

/-- Source-correct unnormalized right-hand side in (9.2). -/
theorem suzukiLayerNumerator_succ_succ (κ β s : ℝ) (n : ℕ) :
    suzukiLayerNumerator κ β (n + 2) s =
      ∫ t in recursionLower β s (n + 2)..(β + (n + 2)),
        suzukiLayer κ β (n + 1) (t - 1) * dPowDensity κ t := rfl

/-- The division-form bridge is total, including at `s = 0`. -/
theorem suzukiLayer_eq_inv_rpow_mul_numerator (κ β : ℝ) (n : ℕ) (s : ℝ) :
    suzukiLayer κ β n s =
      (s ^ κ)⁻¹ * suzukiLayerNumerator κ β n s := by
  cases n with
  | zero => simp [suzukiLayer, suzukiLayerNumerator]
  | succ n =>
      cases n with
      | zero => rfl
      | succ n => rfl

/-- Cancellation is valid whenever the normalizing factor is nonzero. -/
theorem rpow_mul_suzukiLayer_of_ne (κ β : ℝ) (n : ℕ) (s : ℝ)
    (hs : s ^ κ ≠ 0) :
    s ^ κ * suzukiLayer κ β n s = suzukiLayerNumerator κ β n s := by
  rw [suzukiLayer_eq_inv_rpow_mul_numerator]
  field_simp

/-- The source equation `s^κ fₙ(s) = RHSₙ(s)` after legal cancellation on the
positive Suzuki domain. -/
theorem rpow_mul_suzukiLayer (κ β : ℝ) (n : ℕ) {s : ℝ} (hs : 0 < s) :
    s ^ κ * suzukiLayer κ β n s = suzukiLayerNumerator κ β n s := by
  exact rpow_mul_suzukiLayer_of_ne κ β n s
    (ne_of_gt (Real.rpow_pos_of_pos hs κ))


@[simp] theorem baseLower_eq_upper {β s : ℝ} (hs : β + 1 ≤ s) :
    baseLower β s = β + 1 := by simp [baseLower, hs]

@[simp] theorem recursionLower_eq_upper {β s : ℝ} {n : ℕ}
    (hs : β + n ≤ s) : recursionLower β s n = β + n := by
  simp [recursionLower, hs]

/-- Proposition 9.2(i), at the level of the source RHS. -/
theorem suzukiLayerNumerator_eq_zero_of_le (κ β : ℝ) (n : ℕ) {s : ℝ}
    (hs : β + n ≤ s) : suzukiLayerNumerator κ β n s = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
      cases n with
      | zero =>
          have hs' : β + 1 ≤ s := by norm_num at hs ⊢; exact hs
          rw [suzukiLayerNumerator_one, baseLower_eq_upper hs']
          exact intervalIntegral.integral_same
      | succ n =>
          have hlower : recursionLower β s (n + 2) = β + ((n : ℝ) + 2) := by
            simpa only [Nat.cast_add, Nat.cast_ofNat] using
              (recursionLower_eq_upper (β := β) (s := s) (n := n + 2) hs)
          rw [suzukiLayerNumerator_succ_succ, hlower]
          exact intervalIntegral.integral_same

/-- Proposition 9.2(i), for a normalized finite layer. -/
theorem suzukiLayer_eq_zero_of_le (κ β : ℝ) (n : ℕ) {s : ℝ}
    (hs : β + n ≤ s) : suzukiLayer κ β n s = 0 := by
  rw [suzukiLayer_eq_inv_rpow_mul_numerator,
    suzukiLayerNumerator_eq_zero_of_le κ β n hs, mul_zero]


end MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
