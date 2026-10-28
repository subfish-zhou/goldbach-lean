import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Set Filter Topology MeasureTheory intervalIntegral
open scoped Interval

namespace Section10Lemma1028FirstCrossing

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Lemma 10.28: the global minus-envelope first crossing

This file isolates the topological first-crossing step on pp. 55--58.  It does
not assume the desired derivative sign and it does not take a common-majorant
record as input.  The only frozen source boundary is the stationary-point
exclusion obtained from the pairing calculation and the unit-interval estimate
(10.53).  This is the earliest presently unformalized analytic estimate.
-/

/-- The normalized part of (10.44), before subtracting `c₋`. -/
noncomputable def normalizedMinusBase
    (R ξ : ℝ → ℝ) (s : ℝ) : ℝ :=
  -R (s - 1) / (s * R s) + ξ s - 2 / s

/-- Minimal DDE/pairing data.  In particular this has no derivative-sign or
common-majorant field. -/
structure FirstCrossingDDEApparatus (R : ℝ → ℝ) (β : ℝ) where
  adjoint : ℝ → ℝ
  beta_ge_one : 1 ≤ β
  continuous : ContinuousOn R (Ioi (β - 1))
  positive : ∀ s, β - 1 < s → 0 < R s
  original_dde : ∀ s, β < s →
    HasDerivAt R (-(2 * R s + R (s - 1)) / s) s
  adjoint_positive : ∀ s, β ≤ s → 0 < adjoint s
  adjoint_dde : ∀ s, 0 < s →
    HasDerivAt (fun u => u * adjoint u)
      (2 * adjoint s + adjoint (s + 1)) s
  pairing_zero : ∀ s, β < s →
    s * adjoint s * R s = ∫ t in s - 1..s, adjoint (t + 1) * R t


/-- Sanitized output contract: it records a cutoff, so the source's eventual
`ξ-c₋` lower bound is not incorrectly asserted on the fixed interval `[3,S]`.
The slope conclusion is populated by the constructor below, never supplied as
an input to it. -/
structure Section10CommonMajorant (R : ℝ → ℝ) where
  xi : ℝ → ℝ
  cMinus : ℝ
  cutoff : ℝ
  A : ℝ
  four_le_cutoff : 4 ≤ cutoff
  one_le_A : 1 ≤ A
  majorizes_log : ∀ s, cutoff ≤ s →
    (1 / A) * Real.log (Real.exp 1 * s) ≤ xi s - cMinus - 2 / s
  envelope_slope_nonpos : ∀ s, cutoff ≤ s →
    -(R (s - 1)) + s * (xi s - cMinus - 2 / s) * R s ≤ 0


end Section10Lemma1028FirstCrossing
