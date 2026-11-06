/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Pairing conservation directly from an integral delay equation

This module avoids differentiating the source function at the left endpoint.
The integral DDE itself supplies the required right derivative, including at
`x = 2`, where only right continuity of the delayed value at `1` is used.
-/

namespace MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers

open Filter Topology MeasureTheory intervalIntegral Set
open scoped Interval

noncomputable section

/-- The κ=1 Iwaniec pairing in weighted coordinates `F(s) = s Q(s)`. -/
noncomputable def sourceWeightedPairing (F : ℝ → ℝ) (s : ℝ) : ℝ :=
  (s - 1) * F s - ∫ t in (s - 1)..s, F t


end
end MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
