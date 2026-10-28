/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import MathlibNt.AnalyticNumberTheory.LargeSieve.PrimitiveCharacters
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLFoundation
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Chen 1973, Lemma 6, equation (17): the `L' S` contour shift

This file isolates the honest complex-analytic deformation used in (17).  The
integrand is the actual product
`L'(s,χ) S(H,s,χ) y^s K_x(s)`, with `K_x` Chen's rational Mellin kernel.
The proof never divides by `L` on the beta line.
-/

noncomputable section

open Classical Complex Finset MeasureTheory Set Filter
open scoped BigOperators ArithmeticFunction Topology

namespace AnalyticNumberTheory.LargeSieve


/-- A vertical section of a complex integrand. -/
def chen1973VerticalSection (f : ℂ → ℂ) (σ t : ℝ) : ℂ :=
  f (σ + t * I)

/-- The two horizontal sides of the rectangle, oriented from beta to alpha. -/
def chen1973HorizontalSection (f : ℂ → ℂ) (β α T : ℝ) : ℂ :=
  (∫ u in β..α, f (u + (-T) * I)) - ∫ u in β..α, f (u + T * I)


end AnalyticNumberTheory.LargeSieve
