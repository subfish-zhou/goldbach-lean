import MathlibNt.SieveTheory.LiLiuPrereqWFSmallDensity
import Mathlib.Analysis.Complex.ExponentialBounds


/-!
# Normalized exponential bounds on intervals of small primes

The weights and cubic boundary kernels are the ones already constructed.
An exponential tilt bounds the kernels, and an Euler-product majorant
retains the normalization needed by the dimension-one hypothesis.
The resulting estimate is useful on `w ≤ p < u` when `log u / log w`
is bounded. It does not control the remaining small-minimum boundaries.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

open Finset
open scoped Classical


/-- The finite-carrier form of I80 (1), with the same constant `K`.
The left endpoint is closed and the right endpoint is strict. -/
def DimensionOneProductBound (P : Finset ℕ) (g : ℕ → ℝ) (K : ℝ) : Prop :=
  ∀ w z : ℝ, 2 ≤ w → w < z →
    (∏ p ∈ P.filter (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z),
      (1 - g p)⁻¹) ≤ Real.log z / Real.log w * (1 + K / Real.log w)


end MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser
