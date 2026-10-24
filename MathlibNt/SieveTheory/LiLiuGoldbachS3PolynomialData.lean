import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite polynomial data for the S3 integral certificate

The finite rational polynomials and their primitives do not depend on the
analytic sieve estimates. Their derivative and envelope bounds are proved
in the analytic modules.
-/

open scoped BigOperators
open Finset
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The explicit integrated product of the odd logarithm and geometric polynomials. -/
noncomputable def goldbachS3_innerPolynomial (n m : ℕ) (z : ℝ) : ℝ :=
  2 * ∑ i ∈ range n, ∑ j ∈ range m,
    z^(2*i+j+2) / (((2*i+1 : ℕ) : ℝ) * ((2*i+j+2 : ℕ) : ℝ))

/-- Dense exact rational polynomial, in increasing coefficient order. -/
noncomputable def s3eval : List ℚ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, x => (c : ℝ) + x * s3eval cs x

/-- A rational primitive; the natural offset makes the derivative induction transparent. -/
noncomputable def s3primAux : List ℚ → ℕ → ℝ → ℝ
  | [], _, _ => 0
  | c :: cs, n, x => (c : ℝ) / (n+1 : ℕ) * x^(n+1) + s3primAux cs (n+1) x

noncomputable def s3prim (cs : List ℚ) : ℝ → ℝ := s3primAux cs 0


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
