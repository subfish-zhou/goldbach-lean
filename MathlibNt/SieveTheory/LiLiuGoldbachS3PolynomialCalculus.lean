import MathlibNt.SieveTheory.LiLiuGoldbachS3PolynomialCertificate
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Differentiation of exact coefficient lists

For a Horner polynomial `c + x * P`, the derivative is `P + x * P'`.
Constants have the empty derivative list, so no trailing zero is introduced.
The evaluation theorem converts finite rational coefficient identities into
ordinary real derivative proofs.
-/

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.S3Polynomial

/-- Coefficient derivative in increasing degree order. -/
def derivative : List ℚ → List ℚ
  | [] => []
  | [_] => []
  | _ :: c :: cs => add (c :: cs) (0 :: derivative (c :: cs))

theorem eval_hasDerivAt (cs : List ℚ) (x : ℝ) :
    HasDerivAt (s3eval cs) (s3eval (derivative cs) x) x := by
  induction cs with
  | nil => simpa [derivative, s3eval] using hasDerivAt_const x (0 : ℝ)
  | cons c cs ih =>
    cases cs with
    | nil => simpa [derivative, s3eval] using hasDerivAt_const x (c : ℝ)
    | cons d ds =>
      convert (hasDerivAt_const x (c : ℝ)).add ((hasDerivAt_id x).mul ih) using 1 <;>
        first | rfl | simp [derivative, eval_add, s3eval]

theorem eval_continuous (cs : List ℚ) : Continuous (s3eval cs) :=
  continuous_iff_continuousAt.mpr fun x => (eval_hasDerivAt cs x).continuousAt

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.S3Polynomial
