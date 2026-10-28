import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticSiegelFiniteExceptions
import MathlibNt.AnalyticNumberTheory.LargeSieve.DirichLTwistedQuadraticPointwiseSiegelWalfisz

/-!
# Tatuzawa exceptional uniqueness and the Landau--Siegel lower bound

This module formalizes the logical core of the Tatuzawa route.  For a fixed
power `η`, an effective lower bound and a conductor threshold define the set of
primitive nonprincipal quadratic characters where that bound fails.  If this
set has at most one member, strict positivity of the one possible exceptional
`L(1, χ)` absorbs it into an ineffective constant.  The already established
finite-conductor bridge then supplies the raw Landau--Siegel lower bound.

The final source below is deliberately not exceptional uniqueness itself.  It
is the quantitative two-character value-product separation which implies
uniqueness.  Proving that separation by Euler-product positivity / zero
repulsion remains the analytic frontier; no such theorem is assumed to have
been completed here.
-/

open Complex Set

namespace AnalyticNumberTheory.LargeSieve

noncomputable section

/-- A primitive nonprincipal quadratic Dirichlet character, with its conductor
stored in the same object so exceptional characters at different conductors
can be compared. -/
structure PrimitiveQuadraticDatum where
  modulus : ℕ
  modulus_ne : modulus ≠ 0
  character : DirichletCharacter ℂ modulus
  isPrimitive : character.IsPrimitive
  square_eq_one : character ^ 2 = 1
  ne_one : character ≠ 1

namespace PrimitiveQuadraticDatum

/-- The real value `L(1, χ)` attached to a quadratic datum. -/
def value (x : PrimitiveQuadraticDatum) : ℝ :=
  letI : NeZero x.modulus := ⟨x.modulus_ne⟩
  (x.character.LFunction 1).re


lemma modulus_pos (x : PrimitiveQuadraticDatum) : 0 < x.modulus :=
  Nat.pos_of_ne_zero x.modulus_ne


lemma value_pos (x : PrimitiveQuadraticDatum) : 0 < x.value := by
  let : NeZero x.modulus := ⟨x.modulus_ne⟩
  simpa [value] using
    (DirichletCharacter.LFunction_apply_one_re_pos_of_sq_eq_one
      x.square_eq_one x.ne_one)

end PrimitiveQuadraticDatum


end

end AnalyticNumberTheory.LargeSieve
