

import MathlibNt.AnalyticNumberTheory.LargeSieve.VonMangoldtConductorCorrection
import MathlibNt.AnalyticNumberTheory.LargeSieve.ImprimitiveConductorWeightLinear
import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIIActualTensorMomentExplicit

/-!
 # All-character nonprincipal Vaughan ledger and Type-II scale audit

This module only assembles proved producers.  It keeps the principal character
out, keeps the full prefix maximum on the all-character side, and records that
the currently proved tensor Type-II estimate is only an endpoint estimate.
Consequently no Standard Bombieri--Vinogradov theorem is claimed.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- The coefficient `1`, used to specialize Vaughan's identity to `Λ`. -/
def vaughanUnitIntegerCoeff (_ : ℤ) : ℂ := 1

/-- One conductor-weighted primitive prefix-maximal lane. -/
def vaughanConductorPrefixLane (a : ℤ → ℂ) (N Q : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 2 Q, imprimitiveConductorWeight Q d *
    ∑ ψ : PrimitiveCharacter d,
      primitiveCharacterPrefixMaxSquare a 0 N d ψ

/-- The closed `Λ`-specific conductor correction, with every `N,Q,log` factor
kept literal. -/
def vaughanLambdaConductorCorrectionScale (N Q : ℕ) : ℝ :=
  2 * (Q : ℝ) ^ 2 *
    (2 * (Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ)) ^ 2

lemma vaughanLambdaCoeff_unit_eq (n : ℤ) :
    vaughanLambdaCoeff vaughanUnitIntegerCoeff n = vonMangoldtIntegerCoeff n := by
  simp [vaughanLambdaCoeff, vaughanUnitIntegerCoeff, vonMangoldtIntegerCoeff]


/-- The exact endpoint-only Type-II scale delivered by the current producers on
one conductor window `C ≤ conductor ≤ 2C` and one Vaughan outer shell `2^k`.
It includes, in order: linear imprimitive transport, outer Möbius Cauchy, the
primitive large-sieve charge, and the unconditional constant-27 tensor moment. -/
def existingTypeIIEndpointWindowScale (N Q C k B : ℕ) : ℝ :=
  ((Q / C : ℕ) : ℝ) * conductorHarmonicFactor (Q / C) *
    ((2 ^ k : ℕ) : ℝ) *
    ((N : ℝ) +
      (2 * (Nat.ceil (Real.log (((2 * C : ℕ) : ℝ) ^ 2) / Real.log 2) : ℝ) + 12) *
        ((2 * C : ℕ) : ℝ) ^ 2) *
    (27 * (B : ℝ) ^ 2 * (N : ℝ) * Real.log (N + 1 : ℕ) ^ 5)


/-- Algebraic payment audit: the length term of the primitive large sieve pays
`N` a second time after the tensor moment has already paid its physical row mass
`N`; the outer-shell Cauchy separately pays `2^k`. -/
theorem existingTypeIIEndpointWindowScale_split (N Q C k B : ℕ) :
    existingTypeIIEndpointWindowScale N Q C k B =
      27 * (B : ℝ) ^ 2 * ((Q / C : ℕ) : ℝ) *
        conductorHarmonicFactor (Q / C) * ((2 ^ k : ℕ) : ℝ) *
        Real.log (N + 1 : ℕ) ^ 5 *
        ((N : ℝ) ^ 2 +
          (N : ℝ) *
            ((2 * (Nat.ceil (Real.log (((2 * C : ℕ) : ℝ) ^ 2) / Real.log 2) : ℝ) + 12) *
              ((2 * C : ℕ) : ℝ) ^ 2)) := by
  unfold existingTypeIIEndpointWindowScale
  ring


/-- Minimal missing Type-II interface.  Unlike the proved endpoint theorem, this
contract retains the maximum over every prefix before summing over characters
and conductors, and it asks for the inverse-log square-mean scale with no repeated
outer-shell/row-length payment.  It is intentionally a named `Prop`, not asserted
as a theorem. -/
def VaughanTypeIIPrefixTensorRepair (N Q u v A : ℕ) (K : ℝ) : Prop :=
  vaughanConductorPrefixLane
      (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) N Q ≤
    K * (N : ℝ) ^ 2 / Real.log (N + 1 : ℕ) ^ A

end

end AnalyticNumberTheory.LargeSieve
