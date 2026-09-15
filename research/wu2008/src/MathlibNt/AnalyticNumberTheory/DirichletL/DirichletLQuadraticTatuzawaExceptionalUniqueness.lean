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

/-- The conductor power occurring in a Siegel lower bound. -/
def powerScale (η : ℝ) (x : PrimitiveQuadraticDatum) : ℝ :=
  (x.modulus : ℝ) ^ (-η)

lemma modulus_pos (x : PrimitiveQuadraticDatum) : 0 < x.modulus :=
  Nat.pos_of_ne_zero x.modulus_ne

lemma powerScale_pos (η : ℝ) (x : PrimitiveQuadraticDatum) :
    0 < x.powerScale η := by
  exact Real.rpow_pos_of_pos (by exact_mod_cast x.modulus_pos) (-η)

lemma value_pos (x : PrimitiveQuadraticDatum) : 0 < x.value := by
  let : NeZero x.modulus := ⟨x.modulus_ne⟩
  simpa [value] using
    (DirichletCharacter.LFunction_apply_one_re_pos_of_sq_eq_one
      x.square_eq_one x.ne_one)

end PrimitiveQuadraticDatum

/-- The literal set of large-conductor characters where the proposed effective
`c q⁻η` lower bound fails. -/
def tatuzawaEffectiveFailureSet (η c : ℝ) (Q : ℕ) :
    Set PrimitiveQuadraticDatum :=
  {x | Q ≤ x.modulus ∧ x.value < c * x.powerScale η}

/-- Quantifier-level Tatuzawa uniqueness: for every positive exponent there is
an effective threshold and effective positive coefficient for which at most
one large-conductor primitive quadratic character fails the lower bound. -/
def AtMostOneEventualEffectiveException : Prop :=
  ∀ η : ℝ, 0 < η → ∃ (Q : ℕ) (c : ℝ), 0 < c ∧
    (tatuzawaEffectiveFailureSet η c Q).Subsingleton

/-- A quantitative two-character separation interface.  Its lower side is the
product of the two proposed effective thresholds, so two distinct failures
would contradict it immediately.  This is the analytic, value-product-shaped
frontier intended for an Euler-product positivity or Deuring--Heilbronn proof. -/
def EventualTatuzawaValueProductSeparation : Prop :=
  ∀ η : ℝ, 0 < η → ∃ (Q : ℕ) (c : ℝ), 0 < c ∧
    ∀ x y : PrimitiveQuadraticDatum,
      Q ≤ x.modulus → Q ≤ y.modulus → x ≠ y →
        (c * x.powerScale η) * (c * y.powerScale η) ≤ x.value * y.value

/-- Source-faithful value-product power lower bound.  Unlike the failure-set
statement, this predicate does not mention exceptions or uniqueness: it asks
for a direct positive lower bound for the product of two distinct quadratic
`L(1)` values at the product of their two conductor-power scales. -/
def EventualTatuzawaValueProductPowerLowerBound : Prop :=
  ∀ η : ℝ, 0 < η → ∃ (Q : ℕ) (κ : ℝ), 0 < κ ∧
    ∀ x y : PrimitiveQuadraticDatum,
      Q ≤ x.modulus → Q ≤ y.modulus → x ≠ y →
        κ * x.powerScale η * y.powerScale η ≤ x.value * y.value

/-- A direct product lower bound supplies the threshold-form separation by
choosing the effective one-character coefficient `sqrt κ`. -/
theorem eventualTatuzawaValueProductSeparation_of_powerLowerBound
    (hprod : EventualTatuzawaValueProductPowerLowerBound) :
    EventualTatuzawaValueProductSeparation := by
  intro η hη
  obtain ⟨Q, κ, hκ, hlower⟩ := hprod η hη
  refine ⟨Q, Real.sqrt κ, Real.sqrt_pos.2 hκ, ?_⟩
  intro x y hxQ hyQ hxy
  calc
    (Real.sqrt κ * x.powerScale η) * (Real.sqrt κ * y.powerScale η) =
        (Real.sqrt κ) ^ 2 * x.powerScale η * y.powerScale η := by ring
    _ = κ * x.powerScale η * y.powerScale η := by rw [Real.sq_sqrt hκ.le]
    _ ≤ x.value * y.value := hlower x y hxQ hyQ hxy

/-- The quantitative value-product separation makes the effective failure set
subsingleton.  Positivity of both actual values is used before multiplying the
two strict failure inequalities. -/
theorem atMostOneEventualEffectiveException_of_valueProductSeparation
    (hsep : EventualTatuzawaValueProductSeparation) :
    AtMostOneEventualEffectiveException := by
  intro η hη
  obtain ⟨Q, c, hc, hproduct⟩ := hsep η hη
  refine ⟨Q, c, hc, ?_⟩
  intro x hx y hy
  rcases hx with ⟨hxQ, hxfail⟩
  rcases hy with ⟨hyQ, hyfail⟩
  by_contra hxy
  have hlower := hproduct x y hxQ hyQ hxy
  have hstrict :
      x.value * y.value <
        (c * x.powerScale η) * (c * y.powerScale η) := by
    calc
      x.value * y.value < (c * x.powerScale η) * y.value :=
        mul_lt_mul_of_pos_right hxfail (PrimitiveQuadraticDatum.value_pos y)
      _ < (c * x.powerScale η) * (c * y.powerScale η) :=
        mul_lt_mul_of_pos_left hyfail
          (mul_pos hc (PrimitiveQuadraticDatum.powerScale_pos η x))
  exact (not_lt_of_ge hlower) hstrict

/-- At most one eventual effective exception implies the raw Landau--Siegel
lower bound.  If an exception exists, its strictly positive value defines one
additional coefficient; otherwise the effective coefficient already works.
The possible exception is absorbed before the finite-conductor bridge is
invoked. -/
theorem rawLandauSiegelLowerBound_of_atMostOneEventualEffectiveException
    (hunique : AtMostOneEventualEffectiveException) :
    RawLandauSiegelLowerBound := by
  apply DirichletCharacter.quadratic_LFunction_one_lower_of_eventual_forall_exponents
  intro η hη
  obtain ⟨Q, cEff, hcEff, hsub⟩ := hunique η hη
  suffices hbound : ∃ c : ℝ, 0 < c ∧
      ∀ x : PrimitiveQuadraticDatum, Q ≤ x.modulus → c * x.powerScale η ≤ x.value by
    obtain ⟨c, hc, hbound⟩ := hbound
    refine ⟨Q, c, hc, ?_⟩
    intro q _ χ hq hprimitive hquad hnonprincipal
    let x : PrimitiveQuadraticDatum :=
      { modulus := q
        modulus_ne := NeZero.ne q
        character := χ
        isPrimitive := hprimitive
        square_eq_one := hquad
        ne_one := hnonprincipal }
    simpa [x, PrimitiveQuadraticDatum.powerScale, PrimitiveQuadraticDatum.value] using hbound x hq
  by_cases hne : (tatuzawaEffectiveFailureSet η cEff Q).Nonempty
  · obtain ⟨exceptional, hexceptional⟩ := hne
    let cExceptional : ℝ := exceptional.value / exceptional.powerScale η
    have hcExceptional : 0 < cExceptional :=
      div_pos (PrimitiveQuadraticDatum.value_pos exceptional)
        (PrimitiveQuadraticDatum.powerScale_pos η exceptional)
    refine ⟨min cEff cExceptional, lt_min hcEff hcExceptional, ?_⟩
    intro x hxQ
    by_cases hxfail : x ∈ tatuzawaEffectiveFailureSet η cEff Q
    · have hxeq : x = exceptional := hsub hxfail hexceptional
      rw [hxeq]
      calc
        min cEff cExceptional * exceptional.powerScale η ≤
            cExceptional * exceptional.powerScale η :=
          mul_le_mul_of_nonneg_right (min_le_right cEff cExceptional)
            (PrimitiveQuadraticDatum.powerScale_pos η exceptional).le
        _ = exceptional.value := by
          exact div_mul_cancel₀ exceptional.value
            (ne_of_gt (PrimitiveQuadraticDatum.powerScale_pos η exceptional))
    · have hnotlt : ¬ x.value < cEff * x.powerScale η := by
        intro hlt
        exact hxfail ⟨hxQ, hlt⟩
      exact (mul_le_mul_of_nonneg_right (min_le_left cEff cExceptional)
        (PrimitiveQuadraticDatum.powerScale_pos η x).le).trans (not_lt.mp hnotlt)
  · refine ⟨cEff, hcEff, ?_⟩
    intro x hxQ
    apply not_lt.mp
    intro hlt
    exact hne ⟨x, hxQ, hlt⟩

/-- The Tatuzawa route to the raw Landau--Siegel lower bound with a genuinely
analytic final source: quantitative separation of the values of any two
distinct primitive quadratic characters. -/
theorem rawLandauSiegelLowerBound_of_eventualTatuzawaValueProductSeparation
    (hsep : EventualTatuzawaValueProductSeparation) :
    RawLandauSiegelLowerBound :=
  rawLandauSiegelLowerBound_of_atMostOneEventualEffectiveException
    (atMostOneEventualEffectiveException_of_valueProductSeparation hsep)

/-- Final Tatuzawa reduction with no uniqueness-shaped source: the remaining
input is the direct two-character value-product power lower bound. -/
theorem rawLandauSiegelLowerBound_of_eventualTatuzawaValueProductPowerLowerBound
    (hprod : EventualTatuzawaValueProductPowerLowerBound) :
    RawLandauSiegelLowerBound :=
  rawLandauSiegelLowerBound_of_eventualTatuzawaValueProductSeparation
    (eventualTatuzawaValueProductSeparation_of_powerLowerBound hprod)

end

end AnalyticNumberTheory.LargeSieve
