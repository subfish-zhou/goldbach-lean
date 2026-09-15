import MathlibNt.Wu2008DoubleSieve.GeoMassReductionActual
import MathlibNt.Wu2008DoubleSieve.GeoMassReductionLogFibres

/-! Shared literal carriers for the already reviewed ordered-mass argument.
No integral formula or Fubini theorem is asserted by these definitions. -/
namespace Wu2008DoubleSieve.SecondFunctionalGeometricMass
open Set MeasureTheory

/-- Closed ordered coordinates, also meaningful on the zero-dimensional space. -/
def orderedDomain (n : ℕ) (a b : ℝ) : Set (Fin n → ℝ) :=
  {t | (∀ i, t i ∈ Icc a b) ∧ Monotone t}

noncomputable def pureOrderedMass (n : ℕ) (a b : ℝ) : ℝ :=
  ∫ t in orderedDomain n a b, continuousDensity t

noncomputable def selectedOrderedMass {n : ℕ} (j : Fin n) (a b : ℝ) : ℝ :=
  SecondFunctionalJointTail.geometricMass j (orderedDomain n a b)

theorem mem_orderedDomain {n : ℕ} (a b : ℝ) (t : Fin n → ℝ) :
    t ∈ orderedDomain n a b ↔ (∀ i, a ≤ t i ∧ t i ≤ b) ∧ Monotone t := Iff.rfl

end Wu2008DoubleSieve.SecondFunctionalGeometricMass
