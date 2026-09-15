import MathlibNt.Wu2008DoubleSieve.GeoMassFullReduction
import MathlibNt.Wu2008DoubleSieve.ActualMatrixInverseConsumer

/-! The exact twelve-mass logarithmic expression enters the actual inverse feedback. -/
namespace Wu2008DoubleSieve.SecondFunctionalGeometricMass.FullReduction
open Real MotherPair FourthRowPhiOmega2 SecondFunctionalJointTail
open SecondFunctionalPositive

noncomputable def logarithmicSource (p : SecondFunctionalParameters) (δ : ℝ)
    (m : ℕ) (P : ℝ) : ℝ :=
  wuUpperCoefficient p.s +
    (4 * wuImprovementLimit true δ p.S + wuImprovementLimit true δ p.kappa1 +
      J δ p.s p.S + J δ p.kappa2 p.S + J δ p.kappa3 p.S -
      (4 * wuUpperCoefficient p.S + wuUpperCoefficient p.kappa1 +
        SecondFunctionalCoupledFeedback.classical p + (2/(1-2*δ)) *
          (omega3XIntegralEnvelope p.kappa3 p.kappa1 +
            max (compactSup p P)
              (exp (-eulerMascheroniConstant) * oneDimensionalMass p +
                4 * oneDimensionalMass p / (m.factorial : ℝ)))))/5

/-- This is an exact rewrite of the unchanged compact source, not a new bound. -/
theorem compact_source_eq_logarithmic (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (δ : ℝ) (m : ℕ) (P : ℝ) :
    SecondFunctionalCompactTail.source p δ m P = logarithmicSource p δ m P := by
  unfold SecondFunctionalCompactTail.source SecondFunctionalCompactTail.cost
    SecondFunctionalCompactTail.kernelUpper logarithmicSource
  rw [M_one_dimensional p hp hs]

/-- Actual H now consumes the full twelve-mass one-dimensional expression through the actual Q. -/
theorem actual_logarithmic_lower (m : Fin 4 → ℕ) (hm : ∀ i, 3 ≤ m i)
    (P : Fin 4 → ℝ) (hP : ∀ i, max 2 (((m i : ℝ) + 6) / 2) ≤ P i)
    {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    ActualMatrixInverse.Q.mulVec (fun i => logarithmicSource (parameters i) δ (m i) (P i)) ≤
      actualVector δ := by
  have h := ActualMatrixInverse.compact_lower m hm P hP hδ hδhi
  change ActualMatrixInverse.Q.mulVec
    (fun i => SecondFunctionalCompactTail.source (parameters i) δ (m i) (P i)) ≤
      actualVector δ at h
  have he (i : Fin 4) := compact_source_eq_logarithmic (parameters i)
    (parameters_analytic i).mother (parameters_analytic i).two_lt_s.le δ (m i) (P i)
  simpa only [he] using h

end Wu2008DoubleSieve.SecondFunctionalGeometricMass.FullReduction
