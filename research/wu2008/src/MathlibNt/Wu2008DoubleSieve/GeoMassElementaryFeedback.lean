import MathlibNt.Wu2008DoubleSieve.GeoMassElementaryPrimitives
import MathlibNt.Wu2008DoubleSieve.GeoMassLogFeedback

/-! Integral-free evaluation of the unchanged twelve masses and actual inverse feedback.
The compact head and the fixed-delta source are not numerically evaluated. -/
namespace Wu2008DoubleSieve.SecondFunctionalGeometricMass.Elementary
open Real MotherPair FourthRowPhiOmega2 SecondFunctionalJointTail
open SecondFunctionalPositive

noncomputable def elementaryMass (p : SecondFunctionalParameters) : ℝ :=
  let a := 1/p.S
  let b := 1/p.kappa1
  let c := 1/p.kappa2
  let e := 1/p.kappa3
  let f := 1/p.s
  (Real.log (f/c) * elementaryMomentZero 1 b c +
    Real.log (c/b) * elementaryMomentOne 0 c e +
    Real.log (f/e) * elementaryMomentZero 1 a b + lowerThreeLog p +
    Real.log (b/a) * elementaryMomentOne 0 c f + lowerFiveLog p) +
  ((Real.log (e/c) / 2 * elementaryMomentOne 2 e f + elementaryMomentOne 4 e f / 24) +
    (elementaryMomentOne 2 c e / 2 + Real.log (f/e) / 2 * elementaryMomentZero 2 c e +
      Real.log (e/c)^2 / 2 * elementaryMomentOne 0 e f +
      Real.log (c/b) * elementaryMomentOne 1 e f))

theorem oneDimensionalMass_eq_elementary (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) :
    FullReduction.oneDimensionalMass p = elementaryMass p := by
  obtain ⟨ha,hab,hbc,hce,hef,_hf⟩ := LowerTripleContinuous.mother_compact_parameters p hp hs
  have ha0 : 0 < 1/p.S := by linarith
  have hb0 := ha0.trans_le hab
  have hc0 := hb0.trans_le hbc
  have he0 := hc0.trans_le hce
  unfold FullReduction.oneDimensionalMass elementaryMass
  dsimp only
  rw [logMoment_zero_eq 1 hb0 hbc, logMoment_one_eq 0 hc0 hce,
    logMoment_zero_eq 1 ha0 hab, logMoment_one_eq 0 hc0 (hce.trans hef),
    logMoment_one_eq 2 he0 hef, logMoment_one_eq 4 he0 hef,
    logMoment_one_eq 2 hc0 hce, logMoment_zero_eq 2 hc0 hce,
    logMoment_one_eq 0 he0 hef, logMoment_one_eq 1 he0 hef]

/-- All twelve original mass terms are retained, now with no residual integral. -/
theorem M_elementary (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) : SecondFunctionalJointTail.M p = elementaryMass p := by
  rw [FullReduction.M_one_dimensional p hp hs, oneDimensionalMass_eq_elementary p hp hs]

noncomputable def elementarySource (p : SecondFunctionalParameters) (δ : ℝ)
    (m : ℕ) (P : ℝ) : ℝ :=
  wuUpperCoefficient p.s +
    (4 * wuImprovementLimit true δ p.S + wuImprovementLimit true δ p.kappa1 +
      J δ p.s p.S + J δ p.kappa2 p.S + J δ p.kappa3 p.S -
      (4 * wuUpperCoefficient p.S + wuUpperCoefficient p.kappa1 +
        SecondFunctionalCoupledFeedback.classical p + (2/(1-2*δ)) *
          (omega3XIntegralEnvelope p.kappa3 p.kappa1 +
            max (compactSup p P)
              (exp (-eulerMascheroniConstant) * elementaryMass p +
                4 * elementaryMass p / (m.factorial : ℝ)))))/5

theorem logarithmicSource_eq_elementary (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (δ : ℝ) (m : ℕ) (P : ℝ) :
    FullReduction.logarithmicSource p δ m P = elementarySource p δ m P := by
  unfold FullReduction.logarithmicSource elementarySource
  rw [oneDimensionalMass_eq_elementary p hp hs]

/-- Only the mass is evaluated; this is equality of the original sources. -/
theorem compact_source_eq_elementary (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (δ : ℝ) (m : ℕ) (P : ℝ) :
    SecondFunctionalCompactTail.source p δ m P = elementarySource p δ m P := by
  rw [FullReduction.compact_source_eq_logarithmic p hp hs,
    logarithmicSource_eq_elementary p hp hs]

/-- The accepted actual Q and H consumer, with the same head, tail and fixed delta. -/
theorem actual_elementary_lower (m : Fin 4 → ℕ) (hm : ∀ i, 3 ≤ m i)
    (P : Fin 4 → ℝ) (hP : ∀ i, max 2 (((m i : ℝ) + 6) / 2) ≤ P i)
    {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    ActualMatrixInverse.Q.mulVec (fun i => elementarySource (parameters i) δ (m i) (P i)) ≤
      actualVector δ := by
  have h := FullReduction.actual_logarithmic_lower m hm P hP hδ hδhi
  have he (i : Fin 4) := logarithmicSource_eq_elementary (parameters i)
    (parameters_analytic i).mother (parameters_analytic i).two_lt_s.le δ (m i) (P i)
  simpa only [he] using h

end Wu2008DoubleSieve.SecondFunctionalGeometricMass.Elementary
