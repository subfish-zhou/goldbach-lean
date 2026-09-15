import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitFiniteToClosedK
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitSourceKQuadrature
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitKThetaNormalization

namespace Wu2008DoubleSieve.HighNonunit
open Finset Real
open scoped Classical

/-- Original actual sources, through finite transport and genuine quadrature, to the
same-phi paired K payload on the original Theta weights. No density slack remains. -/
theorem actual_source_pair_kTheta (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
        actualSource N δ p (convolutionWuWindows N Δ V) false +
          actualSource N δ p (convolutionWuWindows N Δ V) true ≤
        (2/(1-2*δ))*sourceKTheta N δ Δ V p +
          ε*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  have he : 0 < ε/3 := by positivity
  obtain ⟨ρ,hr,T0,hT0,h0⟩ := sourceLegalKMass_theta_density_slack k hδ hδhi he
  let A := (1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))
  have hD : 0 < 1-2*δ := by linarith
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  obtain ⟨T1,_,h1⟩ := actual_source_pair_finite_density k hδ hδhi hr he
  obtain ⟨T2,_,h2⟩ := sourceClosedKMass_pair_theta k hδ hδhi hA he
  refine ⟨max T0 (max T1 T2),hT0.trans (le_max_left _ _),?_⟩
  intro N hN hn i Δ V hb p hp hs
  have hN0 := (le_max_left T0 (max T1 T2)).trans hN
  have hN1 := (le_max_left T1 T2).trans ((le_max_right T0 (max T1 T2)).trans hN)
  have hN2 := (le_max_right T1 T2).trans ((le_max_right T0 (max T1 T2)).trans hN)
  have hN4 := hT0.trans hN0
  have hC : 0 ≤ wuSingularSeries N/log N := div_nonneg
    (wuSingularSeries_pos N (by omega)).le
    (log_pos (by exact_mod_cast (show 1 < N by omega))).le
  have hnorm := h0 N hN0 i Δ V hb p hp hs
  have hsource := h1 N hN1 hn i Δ V hb p hp hs
  have herror := h2 N hN2 i Δ V hb p hp hs
  have hfinite := mul_le_mul_of_nonneg_right
    (finiteBuchstabMain_pair_le_sourceClosedKMass hN4 hδ hδhi hb p hp hs)
    (mul_nonneg hA hC)
  have hdiff := mul_le_mul_of_nonneg_left
    (le_abs_self ((sourceClosedKMass N δ Δ V p false + sourceClosedKMass N δ Δ V p true) -
      (sourceLegalKMass N δ Δ V p false + sourceLegalKMass N δ Δ V p true)))
    (mul_nonneg hA hC)
  change _ ≤ _ * (A * wuSingularSeries N / log N) + _ at hsource
  rw [mul_div_assoc] at hsource
  change A * (wuSingularSeries N/log N) * _ ≤ _ at hnorm
  nlinarith only [hsource, hfinite, hdiff, herror, hnorm]

end Wu2008DoubleSieve.HighNonunit

namespace Wu2008DoubleSieve
open Finset Real FourthRowPhiOmega2 HighUnitSource
open scoped Classical

/-- The physical five-Phi mother with its original lower Gamma ledger and actual paired K.
The sourceKTheta payload is not replaced by a numerical constant or by the original Theta. -/
theorem secondFunctional_high_nonunit_kTheta_joined_source
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 < p.s) (hs3 : p.s ≤ 3) (hS : 3 ≤ p.S) (hS5 : p.S ≤ 5)
    (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
          (4 * wuUpperCoefficient p.S + wuUpperCoefficient p.kappa1 -
            4 * wuImprovementLimit true δ p.S - wuImprovementLimit true δ p.kappa1 -
            J δ p.s p.S - J δ p.kappa2 p.S - J δ p.kappa3 p.S +
            (2/(1-2*δ)) * (unitLogCap20 (1/p.kappa2) (1/p.kappa3) (1/p.s) +
              unitLogCap21 (1/p.kappa3) (1/p.s)) + ε) *
              boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) +
          secondFunctionalLowerGammaLedger p N δ (convolutionWuWindows N Δ V) +
          (2/(1-2*δ))*HighNonunit.sourceKTheta N δ Δ V p := by
  obtain ⟨T0,hT0,hbase⟩ := secondFunctional_high_unit_theta_joined_source p hp hs hs3 hS hS5
    k hk hδ hδhi (half_pos hε)
  obtain ⟨T1,_,hK⟩ := HighNonunit.actual_source_pair_kTheta k hδ
    (by linarith) (half_pos hε)
  refine ⟨max T0 T1,hT0.trans (le_max_left _ _),?_⟩
  intro N hN hn i Δ V hb
  have h0 := hbase N ((le_max_left T0 T1).trans hN) hn i Δ V hb
  have h1 := hK N ((le_max_right T0 T1).trans hN) hn i Δ V hb p hp hs.le
  simp only [HighNonunit.actualSource, HighNonunit.word, Bool.false_eq_true, ↓reduceIte] at h1
  unfold secondFunctionalHighNonunitGammaLedger at h0
  unfold secondFunctionalLowerGammaLedger
  nlinarith only [h0,h1]

end Wu2008DoubleSieve
