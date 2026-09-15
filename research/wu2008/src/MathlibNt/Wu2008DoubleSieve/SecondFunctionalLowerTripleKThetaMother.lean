import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleKThetaDensity
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleGroupedMother

namespace Wu2008DoubleSieve
open Finset Real FourthRowPhiOmega2 HighSourcePayload
open scoped Classical

/-- The six actual-phi true-li KTheta terms enter five-Phi.
Rho is internal; the fixed delta loss and the other original terms remain. -/
theorem secondFunctional_lower_triple_kTheta_mother
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
            (2/(1-2*δ))*omega3XIntegralEnvelope p.kappa3 p.kappa1 + ε) *
              boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) +
          (∑ j ∈ Icc 5 8, secondFunctionalMotherGammaSum p N δ
            (convolutionWuWindows N Δ V) j) +
          (2/(1-2*δ))*((∑ j : Fin 6, LowerTripleSourceK.sourceKTheta N δ Δ V p j) +
            secondFunctionalCombinedTheta N δ Δ V p) := by
  obtain ⟨T0,hT0,hm⟩ := secondFunctional_lower_triple_grouped_mother p hp hs hs3 hS hS5
    k hk hδ hδhi (half_pos hε)
  have hδhalf : δ < 1/2 := by linarith
  obtain ⟨T1,_,hd⟩ := LowerTripleSourceK.source_six_kTheta_density
    k hδ hδhalf (half_pos hε)
  refine ⟨max T0 T1,hT0.trans (le_max_left _ _),?_⟩
  intro N hN he i Δ V hb
  have hm' := hm N ((le_max_left _ _).trans hN) he i Δ V hb
  have hd' := (hd N ((le_max_right _ _).trans hN) he i Δ V hb p hp hs.le).2
  nlinarith only [hm',hd']

end Wu2008DoubleSieve
