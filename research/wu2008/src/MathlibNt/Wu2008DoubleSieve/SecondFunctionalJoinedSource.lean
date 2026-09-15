import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherSourceRows
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalPhiOmega2

/-! # Actual shared mother after the Phi/Omega2 substitution
All Gamma5--21 source counts remain literal. The two error budgets are
joined before the common threshold; no Gamma estimate is assumed here. -/
namespace Wu2008DoubleSieve
open Finset FourthRowPhiOmega2
open scoped Classical

/-- The actual paid mother consumes both Phi uppers and all three Omega2 lowers. -/
theorem secondFunctional_joined_source
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (hS : 3 ≤ p.S) (hS5 : p.S ≤ 5)
    (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
          (4 * wuUpperCoefficient p.S + wuUpperCoefficient p.kappa1 -
            4 * wuImprovementLimit true δ p.S - wuImprovementLimit true δ p.kappa1 -
            J δ p.s p.S - J δ p.kappa2 p.S - J δ p.kappa3 p.S + ε) *
              boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) +
          ∑ j ∈ Icc 5 21,
            secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) j := by
  have hδhalf : δ < 1 / 2 := by linarith
  have heps : 0 < ε / 2 := by positivity
  obtain ⟨A, hA4, hA⟩ := secondFunctionalMother_source k p hp hδ hδhalf heps
  obtain ⟨B, _, hB⟩ := SecondFunctionalPhiOmega2.actual_limit_block p hp hs hS hS5
    k hk hδ hδhi heps
  refine ⟨max A B, hA4.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb
  have ha := hA N ((le_max_left _ _).trans hN) he i Δ V hb
  have hb' := hB N ((le_max_right _ _).trans hN) he i Δ V hb
  simp only [secondFunctionalMotherRHS] at ha
  nlinarith only [ha, hb']

end Wu2008DoubleSieve
