import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitDensity
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitThetaJoinedSource

open scoped BigOperators Classical
namespace Wu2008DoubleSieve
open Finset Real FourthRowPhiOmega2 HighUnitSource

/-- Remaining terms after paying the high unit sources and applying the high
nonunit sieve. The old four nonunit envelopes and Gamma 5--15 are unchanged. -/
noncomputable def secondFunctionalLowerGammaLedger (p : SecondFunctionalParameters)
    {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  (∑ j ∈ Icc 5 15, secondFunctionalMotherGammaSum p N δ W j) +
    ∑ j : Fin 4, FourPrimeNonunit.actualEnvelope N δ p W j

/-- Physical source-mother consumption: the high nonunit terms now have their
actual good raw masses and full fixed-delta density; all errors share one epsilon. -/
theorem secondFunctional_high_nonunit_density_joined_source
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 < p.s) (hs3 : p.s ≤ 3) (hS : 3 ≤ p.S) (hS5 : p.S ≤ 5)
    (k : ℕ) (hk : 1 ≤ k) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hρ : 0 < ρ) (hε : 0 < ε) :
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
          ((HighNonunit.sourceFamily N δ Δ V p false).coprimePart.mass +
            (HighNonunit.sourceFamily N δ Δ V p true).coprimePart.mass) *
            (((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))) *
              wuSingularSeries N / log N) := by
  have heps : 0 < ε/2 := half_pos hε
  have hdhalf : δ < 1/2 := by linarith
  obtain ⟨T0,hT0,hbase⟩ := secondFunctional_high_unit_theta_joined_source p hp hs hs3 hS hS5
    k hk hδ hδhi heps
  obtain ⟨T1,_,hdensity⟩ := HighNonunit.mother_nonunit_pair_density k hδ hdhalf hρ heps
  refine ⟨max T0 T1,hT0.trans (le_max_left _ _),?_⟩
  intro N hN he i Δ V hb
  have h0 := hbase N ((le_max_left T0 T1).trans hN) he i Δ V hb
  have h1 := hdensity N ((le_max_right T0 T1).trans hN) he i Δ V hb p hp hs.le
  simp only [HighNonunit.actualSource, HighNonunit.word, Bool.false_eq_true, ↓reduceIte] at h1
  unfold secondFunctionalHighNonunitGammaLedger at h0
  unfold secondFunctionalLowerGammaLedger
  nlinarith only [h0,h1]

end Wu2008DoubleSieve
