import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherPairGainUpper
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleKThetaMother

namespace Wu2008DoubleSieve
open Finset Real FourthRowPhiOmega2 HighSourcePayload
open scoped Classical

/-- The four actual H integrals are consumed by the normalized five-Phi mother.
The six same-actual-phi KTheta terms and the fixed delta loss are unchanged. -/
theorem secondFunctional_pair_gain_kTheta_mother
    (p : SecondFunctionalParameters) (hp : MotherPair.AnalyticParameters p)
    (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
          (4 * wuUpperCoefficient p.S + wuUpperCoefficient p.kappa1 -
            4 * wuImprovementLimit true δ p.S - wuImprovementLimit true δ p.kappa1 -
            J δ p.s p.S - J δ p.kappa2 p.S - J δ p.kappa3 p.S +
            (2/(1-2*δ))*omega3XIntegralEnvelope p.kappa3 p.kappa1 +
            MotherPair.fourIntegralUpper p δ + ε) *
              boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) +
          (2/(1-2*δ))*((∑ j : Fin 6, LowerTripleSourceK.sourceKTheta N δ Δ V p j) +
            secondFunctionalCombinedTheta N δ Δ V p) := by
  obtain ⟨T0,hT0,hm⟩ := secondFunctional_lower_triple_kTheta_mother
    p hp.mother hp.two_lt_s hp.s_le_three hp.three_le_S hp.S_le_five
    k hk hδ hδhi (half_pos hε)
  obtain ⟨T1,_,hg⟩ := MotherPair.original_four_gain_upper p hp k hk hδ hδhi (half_pos hε)
  refine ⟨max T0 T1,hT0.trans (le_max_left _ _),?_⟩
  intro N hN he i Δ V hb
  have hm' := hm N ((le_max_left _ _).trans hN) he i Δ V hb
  have hg' := hg N ((le_max_right _ _).trans hN) he i Δ V hb
  norm_num [Finset.sum_Icc_succ_top] at hm'
  linarith only [hm',hg']

end Wu2008DoubleSieve
