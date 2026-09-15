import MathlibNt.Wu2008DoubleSieve.SecondFunctionalGamma9IntegralUpper
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFullKThetaMother

namespace Wu2008DoubleSieve
open Finset Real FourthRowPhiOmega2 HighSourcePayload
open scoped Classical

/-- The actual Gamma9 integral upper is consumed with the original total epsilon.
All other Gamma terms and the same-phi combined kernel payload are unchanged. -/
theorem secondFunctional_gamma9_integral_mother
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
          (∑ j ∈ (Icc 5 15).erase 9, secondFunctionalMotherGammaSum p N δ
            (convolutionWuWindows N Δ V) j) +
          (2/(1-2*δ))*secondFunctionalCombinedTheta N δ Δ V p := by
  obtain ⟨T0,hT0,h0⟩ := secondFunctional_full_kTheta_mother p hp hs hs3 hS hS5
    k hk hδ hδhi (half_pos hε)
  obtain ⟨T9,hT9,h9⟩ := secondFunctionalMother_gamma9_integral_upper k hδ
    (by linarith) (half_pos hε)
  refine ⟨max T0 T9, hT0.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb
  have h := h0 N ((le_max_left _ _).trans hN) he i Δ V hb
  rw [← sum_erase_add _ _ (show (9 : ℕ) ∈ Icc 5 15 by norm_num)] at h
  have hg := h9 N ((le_max_right _ _).trans hN) he i Δ V hb p hp hs.le
  nlinarith only [h, hg]

end Wu2008DoubleSieve
