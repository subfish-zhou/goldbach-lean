import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighPayloadNormalization
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitJDensity

namespace Wu2008DoubleSieve.HighSourcePayload
open Real

/-- The actual prime-output unit sources retain their same-phi J payload.
The compact cap is used only for selecting rho and the error threshold. -/
theorem mother_unit_pair_JTheta (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
        secondFunctionalHighUnitPair p N δ (convolutionWuWindows N Δ V) ≤
          (2/(1-2*δ))*unitTheta N δ Δ V p +
            ε*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨ρ,hr,T0,hT0,h0⟩ := mass_theta_density_slack k hδ hδhi
    (show (0:ℝ) ≤ 2000 by norm_num) (half_pos hε)
  obtain ⟨T1,_,h1⟩ := mother_unit_pair_J_density k hδ hδhi hr (half_pos hε)
  refine ⟨max T0 T1,hT0.trans (le_max_left _ _),?_⟩
  intro N hN hn i Δ V hb p hp hs
  have hnorm := h0 N ((le_max_left _ _).trans hN) i Δ V hb
    (fun d => unitPair N d δ p) (fun d _ => unitPair_bounds N d δ hp hs)
  have hsource := h1 N ((le_max_right _ _).trans hN) hn i Δ V hb p hp hs
  dsimp only at hsource
  change secondFunctionalHighUnitPair p N δ (convolutionWuWindows N Δ V) ≤ _ at hsource
  simp only [mul_div_assoc] at hsource
  change _ ≤ (2/(1-2*δ))*unitTheta N δ Δ V p + _ at hnorm
  nlinarith only [hsource,hnorm]

/-- The actual unit and nonunit high sources share one original-weight integral payload. -/
theorem mother_high_pair_pairedTheta (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
        secondFunctionalHighUnitPair p N δ (convolutionWuWindows N Δ V) +
          HighNonunit.actualSource N δ p (convolutionWuWindows N Δ V) false +
          HighNonunit.actualSource N δ p (convolutionWuWindows N Δ V) true ≤
        (2/(1-2*δ))*pairedTheta N δ Δ V p +
          ε*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT0,h0⟩ := mother_unit_pair_JTheta k hδ hδhi (half_pos hε)
  obtain ⟨T1,_,h1⟩ := HighNonunit.actual_source_pair_kTheta k hδ hδhi (half_pos hε)
  refine ⟨max T0 T1,hT0.trans (le_max_left _ _),?_⟩
  intro N hN hn i Δ V hb p hp hs
  have hu := h0 N ((le_max_left _ _).trans hN) hn i Δ V hb p hp hs
  have hn' := h1 N ((le_max_right _ _).trans hN) hn i Δ V hb p hp hs
  rw [pairedTheta_eq]
  nlinarith only [hu,hn']

end Wu2008DoubleSieve.HighSourcePayload

namespace Wu2008DoubleSieve
open FourthRowPhiOmega2 HighSourcePayload

/-- The physical mother keeps all four actual J/K integrals at the same d and phi.
There is no separate unit logarithmic cap in the leading coefficient. -/
theorem secondFunctional_high_paired_theta_joined_source
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 < p.s) (hs3 : p.s ≤ 3) (hS : 3 ≤ p.S) (hS5 : p.S ≤ 5)
    (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
          (4 * wuUpperCoefficient p.S + wuUpperCoefficient p.kappa1 -
            4 * wuImprovementLimit true δ p.S - wuImprovementLimit true δ p.kappa1 -
            J δ p.s p.S - J δ p.kappa2 p.S - J δ p.kappa3 p.S + ε) *
              boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) +
          secondFunctionalLowerGammaLedger p N δ (convolutionWuWindows N Δ V) +
          (2/(1-2*δ))*pairedTheta N δ Δ V p := by
  obtain ⟨T0,hT0,h0⟩ := secondFunctional_fourprime_nonunit_joined_source p hp hs hs3 hS hS5
    k hk hδ hδhi (half_pos hε)
  obtain ⟨T1,_,h1⟩ := mother_high_pair_pairedTheta k hδ (by linarith) (half_pos hε)
  refine ⟨max T0 T1,hT0.trans (le_max_left _ _),?_⟩
  intro N hN hn i Δ V hb
  have hbase := h0 N ((le_max_left _ _).trans hN) hn i Δ V hb
  have hhigh := h1 N ((le_max_right _ _).trans hN) hn i Δ V hb p hp hs.le
  rw [secondFunctional_high_unit_ledger_partition] at hbase
  unfold secondFunctionalHighNonunitGammaLedger at hbase
  simp only [HighNonunit.actualSource, HighNonunit.word, Bool.false_eq_true, ↓reduceIte] at hhigh
  unfold secondFunctionalLowerGammaLedger
  nlinarith only [hbase,hhigh]

end Wu2008DoubleSieve
