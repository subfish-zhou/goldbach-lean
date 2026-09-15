import MathlibNt.Wu2008DoubleSieve.SecondFunctionalZeroWidthFinite

/-! The zero-width finite mother: enlarge only Gamma16, before closed endpoints
for the absent Gamma17--19 sources can enter the ledger. -/
namespace Wu2008DoubleSieve.SecondFunctionalZeroWidth
open Finset FourthRowPhiOmega2
open scoped Classical

theorem ledger_le (p : SecondFunctionalParameters) (heq : p.kappa3 = p.s)
    {i N : ℕ} {δ : ℝ} (W : Fin i → Finset ℕ)
    (hdpos : ∀ d ∈ boxConvolutionSupport W, 0 < d) (hN : 4 ≤ N) (he : Even N) :
    secondFunctionalNonunitGammaLedger p N δ W ≤
      retained p N δ W + FourPrimeNonunit.actualEnvelope N δ p W 0 := by
  rw [ledger_eq p heq]
  exact add_le_add le_rfl (FourPrimeNonunit.actual_source_le p W hdpos hN he 0)

/-- The original coefficient, fixed delta and a single epsilon, with an explicit
retained ledger and only the Gamma16 four-label nonunit envelope. -/
theorem joined_source
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (heq : p.kappa3 = p.s)
    (hs : 2 < p.s) (hs3 : p.s ≤ 3) (hS : 3 ≤ p.S) (hS5 : p.S ≤ 5)
    (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
          (4 * wuUpperCoefficient p.S + wuUpperCoefficient p.kappa1 -
            4 * wuImprovementLimit true δ p.S - wuImprovementLimit true δ p.kappa1 -
            J δ p.s p.S - J δ p.kappa2 p.S - J δ p.kappa3 p.S + ε) *
              boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) +
          (retained p N δ (convolutionWuWindows N Δ V) +
            FourPrimeNonunit.actualEnvelope N δ p (convolutionWuWindows N Δ V) 0) := by
  obtain ⟨T,hT4,hT⟩ := secondFunctional_unit_joined_source p hp hs hs3 hS hS5
    k hk hδ hδhi hε
  refine ⟨T,hT4,?_⟩
  intro N hN he i Δ V hb
  have hN4 := hT4.trans hN
  have hδhalf : δ < 1 / 2 := by linarith
  exact (hT N hN he i Δ V hb).trans (add_le_add le_rfl
    (ledger_le p heq (convolutionWuWindows N Δ V)
      (fun _ hd => (omega3_source_support_le_Q (by omega) hδ hδhalf hb hd).1) hN4 he))

/-- Regression on the actual row3 record, not a surrogate tuple. -/
theorem row3_joined_source (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) SecondFunctionalParameters.row3.s ≤
          (4 * wuUpperCoefficient SecondFunctionalParameters.row3.S + wuUpperCoefficient SecondFunctionalParameters.row3.kappa1 -
            4 * wuImprovementLimit true δ SecondFunctionalParameters.row3.S - wuImprovementLimit true δ SecondFunctionalParameters.row3.kappa1 -
            J δ SecondFunctionalParameters.row3.s SecondFunctionalParameters.row3.S - J δ SecondFunctionalParameters.row3.kappa2 SecondFunctionalParameters.row3.S - J δ SecondFunctionalParameters.row3.kappa3 SecondFunctionalParameters.row3.S + ε) *
              boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) +
          (retained SecondFunctionalParameters.row3 N δ (convolutionWuWindows N Δ V) +
            FourPrimeNonunit.actualEnvelope N δ SecondFunctionalParameters.row3 (convolutionWuWindows N Δ V) 0) := by
  exact joined_source SecondFunctionalParameters.row3 SecondFunctionalParameters.row3_motherAdmissible
    SecondFunctionalParameters.row3_last_eq
    (by norm_num [SecondFunctionalParameters.row3]) (by norm_num [SecondFunctionalParameters.row3])
    (by norm_num [SecondFunctionalParameters.row3]) (by norm_num [SecondFunctionalParameters.row3]) k hk hδ hδhi hε

/-- Regression on the actual row4 record, not a surrogate tuple. -/
theorem row4_joined_source (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) SecondFunctionalParameters.row4.s ≤
          (4 * wuUpperCoefficient SecondFunctionalParameters.row4.S + wuUpperCoefficient SecondFunctionalParameters.row4.kappa1 -
            4 * wuImprovementLimit true δ SecondFunctionalParameters.row4.S - wuImprovementLimit true δ SecondFunctionalParameters.row4.kappa1 -
            J δ SecondFunctionalParameters.row4.s SecondFunctionalParameters.row4.S - J δ SecondFunctionalParameters.row4.kappa2 SecondFunctionalParameters.row4.S - J δ SecondFunctionalParameters.row4.kappa3 SecondFunctionalParameters.row4.S + ε) *
              boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) +
          (retained SecondFunctionalParameters.row4 N δ (convolutionWuWindows N Δ V) +
            FourPrimeNonunit.actualEnvelope N δ SecondFunctionalParameters.row4 (convolutionWuWindows N Δ V) 0) := by
  exact joined_source SecondFunctionalParameters.row4 SecondFunctionalParameters.row4_motherAdmissible
    SecondFunctionalParameters.row4_last_eq
    (by norm_num [SecondFunctionalParameters.row4]) (by norm_num [SecondFunctionalParameters.row4])
    (by norm_num [SecondFunctionalParameters.row4]) (by norm_num [SecondFunctionalParameters.row4]) k hk hδ hδhi hε

end Wu2008DoubleSieve.SecondFunctionalZeroWidth
