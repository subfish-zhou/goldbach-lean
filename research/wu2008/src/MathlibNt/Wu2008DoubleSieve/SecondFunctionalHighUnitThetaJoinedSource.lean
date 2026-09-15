import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitThetaCap
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeNonunit

open scoped BigOperators Classical
namespace Wu2008DoubleSieve
open Finset FourthRowPhiOmega2 HighUnitSource

/-- The two literal high-order unit sources, with all five original cutoffs. -/
noncomputable def secondFunctionalHighUnitPair (p : SecondFunctionalParameters)
    {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  FourPrimeUnit.source N W (fun d => wuLocalCutoff N δ d p.S)
    (fun d => wuLocalCutoff N δ d p.kappa1) (fun d => wuLocalCutoff N δ d p.kappa2)
    (fun d => wuLocalCutoff N δ d p.kappa3) (fun d => wuLocalCutoff N δ d p.s) word20 +
  FourPrimeUnit.source N W (fun d => wuLocalCutoff N δ d p.S)
    (fun d => wuLocalCutoff N δ d p.kappa1) (fun d => wuLocalCutoff N δ d p.kappa2)
    (fun d => wuLocalCutoff N δ d p.kappa3) (fun d => wuLocalCutoff N δ d p.s) word21

/-- Only the high-order unit parts are removed; the original nonunit masks remain. -/
noncomputable def secondFunctionalHighNonunitGammaLedger (p : SecondFunctionalParameters)
    {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  (∑ j ∈ Icc 5 15, secondFunctionalMotherGammaSum p N δ W j) +
  (∑ j : Fin 4, FourPrimeNonunit.actualEnvelope N δ p W j) +
  FourPrimeNonunit.source N W (fun d => wuLocalCutoff N δ d p.S)
    (fun d => wuLocalCutoff N δ d p.kappa1) (fun d => wuLocalCutoff N δ d p.kappa2)
    (fun d => wuLocalCutoff N δ d p.kappa3) (fun d => wuLocalCutoff N δ d p.s) word20 +
  FourPrimeNonunit.source N W (fun d => wuLocalCutoff N δ d p.S)
    (fun d => wuLocalCutoff N δ d p.kappa1) (fun d => wuLocalCutoff N δ d p.kappa2)
    (fun d => wuLocalCutoff N δ d p.kappa3) (fun d => wuLocalCutoff N δ d p.s) word21

theorem secondFunctional_high_unit_ledger_partition (p : SecondFunctionalParameters)
    {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) :
    secondFunctionalSwitchedGammaLedger p N δ W =
      secondFunctionalHighNonunitGammaLedger p N δ W + secondFunctionalHighUnitPair p N δ W := by
  have h20 := weighted_partition20 N W (fun d => wuLocalCutoff N δ d p.S)
    (fun d => wuLocalCutoff N δ d p.kappa1) (fun d => wuLocalCutoff N δ d p.kappa2)
    (fun d => wuLocalCutoff N δ d p.kappa3) (fun d => wuLocalCutoff N δ d p.s)
  have h21 := weighted_partition21 N W (fun d => wuLocalCutoff N δ d p.S)
    (fun d => wuLocalCutoff N δ d p.kappa1) (fun d => wuLocalCutoff N δ d p.kappa2)
    (fun d => wuLocalCutoff N δ d p.kappa3) (fun d => wuLocalCutoff N δ d p.s)
  unfold secondFunctionalSwitchedGammaLedger secondFunctionalHighNonunitGammaLedger
    secondFunctionalHighUnitPair FourPrimeNonunit.source secondFunctionalMotherGammaSum
  linarith only [h20,h21]

/-- Physical consumption in the source mother, with one total epsilon budget.
The explicit logarithmic correction is not identified with the original I or switched K. -/
theorem secondFunctional_high_unit_theta_joined_source
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
          secondFunctionalHighNonunitGammaLedger p N δ (convolutionWuWindows N Δ V) := by
  have hhalf : 0 < ε/2 := by positivity
  have hδhalf : δ < 1/2 := by linarith
  obtain ⟨T1,hT1,h1⟩ := secondFunctional_fourprime_nonunit_joined_source p hp hs hs3 hS hS5
    k hk hδ hδhi hhalf
  obtain ⟨T2,_,h2⟩ := HighUnitSieve.mother_unit_pair_theta k hδ hδhalf hhalf
  refine ⟨max T1 T2,hT1.trans (le_max_left _ _),?_⟩
  intro N hN hn i Δ V hb
  have hbase := h1 N ((le_max_left _ _).trans hN) hn i Δ V hb
  have hu := h2 N ((le_max_right _ _).trans hN) hn i Δ V hb p hp hs.le
  dsimp only at hu
  rw [secondFunctional_high_unit_ledger_partition] at hbase
  unfold secondFunctionalHighUnitPair at hbase
  nlinarith only [hbase,hu]

end Wu2008DoubleSieve
