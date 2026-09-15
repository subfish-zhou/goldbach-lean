import MathlibNt.Wu2008DoubleSieve.SecondFunctionalJoinedSource
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeUnit

/-! # Removal of the four actual unit slices from the shared source ledger
Only Gamma16--19 lose their paid unit part. Every other source count and
all nonunit prefix fibres remain literal, including Gamma20 and Gamma21. -/
namespace Wu2008DoubleSieve
open Finset FourthRowPhiOmega2
open scoped Classical

noncomputable def secondFunctionalFourPrimeNonunitSum (p : SecondFunctionalParameters)
    {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) (j : Fin 4) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    FourPrimeUnit.prefixTerm false N d (wuLocalCutoff N δ d p.S)
      (wuLocalCutoff N δ d p.kappa1) (wuLocalCutoff N δ d p.kappa2)
      (wuLocalCutoff N δ d p.kappa3) (wuLocalCutoff N δ d p.s) (FourPrimeUnit.word j)

noncomputable def secondFunctionalNonunitGammaLedger (p : SecondFunctionalParameters)
    {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  (∑ j ∈ Icc 5 15, secondFunctionalMotherGammaSum p N δ W j) +
    (∑ j : Fin 4, secondFunctionalFourPrimeNonunitSum p N δ W j) +
    secondFunctionalMotherGammaSum p N δ W 20 + secondFunctionalMotherGammaSum p N δ W 21

/-- Finite interval bookkeeping for arbitrary real summands, not prime enumeration. -/
theorem secondFunctional_gamma_sum_split (F : ℕ → ℝ) :
    (∑ j ∈ Icc 5 21, F j) = (∑ j ∈ Icc 5 15, F j) +
      (∑ j : Fin 4, F (16 + j.val)) + F 20 + F 21 := by
  rw [sum_Icc_succ_top (a := 5) (b := 20) (by omega) F,
    sum_Icc_succ_top (a := 5) (b := 19) (by omega) F,
    sum_Icc_succ_top (a := 5) (b := 18) (by omega) F,
    sum_Icc_succ_top (a := 5) (b := 17) (by omega) F,
    sum_Icc_succ_top (a := 5) (b := 16) (by omega) F,
    sum_Icc_succ_top (a := 5) (b := 15) (by omega) F]
  simp [Fin.sum_univ_succ]
  ring

/-- The exact actual-source identity justifying removal of these units only. -/
theorem secondFunctional_gamma_unit_partition (p : SecondFunctionalParameters)
    {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) :
    (∑ j ∈ Icc 5 21, secondFunctionalMotherGammaSum p N δ W j) =
      secondFunctionalNonunitGammaLedger p N δ W +
        ∑ j : Fin 4, FourPrimeUnit.actualSource N δ p W j := by
  have hsum : (∑ j : Fin 4, secondFunctionalMotherGammaSum p N δ W (16 + j.val)) =
      (∑ j : Fin 4, FourPrimeUnit.actualSource N δ p W j) +
      (∑ j : Fin 4, secondFunctionalFourPrimeNonunitSum p N δ W j) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    exact (FourPrimeUnit.actual_gamma_partition N δ p W j).symm
  rw [secondFunctional_gamma_sum_split, hsum]
  unfold secondFunctionalNonunitGammaLedger
  ring

/-- Both prior errors and all four source-unit contributions share one epsilon.
No bound for the remaining nonunit mass or Gamma20/21 is assumed. -/
theorem secondFunctional_unit_joined_source
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
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
          secondFunctionalNonunitGammaLedger p N δ (convolutionWuWindows N Δ V) := by
  have hδhalf : δ < 1 / 2 := by linarith
  have heps : 0 < ε / 2 := by positivity
  obtain ⟨A, hA4, hA⟩ := secondFunctional_joined_source p hp hs.le hS hS5
    k hk hδ hδhi heps
  obtain ⟨B, _, hB⟩ := FourPrimeUnit.common_payment p hp hs hs3 k hδ hδhalf
    (K := 0) (by norm_num) heps
  refine ⟨max A B, hA4.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb
  have ha := hA N ((le_max_left _ _).trans hN) he i Δ V hb
  have hu := (hB N ((le_max_right _ _).trans hN) i Δ V hb).2.1.2.2
  rw [secondFunctional_gamma_unit_partition] at ha
  nlinarith only [ha, hu]

end Wu2008DoubleSieve
