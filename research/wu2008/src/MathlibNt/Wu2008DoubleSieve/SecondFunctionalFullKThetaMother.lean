import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeKThetaJoinedSource
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimePhysicalJoinedSource

namespace Wu2008DoubleSieve
open Finset Real FourthRowPhiOmega2 HighSourcePayload
open scoped Classical

/-- One literal payload at the same actual supported-d phi, without taking an envelope. -/
noncomputable def secondFunctionalCombinedKernel (N d : ℕ) (δ : ℝ)
    (p : SecondFunctionalParameters) : ℝ :=
  paired N d δ p + ∑ j : Fin 4, FourPrimeNonunit.sourceLegalK N d δ p j

noncomputable def secondFunctionalCombinedTheta (N : ℕ) (δ Δ : ℝ) {i : ℕ}
    (V : Fin i → ℝ) (p : SecondFunctionalParameters) : ℝ :=
  theta N δ Δ V (fun d => secondFunctionalCombinedKernel N d δ p)

/-- Exact summation at the original true-li/totient weights. -/
theorem secondFunctionalCombinedTheta_eq (N : ℕ) (δ Δ : ℝ) {i : ℕ}
    (V : Fin i → ℝ) (p : SecondFunctionalParameters) :
    secondFunctionalCombinedTheta N δ Δ V p = pairedTheta N δ Δ V p +
      ∑ j : Fin 4, FourPrimeNonunit.sourceKTheta N δ Δ V p j := by
  rw [← FourPrimeNonunit.sourceKTheta_sum]
  simp only [secondFunctionalCombinedTheta, secondFunctionalCombinedKernel,
    pairedTheta, theta, mul_add, sum_add_distrib]

/-- All original four-prime sources and both high sources are now genuine integral payloads.
No zero-width hypothesis is imposed; Gamma5 through Gamma15 remain literal. -/
theorem secondFunctional_full_kTheta_mother
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
          (∑ j ∈ Icc 5 15, secondFunctionalMotherGammaSum p N δ
            (convolutionWuWindows N Δ V) j) +
          (2/(1-2*δ))*secondFunctionalCombinedTheta N δ Δ V p := by
  obtain ⟨T0,hT0,hbase⟩ := secondFunctional_fourprime_physical_joined_source
    p hp hs hs3 hS hS5 k hk hδ hδhi (half_pos hε)
  obtain ⟨T1,_,hK⟩ := FourPrimeNonunit.source_four_kTheta k hδ (by linarith) (half_pos hε)
  refine ⟨max T0 T1,hT0.trans (le_max_left _ _),?_⟩
  intro N hN he i Δ V hb
  have h0 := hbase N ((le_max_left _ _).trans hN) he i Δ V hb
  have h1 := (hK N ((le_max_right _ _).trans hN) he i Δ V hb p hp hs.le).2
  rw [secondFunctionalCombinedTheta_eq]
  nlinarith only [h0,h1]

end Wu2008DoubleSieve
