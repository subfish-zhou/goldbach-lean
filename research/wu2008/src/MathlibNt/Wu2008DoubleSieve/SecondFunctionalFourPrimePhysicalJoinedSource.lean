import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeNonunitActualFamily
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighPairedThetaJoinedSource

namespace Wu2008DoubleSieve
open Finset FourthRowPhiOmega2 HighSourcePayload
open scoped Classical

/-- Original nonunit counts enter the physical family without additional source screens. -/
theorem fourprime_source_le_physical_primeMass {i N : ℕ} {δ Δ : ℝ}
    (V : Fin i → ℝ) (p : SecondFunctionalParameters) (hN : 4 ≤ N) (he : Even N)
    (j : Fin 4) :
    secondFunctionalFourPrimeNonunitSum p N δ (convolutionWuWindows N Δ V) j ≤
      (FourPrimeNonunit.sourceFamily N δ Δ V p j).primeMass := by
  rw [(FourPrimeNonunit.sourceFamily_dictionary N δ Δ V p j).1]
  exact FourPrimeNonunit.actual_source_le p (convolutionWuWindows N Δ V)
    (fun _ hd => boxConvolutionSupport_pos
      (fun _ _ hq => (mem_convolutionWuWindows.mp hq).1.pos) hd) hN he j

/-- The lower ledger retains every original coefficient and all four labelled families. -/
theorem fourprime_physical_lowerLedger_eq {i : ℕ} (N : ℕ) (δ Δ : ℝ)
    (V : Fin i → ℝ) (p : SecondFunctionalParameters) :
    secondFunctionalLowerGammaLedger p N δ (convolutionWuWindows N Δ V) =
      (∑ j ∈ Icc 5 15, secondFunctionalMotherGammaSum p N δ
        (convolutionWuWindows N Δ V) j) +
      ∑ j : Fin 4, (FourPrimeNonunit.sourceFamily N δ Δ V p j).primeMass := by
  have hd (j : Fin 4) := (FourPrimeNonunit.sourceFamily_dictionary N δ Δ V p j).1
  simp only [secondFunctionalLowerGammaLedger, hd]

/-- Actual physical four-prime consumers alongside the already paired high payload.
This is an exact interface substitution, not a density estimate for these four families. -/
theorem secondFunctional_fourprime_physical_joined_source
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
          ((∑ j ∈ Icc 5 15, secondFunctionalMotherGammaSum p N δ
            (convolutionWuWindows N Δ V) j) +
            ∑ j : Fin 4, (FourPrimeNonunit.sourceFamily N δ Δ V p j).primeMass) +
          (2/(1-2*δ))*pairedTheta N δ Δ V p := by
  obtain ⟨T,hT4,hT⟩ := secondFunctional_high_paired_theta_joined_source
    p hp hs hs3 hS hS5 k hk hδ hδhi hε
  refine ⟨T,hT4,?_⟩
  intro N hN he i Δ V hb
  have h := hT N hN he i Δ V hb
  rw [fourprime_physical_lowerLedger_eq] at h
  exact h

end Wu2008DoubleSieve
