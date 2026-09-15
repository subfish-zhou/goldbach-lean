import SrcNineAnalyticCostIdentity

noncomputable section
namespace WuSource.SrcNine.Analytic
open Set MeasureTheory Wu2008DoubleSieve ActualNineFeedback NodeExtension
open scoped BigOperators Interval

def extendedSourceIntegral (p : SecondFunctionalParameters) : Fin 13 → ℝ → ℝ :=
  ![omega3XIntegral p.kappa3 p.kappa1,
    rawTriple p 0, rawTriple p 1, rawTriple p 2, rawTriple p 3, rawTriple p 4, rawTriple p 5,
    rawFour p 0, rawFour p 1, rawFour p 2, rawFour p 3, rawFive p, rawSix p]

def extendedSourceI (p : SecondFunctionalParameters) (i : Fin 13) : ℝ :=
  sSup (extendedSourceIntegral p i '' Ici 2)

theorem thirteen_separate_sum (p : SecondFunctionalParameters) :
    (∑ i : Fin 13, extendedSourceI p i) = extendedSeparateCost p := by
  simp only [extendedSourceI, extendedSourceIntegral, extendedSeparateCost, separateTwelve,
    rawEnvelope, omega3XIntegralEnvelope, Fin.sum_univ_succ]
  dsimp only [Matrix.cons_val]
  ring

theorem thirteen_cost_identity (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) :
    coupledCostMass p = (∑ i : Fin 13, extendedSourceI p i) +
      sSup ((fun phi => unitSum p phi - illegalSum p phi -
        synchronizationLoss p phi) '' Ici 2) := by
  rw [thirteen_separate_sum]
  exact coupledCostMass_corrected p hp hs

theorem supported_source_split {i k N d : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) :
    (∑ j : Fin 6, LowerTripleSourceK.sourceIntegralK N d δ p j) +
      secondFunctionalCombinedKernel N d δ p + illegalSum p (omega3XPhi N d δ) =
      rawSum p (omega3XPhi N d δ) + unitSum p (omega3XPhi N d δ) := by
  rw [← SecondFunctionalCoupled.kernel_actual]
  exact kernel_literal_split p hp hs
    (SecondFunctionalCoupled.actual_phi_ge_two hN hδ hδhi hb hd)

theorem source_theta_bound {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) :
    (∑ j : Fin 6, LowerTripleSourceK.sourceKTheta N δ Δ V p j) +
      secondFunctionalCombinedTheta N δ Δ V p ≤
      (separateTwelve p + correctionSup p) *
        boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  rw [← jointSup_corrected p hp hs]
  exact (SecondFunctionalCoupled.theta_scalarization hN hδ hδhi hb p hp hs).2

theorem corrected_actual_lower {p : SecondFunctionalParameters}
    (hp : CoupledGeometry p) {δ : ℝ} (hδ : 0 < δ) (hr : δ ≤ WuSource.SrcNine.d) :
    Wu08OriginalPsiRecovery.classicalNumerator p / 5 -
      2 * ((∑ i : Fin 13, extendedSourceI p i) + correctionSup p) /
        (5 * (1 - 2 * δ)) +
      coupledFeedback p (actualNine δ) ≤ wuImprovementLimit true δ p.s := by
  rw [thirteen_separate_sum, ← coupledCostMass_corrected p hp.1.mother hp.1.two_lt_s.le]
  exact WuSource.SrcNine.coupled_source_actual hp hδ hr

theorem exact_source_net (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (δ : ℝ) :
    Wu08OriginalPsiRecovery.classicalNumerator p / 5 -
      2 * coupledCostMass p / (5 * (1 - 2 * δ)) =
    Wu08OriginalPsiRecovery.classicalNumerator p / 5 -
      2 * (∑ i : Fin 13, extendedSourceI p i) / (5 * (1 - 2 * δ)) -
      2 * correctionSup p / (5 * (1 - 2 * δ)) := by
  rw [thirteen_separate_sum, coupledCostMass_corrected p hp hs]
  ring

end WuSource.SrcNine.Analytic
