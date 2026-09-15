import Wu18938Campaign.M1.Confirmed.PairIntegral
import Wu18938Campaign.M1.Confirmed.OmegaMother

noncomputable section

namespace Wu18938Campaign.M1.Confirmed

open Wu2008DoubleSieve MotherPair Finset Real
open scoped Classical

theorem roughBox_mother_integral_classical (p : SecondFunctionalParameters)
    (hp : AnalyticParameters p) (m : ℕ) {η δ τ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hτ : 0 < τ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
        4 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.S +
        wuBoxPhi N δ (convolutionWuWindows N Δ V) p.kappa1 -
        wuOmega2Sum N δ p.s p.S (convolutionWuWindows N Δ V) -
        wuOmega2Sum N δ p.kappa2 p.S (convolutionWuWindows N Δ V) -
        wuOmega2Sum N δ p.kappa3 p.S (convolutionWuWindows N Δ V) +
        (1 + τ) ^ 2 * (∑ j : Term, Pair.classicalIntegral p j) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) +
        (2 / (1 - 2 * δ)) * (HighSourcePayload.pairedTheta N δ Δ V p +
          (∑ j : Fin 4, FourPrimeNonunit.sourceKTheta N δ Δ V p j) +
          (∑ j : Fin 6, LowerTripleSourceK.sourceKTheta N δ Δ V p j) +
          HighSourcePayload.theta N δ Δ V
            (fun d => omega3XIntegral p.kappa3 p.kappa1 (omega3XPhi N d δ))) +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT04,h0⟩ := roughBox_mother_thirteen_paid p hp.mother hp.two_lt_s hp.s_le_three
    m hη hδ hδhi (half_pos he)
  obtain ⟨T1,_,h1⟩ := Pair.gamma_integral p hp m hη hδ hτ (show 0 < ε / 8 by positivity)
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb
  have hm := h0 N (by omega) heven i Δ V hb
  have h5 := h1 N (by omega) heven i Δ V hb .gammaFive
  have h6 := h1 N (by omega) heven i Δ V hb .gammaSix
  have h7 := h1 N (by omega) heven i Δ V hb .gammaSeven
  have h8 := h1 N (by omega) heven i Δ V hb .gammaEight
  simp only [Term.index] at h5 h6 h7 h8
  rw [show Icc 5 8 = {5,6,7,8} by decide] at hm
  simp only [sum_insert (by decide : (5 : ℕ) ∉ {6,7,8}),
    sum_insert (by decide : (6 : ℕ) ∉ {7,8}),
    sum_insert (by decide : (7 : ℕ) ∉ {8}),sum_singleton] at hm
  change 5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤ _
  have hsum : (∑ j : Term, Pair.classicalIntegral p j) =
      Pair.classicalIntegral p .gammaFive + Pair.classicalIntegral p .gammaSix +
      Pair.classicalIntegral p .gammaSeven + Pair.classicalIntegral p .gammaEight := by
    rw [show (univ : Finset Term) =
      {Term.gammaFive,Term.gammaSix,Term.gammaSeven,Term.gammaEight} by
        ext j
        cases j <;> simp]
    simp only [sum_insert (by decide : Term.gammaFive ∉
      {Term.gammaSix,Term.gammaSeven,Term.gammaEight}),
      sum_insert (by decide : Term.gammaSix ∉ {Term.gammaSeven,Term.gammaEight}),
      sum_insert (by decide : Term.gammaSeven ∉ {Term.gammaEight}),sum_singleton]
    ring
  rw [hsum]
  nlinarith only [hm,h5,h6,h7,h8]

end Wu18938Campaign.M1.Confirmed
