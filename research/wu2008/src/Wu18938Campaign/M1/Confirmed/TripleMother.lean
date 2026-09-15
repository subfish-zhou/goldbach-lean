import Wu18938Campaign.M1.Confirmed.TripleIntegral
import Wu18938Campaign.M1.Confirmed.FourMother

noncomputable section

namespace Wu18938Campaign.M1.Confirmed

open Wu2008DoubleSieve Finset Real
open scoped Classical

theorem roughBox_mother_twelve_paid (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 < p.s) (hs3 : p.s ≤ 3) (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
        4 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.S +
        wuBoxPhi N δ (convolutionWuWindows N Δ V) p.kappa1 -
        wuOmega2Sum N δ p.s p.S (convolutionWuWindows N Δ V) -
        wuOmega2Sum N δ p.kappa2 p.S (convolutionWuWindows N Δ V) -
        wuOmega2Sum N δ p.kappa3 p.S (convolutionWuWindows N Δ V) +
        (∑ j ∈ Icc 5 9, secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) j) +
        (2 / (1 - 2 * δ)) * (HighSourcePayload.pairedTheta N δ Δ V p +
          (∑ j : Fin 4, FourPrimeNonunit.sourceKTheta N δ Δ V p j) +
          ∑ j : Fin 6, LowerTripleSourceK.sourceKTheta N δ Δ V p j) +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT04,h0⟩ := Four.mother_six_high_paid p hp hs hs3 m hη hδ hδhi (half_pos he)
  obtain ⟨T1,_,h1⟩ := Triple.gamma_theta m hη hδ hδhi (show 0 < ε / 12 by positivity)
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb
  have hm := h0 N (by omega) heven i Δ V hb
  have ht := sum_le_sum (s := (univ : Finset (Fin 6)))
    (fun j _ => h1 N (by omega) heven i Δ V hb p hp hs.le j)
  have hsplit : (∑ j ∈ Icc 5 15,
      secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) j) =
      (∑ j ∈ Icc 5 9, secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) j) +
      ∑ j : Fin 6, secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) (10 + j.val) := by
    rw [show Icc 5 15 = Icc 5 9 ∪ Icc 10 15 by decide,sum_union (by decide)]
    congr 1
  rw [hsplit] at hm
  simp only [sum_add_distrib,← mul_sum,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at ht
  nlinarith only [hm,ht]

end Wu18938Campaign.M1.Confirmed
