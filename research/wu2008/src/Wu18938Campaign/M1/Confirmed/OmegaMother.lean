import Wu18938Campaign.M1.Confirmed.OmegaIntegral
import Wu18938Campaign.M1.Confirmed.TripleMother

noncomputable section

namespace Wu18938Campaign.M1.Confirmed

open Wu2008DoubleSieve Finset Real
open scoped Classical

theorem roughBox_gamma9_dictionary {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) :
    secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) 9 =
      wuOmega3Sum N δ p.kappa3 p.kappa1 (convolutionWuWindows N Δ V) := by
  unfold secondFunctionalMotherGammaSum wuOmega3Sum
  apply sum_congr rfl
  intro d hd
  obtain ⟨hab,hbc,hce,hef⟩ := roughBox_mother_cutoffs hb hN hη hδ p hp hd
  rw [secondFunctionalMother_gamma9_ordered_source N d N hab hbc hce hef]
  congr 1
  have h := congrArg (fun z : ℤ => (z : ℝ))
    (sum_s3_orderedTriples_descending N (wuLocalCutoff N δ d p.kappa1)
      (wuLocalCutoff N δ d p.kappa3)
      (fun t => (sourceSieveCount N (d * t.1 * t.2.1 * t.2.2) (d * t.1 * N) t.2.1 : ℤ)))
  simpa only [Int.cast_sum,Int.cast_natCast,wuOmega3] using h

theorem roughBox_gamma9_theta (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) 9 ≤
        (2 / (1 - 2 * δ)) * HighSourcePayload.theta N δ Δ V
          (fun d => omega3XIntegral p.kappa3 p.kappa1 (omega3XPhi N d δ)) +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT4,hT⟩ := Omega.source_theta m hη hδ hδhi he
  refine ⟨T,hT4,?_⟩
  intro N hN heven i Δ V hb p hp hs
  rw [roughBox_gamma9_dictionary hb (by omega) hη hδ p hp]
  exact hT N hN heven i Δ V hb p.kappa3 p.kappa1 (hs.trans hp.s_le_kappa3)
    (hp.kappa3_lt_kappa2.trans hp.kappa2_lt_kappa1).le (hp.kappa1_le_S.trans hp.S_le_ten)

theorem roughBox_mother_thirteen_paid (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
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
        (∑ j ∈ Icc 5 8, secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) j) +
        (2 / (1 - 2 * δ)) * (HighSourcePayload.pairedTheta N δ Δ V p +
          (∑ j : Fin 4, FourPrimeNonunit.sourceKTheta N δ Δ V p j) +
          (∑ j : Fin 6, LowerTripleSourceK.sourceKTheta N δ Δ V p j) +
          HighSourcePayload.theta N δ Δ V
            (fun d => omega3XIntegral p.kappa3 p.kappa1 (omega3XPhi N d δ))) +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT04,h0⟩ := roughBox_mother_twelve_paid p hp hs hs3 m hη hδ hδhi (half_pos he)
  obtain ⟨T1,_,h1⟩ := roughBox_gamma9_theta m hη hδ hδhi (half_pos he)
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb
  have hm := h0 N (by omega) heven i Δ V hb
  have ho := h1 N (by omega) heven i Δ V hb p hp hs.le
  have hsplit : (∑ j ∈ Icc 5 9, secondFunctionalMotherGammaSum p N δ
      (convolutionWuWindows N Δ V) j) =
      (∑ j ∈ Icc 5 8, secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) j) +
      secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) 9 := by
    rw [show Icc 5 9 = Icc 5 8 ∪ {9} by decide,sum_union (by decide),sum_singleton]
  rw [hsplit] at hm
  nlinarith only [hm,ho]

end Wu18938Campaign.M1.Confirmed
