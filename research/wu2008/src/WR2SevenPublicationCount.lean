import WR2GammaHighPublicationCount
import WR2OmegaHighPaid

noncomputable section
namespace WuPaper.R2Seven
open Wu2008DoubleSieve WuSource.SrcSingle Finset
open scoped Classical

/-- All seven published gains now bound the original prime counts. -/
theorem actual_publications {ε : ℝ} (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 7,
      psiCount j N ≤ (8*psiLogWeight j*(1-psiPublication j)+ε)*
        truncatedSixthMassScale N := by
  obtain ⟨T3,hT3,h3⟩ := R2GammaHigh.actual_three_publications he
  obtain ⟨T4,_,h4⟩ := R2OmegaHigh.actual_four_publications he
  refine ⟨max T3 T4,hT3.trans (le_max_left _ _),?_⟩
  intro N hN hn j
  refine Fin.addCases (m := 3) (n := 4) (fun i => ?_) (fun i => ?_) j
  · simpa only [psiPublication, Fin.addCases_left] using h3 N (by omega) hn i
  · have h := h4 N (by omega) hn i
    simpa only [R2OmegaHigh.publicationCoefficient, R2OmegaHigh.index,
      psiPublication, Fin.addCases_right, mul_comm, mul_left_comm, mul_assoc] using h

def sevenClassical : ℝ := 8*∑ j : Fin 7, psiLogWeight j

theorem sum_publication_coefficient :
    (∑ j : Fin 7, 8*psiLogWeight j*(1-psiPublication j)) =
      sevenClassical-psiSevenPaid := by
  simp only [mul_sub, mul_one, sum_sub_distrib, mul_assoc, ← mul_sum,
    sevenClassical, psiSevenPaid]

theorem actual_publication_gain {ε : ℝ} (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (∑ j : Fin 7, psiCount j N) ≤
        (sevenClassical-psiSevenPaid+ε)*truncatedSixthMassScale N := by
  obtain ⟨T,hT,h⟩ := actual_publications (show 0 < ε/7 by positivity)
  refine ⟨T,hT,?_⟩
  intro N hN hn
  have hs := sum_le_sum (s := univ) (fun j _ => h N hN hn j)
  rw [← sum_mul, sum_add_distrib, sum_publication_coefficient] at hs
  simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat,
    show (7:ℝ)*(ε/7)=ε by ring] using hs

end WuPaper.R2Seven
#print axioms WuPaper.R2Seven.actual_publication_gain
