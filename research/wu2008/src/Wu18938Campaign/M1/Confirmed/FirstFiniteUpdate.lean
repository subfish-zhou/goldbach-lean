import Wu18938Campaign.M1.Confirmed.ClassicalBounded
import Wu18938Campaign.M1.Confirmed.SeedOmega2

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Rebox

open Wu2008DoubleSieve Finset Real
open scoped Classical Interval

theorem first_classical_update_bounded (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 → 2 ≤ t - t / s →
      wuBoxPhi N δ (convolutionWuWindows N Δ V) s ≤
        (wuUpperCoefficient s - firstFunctionalGainPsi δ s t + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT04,h0⟩ := roughBox_first_integral m hη hδ hδhi (half_pos he)
  obtain ⟨T1,_,h1⟩ := classical_omega2 m hη hδ (half_pos he)
  obtain ⟨T2,_,h2⟩ := roughBox_upper_leaf_bounded m hη hδ (half_pos he)
  refine ⟨max T0 (max T1 T2),hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb s t hs hst ht ht5 hratio
  have ha := h0 N (by omega) heven i Δ V hb s t hs hst (by linarith)
  have hb' := h1 N (by omega) heven i Δ V hb s t hs hst ht ht5 hratio
  have hc := h2 N (by omega) heven i Δ V hb t (by linarith) (by linarith)
  have henv := mul_le_mul_of_nonneg_left
    (omega3_envelope hb (by omega) hη hδ hs hst (by linarith))
    (show 0 ≤ 2 / (1 - 2 * δ) from div_nonneg (by norm_num) (by linarith))
  unfold firstFunctionalGainPsi
  nlinarith only [ha,hb',hc,henv]

theorem first_seed_update (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      wuBoxPhi N δ (convolutionWuWindows N Δ V) 3 ≤
        (wuUpperCoefficient 3 - firstFunctionalGainPsi δ 3 (9 / 2) -
          HighSixPhase7.seed / 468 + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT04,h0⟩ := roughBox_first_integral m hη hδ (by linarith) (half_pos he)
  obtain ⟨T1,_,h1⟩ := seed_omega2 m hη hδ hδhi (half_pos he)
  obtain ⟨T2,_,h2⟩ := roughBox_upper_leaf_bounded m hη hδ (half_pos he)
  refine ⟨max T0 (max T1 T2),hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb
  have ha := h0 N (by omega) heven i Δ V hb 3 (9 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  have hb' := h1 N (by omega) heven i Δ V hb
  have hc := h2 N (by omega) heven i Δ V hb (9 / 2) (by norm_num) (by norm_num)
  have henv := mul_le_mul_of_nonneg_left
    (omega3_envelope hb (s := 3) (t := 9 / 2) (by omega) hη hδ
      (by norm_num) (by norm_num) (by norm_num))
    (show 0 ≤ 2 / (1 - 2 * δ) from div_nonneg (by norm_num) (by linarith))
  unfold firstFunctionalGainPsi
  norm_num only [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num,
    show (1 : ℝ) - 1 / (9 / 2) = 7 / 9 by norm_num]
  nlinarith only [ha,hb',hc,henv]

end Wu18938Campaign.M1.Confirmed.Rebox
