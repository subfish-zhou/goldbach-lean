import Wu18938Campaign.M1.Confirmed.ClassicalExtended
import HighFullLocal

noncomputable section

namespace Wu18938Campaign.M1.Confirmed

open Wu2008DoubleSieve Finset Real
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open scoped Classical

theorem roughBox_upper_main_bounded (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s : ℝ, 3 / 2 ≤ s → s ≤ 10 →
      convolutionRosserMain N (convolutionWuWindows N Δ V) true
        (wuVariableRosserLevel N δ) (fun d => wuLocalCutoff N δ d s) ≤
        (wuUpperCoefficient s + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,_,hT⟩ := HighFull.main_upper hδ.le (show 0 < η / 10 by positivity) he
  refine ⟨max 4 T,le_max_left _ _,?_⟩
  intro N hN heven i Δ V hb s hs hs10
  apply hT N (by omega) heven i (convolutionWuWindows N Δ V)
    (fun j p hp => (mem_primeWindow.mp hp).1) _ s hs hs10
  intro d hd
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hb.support_pos hd
  have hprod := (le_div_iff₀ hdpos).mp (hb.remaining d hd)
  have hdpow : (d : ℝ) ≤ (N : ℝ) ^ (1 / 2 - δ) / (N : ℝ) ^ η := by
    apply (le_div_iff₀ (rpow_pos_of_pos hNpos η)).mpr
    nlinarith only [hprod]
  rw [← rpow_sub hNpos] at hdpow
  simpa only [show (1 / 2 - δ - 10 * (η / 10) : ℝ) = 1 / 2 - δ - η by ring] using hdpow

theorem roughBox_upper_leaf_bounded (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s : ℝ, 1 ≤ s → s ≤ 10 →
      wuBoxPhi N δ (convolutionWuWindows N Δ V) s ≤
        (wuUpperCoefficient s + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT04,hmain⟩ := roughBox_upper_main_bounded m hη hδ (half_pos he)
  obtain ⟨T1,_,hrem⟩ := roughBox_rosser_remainder m hη hδ (half_pos he)
  obtain ⟨T2,_,hbase⟩ := roughBox_upper_leaf m hη hδ he
  refine ⟨max T0 (max T1 T2),hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb s hs hs10
  by_cases hslo : 3 / 2 ≤ s
  · have hM := hmain N (by omega) heven i Δ V hb s hslo hs10
    have hR := hrem N (by omega) i Δ V hb true (fun d => wuLocalCutoff N δ d s)
    have hfinite : wuBoxPhi N δ (convolutionWuWindows N Δ V) s ≤
        convolutionRosserMain N (convolutionWuWindows N Δ V) true
          (wuVariableRosserLevel N δ) (fun d => wuLocalCutoff N δ d s) +
        convolutionRosserRemainder N (convolutionWuWindows N Δ V) true
          (wuVariableRosserLevel N δ) (fun d => wuLocalCutoff N δ d s) := by
      unfold wuBoxPhi convolutionSieveCount convolutionRosserMain convolutionRosserRemainder
      rw [← sum_add_distrib]
      apply sum_le_sum
      intro d hd
      have hv := variableRosser_geometry (hb.support_geometry (by omega) hη hδ hd).2.2.1 hs
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (ordinaryRosser_upper_finite hv.1 hv.2.1) (Nat.cast_nonneg _)
    have hr := (le_abs_self _).trans hR
    nlinarith only [hfinite,hM,hr]
  · have hs3 : s ≤ 3 := by linarith
    have ha : wuUpperCoefficient s = 1 := jr1965F_normalized_initial (by linarith) hs3
    rw [ha]
    exact hbase N (by omega) heven i Δ V hb s hs hs3

end Wu18938Campaign.M1.Confirmed
