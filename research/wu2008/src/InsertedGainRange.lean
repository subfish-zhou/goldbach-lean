import InsertedGainActual
import MathlibNt.Wu2008DoubleSieve.PhiMonotone

namespace InsertedGain
open Finset Real Filter Wu2008DoubleSieve HighTheta HighBoxRecovery
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open scoped Classical Topology
noncomputable section

/-- Monotonicity transports the actual insertion gain to the whole initial
positive parameter range. This is a count statement, not a presumed H family. -/
theorem inserted_initial_range {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      ∀ U : ℝ, ActualInsertion N δ Δ U V → ∀ s : ℝ, 0 < s → s ≤ 29/10 →
      0 < boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ (Fin.cons U V)) ∧
      wuBoxPhi N δ (convolutionWuWindows N Δ (Fin.cons U V)) s ≤
        (1-1/10000)*boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ (Fin.cons U V)) := by
  have ha : wuUpperCoefficient (29/10) = 1 := by
    unfold wuUpperCoefficient
    rw [jr1965F_eq_of_le_three (by norm_num)]
    field_simp
  obtain ⟨T0,hT04,hupper⟩ := inserted_upper hδ hδhi
  obtain ⟨T1,hsmall⟩ := eventually_atTop.mp delta_eventually_small
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN he Δ hlo hhi V hV hr U hU s hs hst
  have hN0 : T0 ≤ N := by omega
  have hN1 : T1 ≤ N := by omega
  have hN4 := hT04.trans hN0
  obtain ⟨hθ,hu,_⟩ := hupper N hN0 he Δ hlo hhi V hV hr U hU
  obtain ⟨hΔ,hΔhi⟩ := hsmall N hN1 Δ hlo hhi
  have hg := inserted_box_geometry (show 2 ≤ N by omega) hδhi hΔ hΔhi hV hr hU
  have hq := (HighCross.support_admission _ (show 2 ≤ N by omega)
    (show 0 < highEta by norm_num [highEta]) (fun j p hp => (hg.1 j p hp).1) hg.2).2
  rw [ha] at hu
  exact ⟨hθ,(wuBoxPhi_mono_parameter _ (fun d hd => (hq d hd).le) hs hst).trans hu⟩

end
end InsertedGain
