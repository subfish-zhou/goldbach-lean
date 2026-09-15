import BuchstabCountFinal
import CoverMassFinal

namespace PositiveH
open Finset Real Wu2008DoubleSieve HighTheta HighBoxRecovery
open scoped Classical
noncomputable section

/-- The original actual count now has a positive lower correction. All grid
terminals are eliminated by their original existence theorem; the threshold
is chosen before the moving box and parameter. -/
theorem original_lower {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      ∀ s : ℝ, 2 ≤ s → s ≤ 29/10 →
      0 < boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) ∧
      (log (s-1)+(1/10000)*log (2/(s-1))-ε)*
        boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) ≤
        wuBoxPhi N δ (convolutionWuWindows N Δ V) s := by
  obtain ⟨T0,hT04,hcount⟩ := BuchstabCount.original_lower hδ hδhi (show 0 < ε/2 by positivity)
  obtain ⟨T1,_,hmass⟩ := CoverMass.original_cover_upper hδ hδhi (show 0 < ε/2 by positivity)
  obtain ⟨T2,_,htheta⟩ := ActualLogGain.original_remainder_relative 0 hδ hδhi
    (by norm_num : (0 : ℝ) < 1)
  refine ⟨max T0 (max T1 T2),hT04.trans (le_max_left _ _),?_⟩
  intro N hN he Δ hlo hhi V hV hrect s hs hsmax
  have hN0 : T0 ≤ N := by omega
  have hN1 : T1 ≤ N := by omega
  have hN2 : T2 ≤ N := by omega
  have hN4 := hT04.trans hN0
  obtain ⟨hθ,_⟩ := htheta N hN2 Δ hlo hhi V hV hrect
  have hΔ := (CoverMass.delta_log_bound
    (log_pos (show (1 : ℝ) < N by exact_mod_cast (show 1 < N by omega))) hlo hhi).1
  obtain ⟨_,r,hr,_⟩ := HighOmega2.original_terminal (show 2 ≤ N by omega)
    hδhi hΔ hV hrect hs (show s ≤ 3 by linarith)
  have hc := hcount N hN0 he Δ hlo hhi V hV hrect s hs hsmax r hr
  have hm := hmass N hN1 Δ hlo hhi V hV hrect s hs hsmax r hr.1 hr.2
  have hp := mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 1-1/10000)
  refine ⟨hθ,?_⟩
  rw [log_div (by norm_num : (2 : ℝ) ≠ 0) (by linarith : s-1 ≠ 0)] at hp ⊢
  nlinarith only [hc,hp,mul_nonneg hε.le hθ.le]

end
end PositiveH
