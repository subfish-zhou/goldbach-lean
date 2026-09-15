import InsertedGainCover
import HighO2TerminalQuadrature

namespace CoverMass
open Finset Real Filter Wu2008DoubleSieve HighTheta HighBoxRecovery
open scoped Classical Topology Interval
noncomputable section

/-- The existing exact substitution at the constant coefficient, including s=2. -/
theorem kernel_exact {s t : ℝ} (hs : 2 ≤ s) (hst : s ≤ t) :
    (∫ u in (1-1/s)..(1-1/t), (1 : ℝ)/(u*(1-u))) = log ((t-1)/(s-1)) := by
  rw [← omega2_integral_substitution (fun _ => (1 : ℝ)) hs hst]
  exact integral_one_div_of_pos (by linarith) (by linarith)

/-- Actual selected prime mass; deletion of both p|d and p|N is already paid
in the imported fibre quadrature. All original tuple multiplicities remain. -/
theorem selected_original {δ ε : ℝ}
    (hδ : 0 ≤ δ) (hδhi : δ ≤ 50*highEta) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Δ : ℝ, 0 < Δ →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      ∀ s : ℝ, 2 ≤ s → s ≤ 29/10 →
      |reboxingPrimeSum true N δ s 3 (convolutionWuWindows N Δ V) (fun _ _ => 1) -
        log (2/(s-1))*boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V)| ≤
      ε*boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT4,hT⟩ := HighO2Terminal.original_selected_integral hδ hδhi hε
  refine ⟨T,hT4,?_⟩
  intro N hN Δ hΔ V hV hr s hs hs3
  have h := hT N hN Δ hΔ V hV hr (fun _ => (1 : ℝ))
    (fun _ _ _ _ _ => le_rfl) (by intro u hu; norm_num) s 3 hs (by linarith)
    (by norm_num) (by norm_num)
  rw [kernel_exact hs (by linarith)] at h
  norm_num only [show (3 : ℝ)-1=2 by norm_num] at h
  exact h

end
end CoverMass
