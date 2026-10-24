import NinePositivity
import FiniteComparison

namespace NineFeedbackStrength
open Wu2008DoubleSieve ActualNineFeedback NodeExtension
open scoped BigOperators
noncomputable section

theorem matrixApply_scale (r : ℝ) (z : Fin 9 → ℝ) (i : Fin 9) :
    matrixApply feedbackMatrix (fun k => r*z k) i = r*matrixApply feedbackMatrix z i :=
  FiniteFeedbackComparison.matrixApply_scale feedbackMatrix r z i

/-- Positive forcing propagates through the retained terminal feedback. -/
theorem supersolution_pos {b z : Fin 9 → ℝ}
    (hb : ∀ i,0≤b i) (hbp : ∀ i : Fin 9,i≠8 → 0<b i)
    (hz : ∀ i,0≤z i) (hs : ∀ i,b i+matrixApply feedbackMatrix z i≤z i) :
    ∀ i,0<z i :=
  FiniteFeedbackComparison.supersolution_pos 8 0 (by decide)
    feedbackMatrix_nonneg terminal_first_entry_pos hb hbp hz hs

/-- The generic comparison specializes to the actual original matrix. -/
theorem subsolution_le_supersolution {b x z : Fin 9 → ℝ}
    (hb : ∀ i,0≤b i) (hbp : ∀ i : Fin 9,i≠8 → 0<b i)
    (hz : ∀ i,0≤z i)
    (hx : ∀ i,x i≤b i+matrixApply feedbackMatrix x i)
    (hs : ∀ i,b i+matrixApply feedbackMatrix z i≤z i) : ∀ i,x i≤z i :=
  FiniteFeedbackComparison.subsolution_le_supersolution 8 0 (by decide)
    feedbackMatrix_nonneg terminal_first_entry_pos hb hbp hz hx hs

/-- The missing lower comparison is now proved for the original Ainf, without extra analytic premises. -/
theorem subsolution_le_Ainf {x : Fin 9 → ℝ}
    (hx : ∀ i,x i≤base i+matrixApply feedbackMatrix x i) : ∀ i,x i≤FeedbackLimit.Ainf i :=
  subsolution_le_supersolution base_nonneg (fun _ h => base_pos h) FeedbackLimit.Ainf_nonneg hx
    FeedbackLimit.Ainf_supersolution

/-- Uniqueness concerns the genuine affine system, not the printed matrix. -/
theorem affine_fixed_unique {z : Fin 9 → ℝ} (hz : ∀ i,0≤z i)
    (hs : ∀ i,z i=base i+matrixApply feedbackMatrix z i) : z=FeedbackLimit.Ainf := by
  funext i
  exact le_antisymm (subsolution_le_Ainf (fun j => (hs j).le) i)
    (FeedbackLimit.Ainf_le_supersolution hz (fun j => (hs j).ge) i)

/-- Every genuine publication subsolution bounds the same actual delta on all nine rows. -/
theorem actual_comparison_same_delta : ∃ d : ℝ,0<d ∧ d≤1/10 ∧
    ∀ δ : ℝ,0<δ → δ≤d → ∀ x : Fin 9 → ℝ,
      (∀ i,x i≤publication i+matrixApply feedbackMatrix x i) → ∀ i,x i≤actualNine δ i := by
  obtain ⟨d,hd,hcap,hs⟩ := actual_same_delta
  refine ⟨d,hd,hcap,?_⟩
  intro δ hδ hr x hx
  exact subsolution_le_supersolution publication_nonneg (fun _ h => publication_pos h)
    (actualNine_nonneg hδ (hr.trans hcap)) hx (hs δ hδ hr)

end
end NineFeedbackStrength
