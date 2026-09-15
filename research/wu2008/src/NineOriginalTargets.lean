import NineComparison

namespace NineFeedbackStrength
open Wu2008DoubleSieve ActualNineFeedback NodeExtension
open scoped BigOperators
noncomputable section

/-- Direct weighted-feedback improvement, not a numerically chosen iterate. -/
theorem paid_feedback_le_Ainf (i : Fin 9) :
    publication i+matrixApply feedbackMatrix publication i ≤ FeedbackLimit.Ainf i := by
  rw [Ainf_affine]
  exact add_le_add (publication_le_base i)
    (matrixApply_mono feedbackMatrix_nonneg publication_le_Ainf i)

/-- One common radius pays the actual original bases AND their exact weighted feedback. -/
theorem actual_paid_feedback_same_delta : ∃ d : ℝ,0<d ∧ d≤1/10 ∧
    ∀ δ : ℝ,0<δ → δ≤d → ∀ i : Fin 9,
      publication i+matrixApply feedbackMatrix publication i≤actualNine δ i := by
  obtain ⟨d,hd,hcap,hs⟩ := actual_same_delta
  refine ⟨d,hd,hcap,?_⟩
  intro δ hδ hr
  have hn := actualNine_nonneg hδ (hr.trans hcap)
  have hp : ∀ i,publication i≤actualNine δ i := by
    intro i
    exact (le_add_of_nonneg_right (matrixApply_nonneg feedbackMatrix_nonneg hn i)).trans (hs δ hδ hr i)
  intro i
  exact (add_le_add le_rfl (matrixApply_mono feedbackMatrix_nonneg hp i)).trans (hs δ hδ hr i)

/-- Author's unchanged Table 1 numbers at s=2.2,...,3.0, recorded ONLY as targets.
Source: Wu 2008 author TeX, lines 775--950. -/
def originalH : Fin 9 → ℝ :=
  ![0.0223939,0.0217196,0.0202876,0.0181433,0.0158644,
    0.0129923,0.0100686,0.0078162,0.0072943]

/-- The remaining nine targets are genuine weighted integrals, not printed matrix premises. -/
theorem original_integrals_to_subsolution
    (hc : ∀ i : Fin 4,originalH (i.castAdd 5)≤publication (i.castAdd 5)+
      coupledFeedback (coupledRow i) originalH)
    (hf : ∀ i : Fin 5,originalH (Fin.natAdd 4 i)≤Wu04FirstCore.publication i+
      firstFeedback originalH (firstNode i) (firstS i)) :
    ∀ i : Fin 9,originalH i≤publication i+matrixApply feedbackMatrix originalH i := by
  intro i
  change originalH i≤publication i+(∑ k,feedbackMatrix i k*originalH k)
  rw [← feedback_expansion]
  refine Fin.addCases (m := 4) (n := 5) (fun j => ?_) (fun j => ?_) i
  · rw [coupled_feedback_index]
    exact hc j
  · rw [publication_first,first_feedback_index]
    exact hf j

/-- CONDITIONAL target consumer: hc and hf have not been proved in this development. -/
theorem original_H_le_Ainf_of_integrals
    (hc : ∀ i : Fin 4,originalH (i.castAdd 5)≤publication (i.castAdd 5)+
      coupledFeedback (coupledRow i) originalH)
    (hf : ∀ i : Fin 5,originalH (Fin.natAdd 4 i)≤Wu04FirstCore.publication i+
      firstFeedback originalH (firstNode i) (firstS i)) :
    ∀ i : Fin 9,originalH i≤FeedbackLimit.Ainf i := by
  apply subsolution_le_Ainf
  intro i
  exact (original_integrals_to_subsolution hc hf i).trans
    (add_le_add (publication_le_base i) le_rfl)

/-- CONDITIONAL, but with the comparison theorem genuinely proved and the delta shared. -/
theorem original_H_actual_of_integrals
    (hc : ∀ i : Fin 4,originalH (i.castAdd 5)≤publication (i.castAdd 5)+
      coupledFeedback (coupledRow i) originalH)
    (hf : ∀ i : Fin 5,originalH (Fin.natAdd 4 i)≤Wu04FirstCore.publication i+
      firstFeedback originalH (firstNode i) (firstS i)) :
    ∃ d : ℝ,0<d ∧ d≤1/10 ∧ ∀ δ : ℝ,0<δ → δ≤d →
      ∀ i : Fin 9,originalH i≤actualNine δ i := by
  obtain ⟨d,hd,hcap,hcomp⟩ := actual_comparison_same_delta
  exact ⟨d,hd,hcap,fun δ hδ hr => hcomp δ hδ hr originalH (original_integrals_to_subsolution hc hf)⟩

end
end NineFeedbackStrength
