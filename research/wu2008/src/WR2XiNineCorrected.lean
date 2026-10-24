import WR2XiPublicationCorrected
import NineBaselinePositivity
import FiniteComparison

/-! One actual nine-row system using the exact corrected second-functional kernel. -/
noncomputable section
namespace WuPaper.R2Xi
open NodeExtension Wu2008DoubleSieve MotherPair ActualNineFeedback NineFeedbackStrength
open scoped BigOperators

def correctedNineMatrix (i k : Fin 9) : ℝ :=
  Fin.addCases (m := 4) (n := 5)
    (fun r => Xi2CorrectedCoefficient r k)
    (fun r => firstFeedback (nodeBasis k) (firstNode r) (firstS r)) i

theorem correctedNineMatrix_nonneg (i k : Fin 9) : 0 ≤ correctedNineMatrix i k := by
  refine Fin.addCases (m := 4) (n := 5) (fun r => ?_) (fun r => ?_) i
  · simpa [correctedNineMatrix] using Xi2CorrectedCoefficient_nonneg r k
  · obtain ⟨hs, hs3, hS, hS5, hr⟩ := first_geometry r
    simpa [correctedNineMatrix] using firstFeedback_nonneg (nodeBasis_nonneg k)
      hs hS hS5 (hs3.trans hS) hr

theorem correctedNineMatrix_terminal_pos : 0 < correctedNineMatrix 8 0 := by
  change 0 < feedbackMatrix 8 0
  exact terminal_first_entry_pos

/-- All nine rows share one positive delta, with unchanged publication baselines. -/
theorem corrected_nine_actual : ∃ d : ℝ, 0 < d ∧ d ≤ 1/10 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d → ∀ i : Fin 9,
      publication i + matrixApply correctedNineMatrix (actualNine δ) i ≤ actualNine δ i := by
  let d := min Wu04RemainingStrongFourRows.commonRadius Wu04FirstPaid.commonRadius
  have hcap : d ≤ 1/10 := (min_le_left _ _).trans
    ((min_le_left _ _).trans (min_le_left _ _))
  refine ⟨d, lt_min Wu04RemainingStrongFourRows.commonRadius_pos
    Wu04FirstPaid.commonRadius_pos, hcap, ?_⟩
  intro δ hd hr i
  refine Fin.addCases (m := 4) (n := 5) (fun r => ?_) (fun r => ?_) i
  · have h := Xi2_publication_corrected r hd (hr.trans (min_le_left _ _))
    have hn : (gamma5OriginalRow r).s = upperNode (r.castAdd 5) := by
      have he := coupledRow_node r
      change (gamma5OriginalRow r).s = (22 + (r.val:ℝ))/10 at he
      simpa only [upperNode, Fin.val_castAdd] using he
    rw [hn] at h
    simpa [publication, secondPublication, matrixApply, correctedNineMatrix, actualNine] using h
  · have h := Wu04FirstPaid.five_actual hd (hr.trans hcap)
      (hr.trans (min_le_right _ _)) r
    obtain ⟨hs, hs3, hS, hS5, hgeom⟩ := first_geometry r
    rw [firstFeedback_expansion _ hs hS hS5 (hs3.trans hS) hgeom,
      first_node_index] at h
    simpa [publication_first, matrixApply, correctedNineMatrix, actualNine, first_node_index] using h

/-- Numerical subsolutions can now be consumed by the exact corrected system. -/
theorem corrected_nine_comparison : ∃ d : ℝ, 0 < d ∧ d ≤ 1/10 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d → ∀ x : Fin 9 → ℝ,
      (∀ i, x i ≤ publication i + matrixApply correctedNineMatrix x i) →
      ∀ i, x i ≤ actualNine δ i := by
  obtain ⟨d, hd, hcap, hs⟩ := corrected_nine_actual
  refine ⟨d, hd, hcap, ?_⟩
  intro δ hδ hr x hx
  exact FiniteFeedbackComparison.subsolution_le_supersolution 8 0 (by decide)
    correctedNineMatrix_nonneg correctedNineMatrix_terminal_pos publication_nonneg
    (fun i hi => publication_pos hi) (actualNine_nonneg hδ (hr.trans hcap)) hx (hs δ hδ hr)

end WuPaper.R2Xi
