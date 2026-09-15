import Wu04SourceKernel

noncomputable section
namespace Wu04Source
open Real Set MeasureTheory NodeExtension FirstFeedbackIntegrals ActualNineFeedback
open scoped Interval BigOperators

/-- Wu 2004 §7: s0=1, sn=2+0.1(n+1) for n>0. -/
def paperNode (n : ℕ) : ℝ := if n=0 then 1 else 2+((n:ℝ)+1)/10

def a9 (k : Fin 9) : ℝ := ∫ t in paperNode k.val..paperNode (k.val+1), xi1 t 3 3

def terminalRow (z : Fin 9 → ℝ) : ℝ := ∑ k : Fin 9, z k*a9 k

theorem node_left (k : Fin 9) : paperNode k.val = upperLeft k := by
  unfold paperNode upperLeft
  split_ifs <;> ring

theorem node_right (k : Fin 9) : paperNode (k.val+1) = upperNode k := by
  simp [paperNode,upperNode]
  ring

/-- Exact equality for every vector, not only for the printed numerical targets. -/
theorem project_eq_paper_row (z : Fin 9 → ℝ) : firstFeedback z 3 3 = terminalRow z := by
  rw [firstFeedback_eq_kernel,profile_integral_cells z le_rfl
    (by norm_num [upperNode]) terminalKernel_continuous]
  unfold terminalRow a9
  apply Finset.sum_congr rfl
  intro k _
  rw [node_left,node_right]
  have he : cellLeft 1 k = upperLeft k := by
    unfold cellLeft upperLeft
    split_ifs <;> rfl
  rw [he]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  obtain ⟨ha,hab,hb⟩ := SigmaEndpointPayment.original_cell_bounds k
  rw [uIcc_of_le hab] at ht
  exact (xi1_terminal ⟨ha.trans ht.1,ht.2.trans hb⟩).symm

theorem row_basis (k : Fin 9) : terminalRow (nodeBasis k) = a9 k := by
  classical
  simp [terminalRow,nodeBasis,ite_mul]

/-- Each of the nine entries in the last implemented row is the source integral. -/
theorem coefficient_eq_project (k : Fin 9) : feedbackMatrix 8 k = a9 k := by
  have he : feedbackMatrix 8 k = firstFeedback (nodeBasis k) 3 3 := by
    change firstFeedback (nodeBasis k) (firstNode 4) (firstS 4) = _
    rw [show firstNode (4:Fin 5) = 3 by norm_num [firstNode],show firstS (4:Fin 5) = 3 from rfl]
  rw [he,project_eq_paper_row,row_basis]

theorem printed_row_upper : terminalRow NineFeedbackStrength.originalH ≤ (728/100000:ℝ) := by
  rw [← project_eq_paper_row]
  exact Hf4Actual.true_feedback_cap

theorem printed_row_deficit : (143/10000000:ℝ) ≤
    NineFeedbackStrength.originalH 8-terminalRow NineFeedbackStrength.originalH := by
  rw [← project_eq_paper_row]
  exact Hf4Actual.true_feedback_deficit

end Wu04Source
