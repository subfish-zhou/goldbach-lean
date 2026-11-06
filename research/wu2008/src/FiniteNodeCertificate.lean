import FiniteMargin
import StaircaseActualCount

namespace ActualNineFeedback
open Wu2008DoubleSieve NodeExtension

/-- The literal original row, not a copied table of heights. -/
noncomputable def originalRow (j : Fin 21) : ℝ × ℝ × ℝ :=
  Wu08Staircase.table.get ⟨j.val, by simpa only [Wu08Staircase.table, List.length_cons,
    List.length_nil] using j.isLt⟩

noncomputable def originalHeight (j : Fin 21) : ℝ := (originalRow j).2.2

/-- Exact coordinate binding, independent of the original height values. -/
theorem originalRow_node (j : Fin 21) : (originalRow j).2.1 = rNode (j.val + 1) := by
  revert j
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]
  norm_num [originalRow, Wu08Staircase.table, rNode]

/-- No replacement certificate: the conclusion is the old production predicate. -/
theorem originalNodeCertificate_of_coordinates {δ : ℝ}
    (h : ∀ j : Fin 21, originalHeight j ≤
      wuImprovementLimit false δ (rNode (j.val + 1))) : StaircaseActual.NodeCertificate δ := by
  intro r hr
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hr
  let j : Fin 21 := ⟨i.val, by simpa only [Wu08Staircase.table, List.length_cons,
    List.length_nil] using i.isLt⟩
  have he : originalRow j = r := hi
  have hj := h j
  rw [← originalRow_node j] at hj
  change (originalRow j).2.2 ≤ wuImprovementLimit false δ (originalRow j).2.1 at hj
  simpa only [he] using hj

/-- This finite output condition contains no delta and no actual H or h values.
No instance or iteration count satisfying it is asserted here. -/
def FiniteStrictOutput (n : ℕ) : Prop := ∀ j, originalHeight j < transferredLower n j

/-- A fixed symbolic successful output supplies the explicit common radius. -/
theorem originalNodeCertificate_with_radius (n : ℕ) (h : FiniteStrictOutput n) :
    ∃ μ : ℝ, 0 < μ ∧ (∀ j, originalHeight j + μ ≤ transferredLower n j) ∧
      0 < marginRadius (totalDebit n) μ ∧
      ∀ δ : ℝ, 0 < δ → δ < marginRadius (totalDebit n) μ →
        StaircaseActual.NodeCertificate δ := by
  obtain ⟨μ, hμ, hm, hr, hc⟩ := finite_strict_output_eventually n originalHeight h
  exact ⟨μ, hμ, hm, hr, fun δ hd hs =>
    originalNodeCertificate_of_coordinates (fun j => (hc δ hd hs j).le)⟩

theorem originalNodeCertificate_eventually (n : ℕ) (h : FiniteStrictOutput n) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ < d → StaircaseActual.NodeCertificate δ := by
  obtain ⟨μ, _, _, hr, hc⟩ := originalNodeCertificate_with_radius n h
  exact ⟨marginRadius (totalDebit n) μ, hr, hc⟩


end ActualNineFeedback
