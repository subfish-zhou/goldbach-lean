import Wu04FirstPaid
import FeedbackFixedPoint

namespace NineFeedbackStrength
open Wu2008DoubleSieve ActualNineFeedback NodeExtension
open scoped BigOperators
noncomputable section

/-- Reindexing only the already paid original publication bases. No new numerical data. -/
def publication (i : Fin 9) : ℝ :=
  Fin.addCases (m := 4) (n := 5) (motive := fun _ => ℝ)
    (fun j => Fin.cases (motive := fun _ => ℝ) Wu04CurvePaid.publication Wu04RemainingCore.publication j)
    Wu04FirstCore.publication i

theorem publication_coupled_zero : publication (0 : Fin 9) = Wu04CurvePaid.publication := rfl

theorem publication_coupled_succ (i : Fin 3) :
    publication (i.succ.castAdd 5) = Wu04RemainingCore.publication i := by
  simp [publication]

theorem publication_first (i : Fin 5) :
    publication (Fin.natAdd 4 i) = Wu04FirstCore.publication i := by
  simp [publication]

theorem coupled_feedback_index (z : Fin 9 → ℝ) (i : Fin 4) :
    feedback z (i.castAdd 5) = coupledFeedback (coupledRow i) z := by
  simp [feedback, i.isLt]

theorem first_feedback_index (z : Fin 9 → ℝ) (i : Fin 5) :
    feedback z (Fin.natAdd 4 i) = firstFeedback z (firstNode i) (firstS i) := by
  simp [feedback, show ¬ 4+i.val<4 by omega]

theorem first_node_index (i : Fin 5) : firstNode i = upperNode (Fin.natAdd 4 i) := by
  simp only [firstNode, upperNode, Fin.val_natAdd, Nat.cast_add]
  norm_num
  ring

theorem coupled_base_index (i : Fin 4) : base (i.castAdd 5) = coupledBase (coupledRow i) := by
  simp [base, i.isLt]

theorem first_base_index (i : Fin 5) : base (Fin.natAdd 4 i) =
    firstFunctionalGainPsiOne (firstNode i) (firstS i) := by
  by_cases h : i.val=4
  · have hi : i=(4 : Fin 5) := Fin.ext h
    subst i
    rw [Wu04FirstCore.terminal_psi]
    change (0 : ℝ) = 0
    rfl
  · simp [base, show ¬ 4+i.val<4 by omega, show ¬4+i.val=8 by omega]

/-- The original nine paid inequalities now use the literal nine-dimensional feedback operator. -/
theorem actual_same_delta : ∃ d : ℝ, 0<d ∧ d≤1/10 ∧
    ∀ δ : ℝ, 0<δ → δ≤d → ∀ i : Fin 9,
      publication i + matrixApply feedbackMatrix (actualNine δ) i ≤ actualNine δ i := by
  obtain ⟨d,hd,hcap,hrows⟩ := Wu04FirstPaid.nine_actual_same_delta
  refine ⟨d,hd,hcap,?_⟩
  intro δ hδ hr i
  have h := hrows δ hδ hr
  change publication i + (∑ k, feedbackMatrix i k * actualNine δ k) ≤ actualNine δ i
  rw [← feedback_expansion]
  refine Fin.addCases (m := 4) (n := 5) (fun j => ?_) (fun j => ?_) i
  · rw [coupled_feedback_index]
    change publication (j.castAdd 5) + coupledFeedback (coupledRow j) (actualNine δ) ≤
      wuImprovementLimit true δ (upperNode (j.castAdd 5))
    have hn : (coupledRow j).s = upperNode (j.castAdd 5) := by
      simpa only [upperNode, Fin.val_castAdd] using coupledRow_node j
    rw [← hn]
    refine Fin.cases ?_ (fun k => ?_) j
    · exact h.1
    · rw [publication_coupled_succ]
      exact h.2.1 k
  · rw [publication_first,first_feedback_index]
    change _ ≤ wuImprovementLimit true δ (upperNode (Fin.natAdd 4 j))
    rw [← first_node_index]
    exact h.2.2 j

/-- Paid original bases lie below the genuine, possibly previously signed, base. -/
theorem publication_le_base (i : Fin 9) : publication i ≤ base i := by
  refine Fin.addCases (m := 4) (n := 5) (fun j => ?_) (fun j => ?_) i
  · rw [coupled_base_index,Wu08OriginalPsiRecovery.coupledBase_eq_original_logs (coupledRow_geometry j)]
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<5)).mpr
    refine Fin.cases ?_ (fun k => ?_) j
    · have h := Wu04CurvePaid.publication_budget
      change 5*Wu04CurvePaid.publication ≤
        Wu08OriginalPsiRecovery.classicalNumerator (coupledRow 0)-2*coupledCostMass (coupledRow 0) at h
      change Wu04CurvePaid.publication*5≤_
      linarith only [h]
    · rw [publication_coupled_succ]
      have h := Wu04RemainingStrongPaid.publication_budget k
      change 5*Wu04RemainingCore.publication k ≤
        Wu08OriginalPsiRecovery.classicalNumerator (coupledRow k.succ)-2*coupledCostMass (coupledRow k.succ) at h
      linarith only [h]
  · rw [publication_first,first_base_index]
    refine Fin.lastCases ?_ (fun k => ?_) j
    · exact (Wu04FirstCore.terminal_psi).ge
    · linarith only [Wu04FirstPaid.publication_with_slack k,Wu04FirstPaid.slack_pos k]

theorem publication_nonneg (i : Fin 9) : 0 ≤ publication i := by
  refine Fin.addCases (m := 4) (n := 5) (fun j => ?_) (fun j => ?_) i
  · refine Fin.cases ?_ (fun k => ?_) j
    · norm_num [publication,Wu04CurvePaid.publication]
    · rw [publication_coupled_succ]
      unfold Wu04RemainingCore.publication
      split_ifs <;> norm_num
  · rw [publication_first]
    have h : ∀ j : Fin 5, 0 ≤ Wu04FirstCore.publication j := by
      simp only [Wu04FirstCore.publication, Fin.forall_fin_succ, Fin.forall_fin_zero,
        and_true, Matrix.cons_val_zero, Matrix.cons_val_succ]
      norm_num
    exact h j

theorem base_nonneg (i : Fin 9) : 0 ≤ base i :=
  (publication_nonneg i).trans (publication_le_base i)

/-- Clipping is genuinely removable only after the paid original base is proved nonnegative. -/
theorem Ainf_affine (i : Fin 9) : FeedbackLimit.Ainf i =
    base i + matrixApply feedbackMatrix FeedbackLimit.Ainf i := by
  rw [FeedbackLimit.Ainf_fixed]
  exact max_eq_right (add_nonneg (base_nonneg i)
    (matrixApply_nonneg feedbackMatrix_nonneg FeedbackLimit.Ainf_nonneg i))

theorem publication_le_Ainf (i : Fin 9) : publication i ≤ FeedbackLimit.Ainf i := by
  rw [Ainf_affine]
  exact (publication_le_base i).trans (le_add_of_nonneg_right
    (matrixApply_nonneg feedbackMatrix_nonneg FeedbackLimit.Ainf_nonneg i))

end
end NineFeedbackStrength
