import Wu04RemainingStrongPaid

namespace Wu04RemainingStrongFourRows
open Wu2008DoubleSieve ActualNineFeedback NodeExtension Wu08OriginalPsiRecovery
noncomputable section

/-- One common positive-delta radius; the original four publication targets are unchanged. -/
def firstRadius : ℝ := min (1/10)
  (Wu04CurvePaid.slack/(8*(|Wu04CurveCost.costCap|+Wu04CurvePaid.slack)))

theorem firstRadius_pos : 0<firstRadius := by
  apply lt_min (by norm_num)
  exact div_pos Wu04CurvePaid.slack_pos
    (mul_pos (by norm_num) (add_pos_of_nonneg_of_pos (abs_nonneg _) Wu04CurvePaid.slack_pos))

theorem first_small {δ : ℝ} (hd : 0<δ) (hr : δ≤firstRadius) :
    Wu04CurvePaid.publication+coupledFeedback SecondFunctionalParameters.row1 (actualNine δ) ≤
      wuImprovementLimit true δ SecondFunctionalParameters.row1.s := by
  have hh : δ≤1/10 := hr.trans (min_le_left _ _)
  have hs := Wu04CurvePaid.slack_pos
  have hp : 0<8*(|Wu04CurveCost.costCap|+Wu04CurvePaid.slack) :=
    mul_pos (by norm_num) (add_pos_of_nonneg_of_pos (abs_nonneg _) hs)
  have hsmall := (le_div_iff₀ hp).mp (hr.trans (min_le_right _ _))
  have hc := mul_le_mul_of_nonneg_left (le_abs_self Wu04CurveCost.costCap) hd.le
  have hdebit : Wu04CurvePaid.deltaDebit δ≤Wu04CurvePaid.slack/5 := by
    unfold Wu04CurvePaid.deltaDebit
    apply (div_le_iff₀ (show 0<5*(1-2*δ) by linarith only [hh])).mpr
    nlinarith only [hsmall,hc,mul_nonneg hd.le hs.le,
      mul_nonneg hd.le (abs_nonneg Wu04CurveCost.costCap)]
  linarith only [Wu04CurvePaid.actual_with_slack hd hh,hdebit]

def commonRadius : ℝ := min firstRadius
  (min (Wu04RemainingStrongPaid.deltaRadius 0)
    (min (Wu04RemainingStrongPaid.deltaRadius 1) (Wu04RemainingStrongPaid.deltaRadius 2)))

theorem commonRadius_pos : 0<commonRadius :=
  lt_min firstRadius_pos (lt_min (Wu04RemainingStrongPaid.deltaRadius_pos 0)
    (lt_min (Wu04RemainingStrongPaid.deltaRadius_pos 1) (Wu04RemainingStrongPaid.deltaRadius_pos 2)))

theorem commonRadius_le (i : Fin 3) : commonRadius≤Wu04RemainingStrongPaid.deltaRadius i := by
  have h := min_le_right firstRadius
    (min (Wu04RemainingStrongPaid.deltaRadius 0)
      (min (Wu04RemainingStrongPaid.deltaRadius 1) (Wu04RemainingStrongPaid.deltaRadius 2)))
  change commonRadius≤_ at h
  have h0 := h.trans (min_le_left _ _)
  have h12 := h.trans (min_le_right _ _)
  have h1 := h12.trans (min_le_left _ _)
  have h2 := h12.trans (min_le_right _ _)
  have hall : ∀ i : Fin 3,commonRadius≤Wu04RemainingStrongPaid.deltaRadius i := by
    simp only [Fin.forall_fin_succ,Fin.forall_fin_zero,and_true]
    exact ⟨h0,h1,h2⟩
  exact hall i

/-- All four original Psi2 rows use one and the same actual positive delta. -/
theorem four_actual_same_delta : ∃ d : ℝ,0<d ∧ d≤1/10 ∧
    ∀ δ : ℝ,0<δ → δ≤d →
      (Wu04CurvePaid.publication+coupledFeedback SecondFunctionalParameters.row1 (actualNine δ)≤
        wuImprovementLimit true δ SecondFunctionalParameters.row1.s) ∧
      (∀ i : Fin 3,Wu04RemainingCore.publication i+
        coupledFeedback (Wu04RemainingCore.row i) (actualNine δ)≤
          wuImprovementLimit true δ (Wu04RemainingCore.row i).s) := by
  have hf : commonRadius≤firstRadius := min_le_left _ _
  refine ⟨commonRadius,commonRadius_pos,hf.trans (min_le_left _ _),?_⟩
  intro δ hd hr
  exact ⟨first_small hd (hr.trans hf),fun i =>
    Wu04RemainingStrongPaid.actual_small_delta i hd (hr.trans (commonRadius_le i))⟩

end
end Wu04RemainingStrongFourRows
