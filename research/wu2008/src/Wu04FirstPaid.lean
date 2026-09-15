import Wu04FirstPublication

namespace Wu04FirstPaid
open Wu2008DoubleSieve ActualNineFeedback NodeExtension Real
open Wu04FirstCore Wu04FirstPublication
noncomputable section

theorem slack_pos (i : Fin 4) : 0<slack i := by
  have h : ∀ i : Fin 4,0<slack i := by
    simp only [Fin.forall_fin_succ,Fin.forall_fin_zero,and_true]
    exact ⟨slack_zero,slack_one,slack_two,slack_three⟩
  exact h i

theorem publication_with_slack (i : Fin 4) : publication i.castSucc+slack i≤
    firstFunctionalGainPsiOne (firstNode i.castSucc) (firstS i.castSucc) := by
  unfold slack
  linarith only [Wu04FirstCertificate.base_paid i]

def radius (i : Fin 4) : ℝ := min (1/10)
  (slack i/(8*(|Wu04FirstCertificate.costCap i.castSucc|+slack i)))

theorem radius_pos (i : Fin 4) : 0<radius i := by
  apply lt_min (by norm_num)
  exact div_pos (slack_pos i)
    (mul_pos (by norm_num) (add_pos_of_nonneg_of_pos (abs_nonneg _) (slack_pos i)))

theorem actual_with_slack (i : Fin 4) {δ : ℝ} (hd : 0<δ) (hh : δ≤1/10) :
    publication i.castSucc+slack i-deltaLoss δ*Wu04FirstCertificate.costCap i.castSucc+
      firstFeedback (actualNine δ) (firstNode i.castSucc) (firstS i.castSucc)≤
      wuImprovementLimit true δ (firstNode i.castSucc) := by
  have h := Wu04FirstCertificate.actual i hd hh
  unfold slack
  linarith only [h]

theorem debit_le_slack (i : Fin 4) {δ : ℝ} (hd : 0<δ) (hr : δ≤radius i) :
    deltaLoss δ*Wu04FirstCertificate.costCap i.castSucc≤slack i := by
  have hh : δ≤1/10 := hr.trans (min_le_left _ _)
  have hs := slack_pos i
  have hp : 0<8*(|Wu04FirstCertificate.costCap i.castSucc|+slack i) :=
    mul_pos (by norm_num) (add_pos_of_nonneg_of_pos (abs_nonneg _) hs)
  have hm := (le_div_iff₀ hp).mp (hr.trans (min_le_right _ _))
  have hc := mul_le_mul_of_nonneg_left (le_abs_self (Wu04FirstCertificate.costCap i.castSucc)) hd.le
  rw [deltaLoss,div_mul_eq_mul_div]
  apply (div_le_iff₀ (show 0<1-2*δ by linarith only [hh])).mpr
  nlinarith only [hm,hc,mul_nonneg hd.le hs.le,
    mul_nonneg hd.le (abs_nonneg (Wu04FirstCertificate.costCap i.castSucc))]

theorem actual_small (i : Fin 4) {δ : ℝ} (hd : 0<δ) (hr : δ≤radius i) :
    publication i.castSucc+firstFeedback (actualNine δ) (firstNode i.castSucc) (firstS i.castSucc)≤
      wuImprovementLimit true δ (firstNode i.castSucc) := by
  have hh : δ≤1/10 := hr.trans (min_le_left _ _)
  linarith only [actual_with_slack i hd hh,debit_le_slack i hd hr]

def commonRadius : ℝ := min (radius 0) (min (radius 1) (min (radius 2) (radius 3)))

theorem commonRadius_pos : 0<commonRadius :=
  lt_min (radius_pos 0) (lt_min (radius_pos 1) (lt_min (radius_pos 2) (radius_pos 3)))

theorem commonRadius_le (i : Fin 4) : commonRadius≤radius i := by
  have h0 : commonRadius≤radius 0 := min_le_left _ _
  have h123 : commonRadius≤min (radius 1) (min (radius 2) (radius 3)) := min_le_right _ _
  have h1 := h123.trans (min_le_left _ _)
  have h23 := h123.trans (min_le_right _ _)
  have h2 := h23.trans (min_le_left _ _)
  have h3 := h23.trans (min_le_right _ _)
  have hall : ∀ i : Fin 4,commonRadius≤radius i := by
    simp only [Fin.forall_fin_succ,Fin.forall_fin_zero,and_true]
    exact ⟨h0,h1,h2,h3⟩
  exact hall i

/-- All five original first rows, including the exact zero-cost terminal feedback. -/
theorem five_actual {δ : ℝ} (hd : 0<δ) (hh : δ≤1/10) (hr : δ≤commonRadius) (i : Fin 5) :
    publication i+firstFeedback (actualNine δ) (firstNode i) (firstS i)≤
      wuImprovementLimit true δ (firstNode i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact terminal_actual hd hh
  · exact actual_small j hd (hr.trans (commonRadius_le j))

/-- A common actual delta for the original four Psi2 and five Psi1 rows. -/
theorem nine_actual_same_delta : ∃ d : ℝ,0<d ∧ d≤1/10 ∧
    ∀ δ : ℝ,0<δ → δ≤d →
      (Wu04CurvePaid.publication+coupledFeedback SecondFunctionalParameters.row1 (actualNine δ)≤
        wuImprovementLimit true δ SecondFunctionalParameters.row1.s) ∧
      (∀ i : Fin 3,Wu04RemainingCore.publication i+
        coupledFeedback (Wu04RemainingCore.row i) (actualNine δ)≤
          wuImprovementLimit true δ (Wu04RemainingCore.row i).s) ∧
      (∀ i : Fin 5,publication i+firstFeedback (actualNine δ) (firstNode i) (firstS i)≤
        wuImprovementLimit true δ (firstNode i)) := by
  obtain ⟨d,hd,hdcap,hfour⟩ := Wu04RemainingStrongFourRows.four_actual_same_delta
  refine ⟨min d commonRadius,lt_min hd commonRadius_pos,(min_le_left _ _).trans hdcap,?_⟩
  intro δ hδ hr
  have hδd := hr.trans (min_le_left d commonRadius)
  have h4 := hfour δ hδ hδd
  exact ⟨h4.1,h4.2,fun i => five_actual hδ (hδd.trans hdcap) (hr.trans (min_le_right _ _)) i⟩

end
end Wu04FirstPaid
