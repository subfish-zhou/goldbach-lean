import R2XiOriginalFeedback
import Wu04FirstPaid

noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory Wu2008DoubleSieve ActualNineFeedback
open scoped Interval

theorem Xi1_four_paid {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    (hr : δ ≤ Wu04FirstPaid.commonRadius) (i : Fin 4) :
    Wu04FirstCore.publication i.castSucc +
      (∫ t in (1 : ℝ)..3, wuImprovementLimit true δ t *
        Xi1 (firstNode i.castSucc) (firstS i.castSucc) t) ≤
      wuImprovementLimit true δ (firstNode i.castSucc) := by
  rcases WuPaper.RMapMMatrix.original_five_rows_qualified i.castSucc with
    ⟨hs, hs3, hS, hS5, hrgeom⟩
  have hactual := proposition3_actual hd hdhi hs hs3 hS hS5 hrgeom
  have hbase := Wu04FirstPaid.publication_with_slack i
  have hcost := Wu04FirstCertificate.cost_paid i.castSucc
  have hdelta : 0 ≤ 2 * δ / (1 - 2 * δ) :=
    div_nonneg (by positivity) (by linarith)
  have hpaid := Wu04FirstPaid.debit_le_slack i hd (hr.trans (Wu04FirstPaid.commonRadius_le i))
  have hcomp := mul_le_mul_of_nonneg_left hcost hdelta
  change 2 * δ / (1 - 2 * δ) * Wu04FirstCertificate.costCap i.castSucc ≤
    Wu04FirstPublication.slack i at hpaid
  linarith

theorem Xi1_five_paid {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    (hr : δ ≤ Wu04FirstPaid.commonRadius) (i : Fin 5) :
    Wu04FirstCore.publication i +
      (∫ t in (1 : ℝ)..3, wuImprovementLimit true δ t * Xi1 (firstNode i) (firstS i) t) ≤
      wuImprovementLimit true δ (firstNode i) := by
  refine Fin.lastCases ?_ (fun j => Xi1_four_paid hd hdhi hr j) i
  have h := proposition3_five_original_rows hd hdhi (Fin.last 4)
  have ht : firstNode (Fin.last 4) = 3 ∧ firstS (Fin.last 4) = 3 ∧
      Wu04FirstCore.publication (Fin.last 4) = 0 := by
    refine ⟨?_, rfl, rfl⟩
    norm_num [firstNode, Fin.last]
  rw [ht.1, ht.2.1, firstFunctionalGainPsi_self, zero_add] at h
  simpa only [ht.1, ht.2.1, ht.2.2, zero_add] using h

theorem Xi1_five_paid_common :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 10 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d → ∀ i : Fin 5,
        Wu04FirstCore.publication i +
          (∫ t in (1 : ℝ)..3, wuImprovementLimit true δ t * Xi1 (firstNode i) (firstS i) t) ≤
        wuImprovementLimit true δ (firstNode i) := by
  refine ⟨min (1 / 10) Wu04FirstPaid.commonRadius,
    lt_min (by norm_num) Wu04FirstPaid.commonRadius_pos, min_le_left _ _, ?_⟩
  intro δ hd hδ i
  exact Xi1_five_paid hd (hδ.trans (min_le_left _ _)) (hδ.trans (min_le_right _ _)) i

end WuPaper.R2Xi

#check @Wu04FirstPaid.publication_with_slack
#print axioms Wu04FirstPaid.publication_with_slack
#check @Wu04FirstCertificate.cost_paid
#print axioms Wu04FirstCertificate.cost_paid
#check @Wu04FirstPaid.debit_le_slack
#print axioms Wu04FirstPaid.debit_le_slack

run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.getPrefix == `WuPaper.R2Xi then
      Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))
      Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent name)))
