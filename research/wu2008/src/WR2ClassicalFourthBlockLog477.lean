import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints477
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_477 (j : Fin 16) (hj : 16*477+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*477+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*477+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7632) ≤ val WuPaper.ClassicalFourthData.Bq 7632
    have hp : val WuPaper.ClassicalFourthData.Bq 7632 = (273148812608092:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7632 = 273148812608092 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7632 = (977:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7632
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7633) ≤ val WuPaper.ClassicalFourthData.Bq 7633
    have hp : val WuPaper.ClassicalFourthData.Bq 7633 = (273153336075198:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7633 = 273153336075198 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7633 = (15633:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7633
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7634) ≤ val WuPaper.ClassicalFourthData.Bq 7634
    have hp : val WuPaper.ClassicalFourthData.Bq 7634 = (273157857073003:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7634 = 273157857073003 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7634 = (7817:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7634
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7635) ≤ val WuPaper.ClassicalFourthData.Bq 7635
    have hp : val WuPaper.ClassicalFourthData.Bq 7635 = (273162375602308:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7635 = 273162375602308 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7635 = (3127:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7635
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7636) ≤ val WuPaper.ClassicalFourthData.Bq 7636
    have hp : val WuPaper.ClassicalFourthData.Bq 7636 = (273166891663910:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7636 = 273166891663910 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7636 = (3909:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7636
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7637) ≤ val WuPaper.ClassicalFourthData.Bq 7637
    have hp : val WuPaper.ClassicalFourthData.Bq 7637 = (273171405258608:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7637 = 273171405258608 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7637 = (15637:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7637
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7638) ≤ val WuPaper.ClassicalFourthData.Bq 7638
    have hp : val WuPaper.ClassicalFourthData.Bq 7638 = (273175916387198:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7638 = 273175916387198 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7638 = (7819:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7638
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7639) ≤ val WuPaper.ClassicalFourthData.Bq 7639
    have hp : val WuPaper.ClassicalFourthData.Bq 7639 = (273180425050481:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7639 = 273180425050481 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7639 = (15639:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7639
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7640) ≤ val WuPaper.ClassicalFourthData.Bq 7640
    have hp : val WuPaper.ClassicalFourthData.Bq 7640 = (273184931249251:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7640 = 273184931249251 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7640 = (391:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7640
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7641) ≤ val WuPaper.ClassicalFourthData.Bq 7641
    have hp : val WuPaper.ClassicalFourthData.Bq 7641 = (273189434984307:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7641 = 273189434984307 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7641 = (15641:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7641
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7642) ≤ val WuPaper.ClassicalFourthData.Bq 7642
    have hp : val WuPaper.ClassicalFourthData.Bq 7642 = (273193936256445:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7642 = 273193936256445 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7642 = (7821:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7642
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7643) ≤ val WuPaper.ClassicalFourthData.Bq 7643
    have hp : val WuPaper.ClassicalFourthData.Bq 7643 = (273198435066462:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7643 = 273198435066462 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7643 = (15643:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7643
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7644) ≤ val WuPaper.ClassicalFourthData.Bq 7644
    have hp : val WuPaper.ClassicalFourthData.Bq 7644 = (273202931415154:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7644 = 273202931415154 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7644 = (3911:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7644
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7645) ≤ val WuPaper.ClassicalFourthData.Bq 7645
    have hp : val WuPaper.ClassicalFourthData.Bq 7645 = (273207425303317:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7645 = 273207425303317 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7645 = (3129:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7645
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7646) ≤ val WuPaper.ClassicalFourthData.Bq 7646
    have hp : val WuPaper.ClassicalFourthData.Bq 7646 = (273211916731746:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7646 = 273211916731746 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7646 = (7823:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7646
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7647) ≤ val WuPaper.ClassicalFourthData.Bq 7647
    have hp : val WuPaper.ClassicalFourthData.Bq 7647 = (273216405701237:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7647 = 273216405701237 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7647 = (15647:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7647
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_477
