import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints404
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_404 (j : Fin 16) (hj : 16*404+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*404+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*404+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6464) ≤ val WuPaper.ClassicalFourthData.Bq 6464
    have hp : val WuPaper.ClassicalFourthData.Bq 6464 = (265942044688887:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6464 = 265942044688887 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6464 = (452:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6464
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6465) ≤ val WuPaper.ClassicalFourthData.Bq 6465
    have hp : val WuPaper.ClassicalFourthData.Bq 6465 = (265950084971486:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6465 = 265950084971486 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6465 = (2893:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6465
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6466) ≤ val WuPaper.ClassicalFourthData.Bq 6466
    have hp : val WuPaper.ClassicalFourthData.Bq 6466 = (265958121617639:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6466 = 265958121617639 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6466 = (7233:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6466
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6467) ≤ val WuPaper.ClassicalFourthData.Bq 6467
    have hp : val WuPaper.ClassicalFourthData.Bq 6467 = (265966154628581:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6467 = 265966154628581 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6467 = (14467:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6467
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6468) ≤ val WuPaper.ClassicalFourthData.Bq 6468
    have hp : val WuPaper.ClassicalFourthData.Bq 6468 = (265974184005550:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6468 = 265974184005550 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6468 = (3617:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6468
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6469) ≤ val WuPaper.ClassicalFourthData.Bq 6469
    have hp : val WuPaper.ClassicalFourthData.Bq 6469 = (265982209749780:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6469 = 265982209749780 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6469 = (14469:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6469
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6470) ≤ val WuPaper.ClassicalFourthData.Bq 6470
    have hp : val WuPaper.ClassicalFourthData.Bq 6470 = (265990231862507:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6470 = 265990231862507 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6470 = (1447:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6470
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6471) ≤ val WuPaper.ClassicalFourthData.Bq 6471
    have hp : val WuPaper.ClassicalFourthData.Bq 6471 = (265998250344966:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6471 = 265998250344966 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6471 = (14471:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6471
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6472) ≤ val WuPaper.ClassicalFourthData.Bq 6472
    have hp : val WuPaper.ClassicalFourthData.Bq 6472 = (266006265198390:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6472 = 266006265198390 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6472 = (1809:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6472
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6473) ≤ val WuPaper.ClassicalFourthData.Bq 6473
    have hp : val WuPaper.ClassicalFourthData.Bq 6473 = (266014276424013:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6473 = 266014276424013 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6473 = (14473:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6473
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6474) ≤ val WuPaper.ClassicalFourthData.Bq 6474
    have hp : val WuPaper.ClassicalFourthData.Bq 6474 = (266022284023068:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6474 = 266022284023068 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6474 = (7237:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6474
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6475) ≤ val WuPaper.ClassicalFourthData.Bq 6475
    have hp : val WuPaper.ClassicalFourthData.Bq 6475 = (266030287996788:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6475 = 266030287996788 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6475 = (579:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6475
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6476) ≤ val WuPaper.ClassicalFourthData.Bq 6476
    have hp : val WuPaper.ClassicalFourthData.Bq 6476 = (266038288346405:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6476 = 266038288346405 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6476 = (3619:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6476
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6477) ≤ val WuPaper.ClassicalFourthData.Bq 6477
    have hp : val WuPaper.ClassicalFourthData.Bq 6477 = (266046285073152:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6477 = 266046285073152 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6477 = (14477:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6477
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6478) ≤ val WuPaper.ClassicalFourthData.Bq 6478
    have hp : val WuPaper.ClassicalFourthData.Bq 6478 = (266054278178258:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6478 = 266054278178258 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6478 = (7239:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6478
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6479) ≤ val WuPaper.ClassicalFourthData.Bq 6479
    have hp : val WuPaper.ClassicalFourthData.Bq 6479 = (266062267662955:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6479 = 266062267662955 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6479 = (14479:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6479
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_404
