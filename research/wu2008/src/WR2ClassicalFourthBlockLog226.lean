import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints226
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_226 (j : Fin 16) (hj : 16*226+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*226+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*226+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3616) ≤ val WuPaper.ClassicalFourthData.Bq 3616
    have hp : val WuPaper.ClassicalFourthData.Bq 3616 = (221748256325473:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3616 = 221748256325473 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3616 = (363:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3616
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3617) ≤ val WuPaper.ClassicalFourthData.Bq 3617
    have hp : val WuPaper.ClassicalFourthData.Bq 3617 = (221774375577434:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3617 = 221774375577434 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3617 = (11617:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3617
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3618) ≤ val WuPaper.ClassicalFourthData.Bq 3618
    have hp : val WuPaper.ClassicalFourthData.Bq 3618 = (221800484398872:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3618 = 221800484398872 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3618 = (5809:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3618
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3619) ≤ val WuPaper.ClassicalFourthData.Bq 3619
    have hp : val WuPaper.ClassicalFourthData.Bq 3619 = (221826582794039:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3619 = 221826582794039 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3619 = (11619:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3619
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3620) ≤ val WuPaper.ClassicalFourthData.Bq 3620
    have hp : val WuPaper.ClassicalFourthData.Bq 3620 = (221852670767183:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3620 = 221852670767183 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3620 = (581:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3620
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3621) ≤ val WuPaper.ClassicalFourthData.Bq 3621
    have hp : val WuPaper.ClassicalFourthData.Bq 3621 = (221878748322551:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3621 = 221878748322551 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3621 = (11621:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3621
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3622) ≤ val WuPaper.ClassicalFourthData.Bq 3622
    have hp : val WuPaper.ClassicalFourthData.Bq 3622 = (221904815464388:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3622 = 221904815464388 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3622 = (5811:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3622
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3623) ≤ val WuPaper.ClassicalFourthData.Bq 3623
    have hp : val WuPaper.ClassicalFourthData.Bq 3623 = (221930872196936:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3623 = 221930872196936 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3623 = (11623:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3623
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3624) ≤ val WuPaper.ClassicalFourthData.Bq 3624
    have hp : val WuPaper.ClassicalFourthData.Bq 3624 = (221956918524436:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3624 = 221956918524436 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3624 = (1453:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3624
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3625) ≤ val WuPaper.ClassicalFourthData.Bq 3625
    have hp : val WuPaper.ClassicalFourthData.Bq 3625 = (221982954451126:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3625 = 221982954451126 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3625 = (93:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3625
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3626) ≤ val WuPaper.ClassicalFourthData.Bq 3626
    have hp : val WuPaper.ClassicalFourthData.Bq 3626 = (222008979981243:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3626 = 222008979981243 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3626 = (5813:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3626
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3627) ≤ val WuPaper.ClassicalFourthData.Bq 3627
    have hp : val WuPaper.ClassicalFourthData.Bq 3627 = (222034995119020:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3627 = 222034995119020 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3627 = (11627:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3627
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3628) ≤ val WuPaper.ClassicalFourthData.Bq 3628
    have hp : val WuPaper.ClassicalFourthData.Bq 3628 = (222060999868691:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3628 = 222060999868691 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3628 = (2907:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3628
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3629) ≤ val WuPaper.ClassicalFourthData.Bq 3629
    have hp : val WuPaper.ClassicalFourthData.Bq 3629 = (222086994234484:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3629 = 222086994234484 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3629 = (11629:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3629
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3630) ≤ val WuPaper.ClassicalFourthData.Bq 3630
    have hp : val WuPaper.ClassicalFourthData.Bq 3630 = (222112978220628:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3630 = 222112978220628 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3630 = (1163:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3630
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3631) ≤ val WuPaper.ClassicalFourthData.Bq 3631
    have hp : val WuPaper.ClassicalFourthData.Bq 3631 = (222138951831350:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3631 = 222138951831350 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3631 = (11631:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3631
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_226
