import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints232
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_232 (j : Fin 16) (hj : 16*232+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*232+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*232+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3712) ≤ val WuPaper.ClassicalFourthData.Bq 3712
    have hp : val WuPaper.ClassicalFourthData.Bq 3712 = (224208741867608:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3712 = 224208741867608 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3712 = (366:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3712
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3713) ≤ val WuPaper.ClassicalFourthData.Bq 3713
    have hp : val WuPaper.ClassicalFourthData.Bq 3713 = (224233878880551:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3713 = 224233878880551 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3713 = (11713:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3713
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3714) ≤ val WuPaper.ClassicalFourthData.Bq 3714
    have hp : val WuPaper.ClassicalFourthData.Bq 3714 = (224259005861754:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3714 = 224259005861754 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3714 = (5857:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3714
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3715) ≤ val WuPaper.ClassicalFourthData.Bq 3715
    have hp : val WuPaper.ClassicalFourthData.Bq 3715 = (224284122815274:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3715 = 224284122815274 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3715 = (2343:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3715
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3716) ≤ val WuPaper.ClassicalFourthData.Bq 3716
    have hp : val WuPaper.ClassicalFourthData.Bq 3716 = (224309229745167:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3716 = 224309229745167 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3716 = (2929:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3716
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3717) ≤ val WuPaper.ClassicalFourthData.Bq 3717
    have hp : val WuPaper.ClassicalFourthData.Bq 3717 = (224334326655484:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3717 = 224334326655484 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3717 = (11717:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3717
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3718) ≤ val WuPaper.ClassicalFourthData.Bq 3718
    have hp : val WuPaper.ClassicalFourthData.Bq 3718 = (224359413550277:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3718 = 224359413550277 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3718 = (5859:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3718
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3719) ≤ val WuPaper.ClassicalFourthData.Bq 3719
    have hp : val WuPaper.ClassicalFourthData.Bq 3719 = (224384490433596:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3719 = 224384490433596 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3719 = (11719:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3719
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3720) ≤ val WuPaper.ClassicalFourthData.Bq 3720
    have hp : val WuPaper.ClassicalFourthData.Bq 3720 = (224409557309487:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3720 = 224409557309487 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3720 = (293:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3720
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3721) ≤ val WuPaper.ClassicalFourthData.Bq 3721
    have hp : val WuPaper.ClassicalFourthData.Bq 3721 = (224434614181995:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3721 = 224434614181995 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3721 = (11721:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3721
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3722) ≤ val WuPaper.ClassicalFourthData.Bq 3722
    have hp : val WuPaper.ClassicalFourthData.Bq 3722 = (224459661055163:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3722 = 224459661055163 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3722 = (5861:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3722
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3723) ≤ val WuPaper.ClassicalFourthData.Bq 3723
    have hp : val WuPaper.ClassicalFourthData.Bq 3723 = (224484697933033:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3723 = 224484697933033 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3723 = (11723:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3723
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3724) ≤ val WuPaper.ClassicalFourthData.Bq 3724
    have hp : val WuPaper.ClassicalFourthData.Bq 3724 = (224509724819645:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3724 = 224509724819645 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3724 = (2931:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3724
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3725) ≤ val WuPaper.ClassicalFourthData.Bq 3725
    have hp : val WuPaper.ClassicalFourthData.Bq 3725 = (224534741719035:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3725 = 224534741719035 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3725 = (469:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3725
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3726) ≤ val WuPaper.ClassicalFourthData.Bq 3726
    have hp : val WuPaper.ClassicalFourthData.Bq 3726 = (224559748635238:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3726 = 224559748635238 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3726 = (5863:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3726
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3727) ≤ val WuPaper.ClassicalFourthData.Bq 3727
    have hp : val WuPaper.ClassicalFourthData.Bq 3727 = (224584745572289:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3727 = 224584745572289 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3727 = (11727:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3727
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_232
