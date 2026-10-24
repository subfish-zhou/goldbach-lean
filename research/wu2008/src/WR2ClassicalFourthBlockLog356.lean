import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints356
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_356 (j : Fin 16) (hj : 16*356+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*356+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*356+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5696) ≤ val WuPaper.ClassicalFourthData.Bq 5696
    have hp : val WuPaper.ClassicalFourthData.Bq 5696 = (258592017583842:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5696 = 258592017583842 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5696 = (428:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5696
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5697) ≤ val WuPaper.ClassicalFourthData.Bq 5697
    have hp : val WuPaper.ClassicalFourthData.Bq 5697 = (258603255662562:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5697 = 258603255662562 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5697 = (13697:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5697
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5698) ≤ val WuPaper.ClassicalFourthData.Bq 5698
    have hp : val WuPaper.ClassicalFourthData.Bq 5698 = (258614488994971:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5698 = 258614488994971 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5698 = (6849:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5698
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5699) ≤ val WuPaper.ClassicalFourthData.Bq 5699
    have hp : val WuPaper.ClassicalFourthData.Bq 5699 = (258625717582750:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5699 = 258625717582750 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5699 = (13699:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5699
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5700) ≤ val WuPaper.ClassicalFourthData.Bq 5700
    have hp : val WuPaper.ClassicalFourthData.Bq 5700 = (258636941427578:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5700 = 258636941427578 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5700 = (137:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5700
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5701) ≤ val WuPaper.ClassicalFourthData.Bq 5701
    have hp : val WuPaper.ClassicalFourthData.Bq 5701 = (258648160531133:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5701 = 258648160531133 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5701 = (13701:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5701
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5702) ≤ val WuPaper.ClassicalFourthData.Bq 5702
    have hp : val WuPaper.ClassicalFourthData.Bq 5702 = (258659374895093:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5702 = 258659374895093 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5702 = (6851:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5702
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5703) ≤ val WuPaper.ClassicalFourthData.Bq 5703
    have hp : val WuPaper.ClassicalFourthData.Bq 5703 = (258670584521135:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5703 = 258670584521135 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5703 = (13703:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5703
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5704) ≤ val WuPaper.ClassicalFourthData.Bq 5704
    have hp : val WuPaper.ClassicalFourthData.Bq 5704 = (258681789410936:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5704 = 258681789410936 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5704 = (1713:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5704
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5705) ≤ val WuPaper.ClassicalFourthData.Bq 5705
    have hp : val WuPaper.ClassicalFourthData.Bq 5705 = (258692989566170:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5705 = 258692989566170 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5705 = (2741:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5705
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5706) ≤ val WuPaper.ClassicalFourthData.Bq 5706
    have hp : val WuPaper.ClassicalFourthData.Bq 5706 = (258704184988514:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5706 = 258704184988514 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5706 = (6853:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5706
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5707) ≤ val WuPaper.ClassicalFourthData.Bq 5707
    have hp : val WuPaper.ClassicalFourthData.Bq 5707 = (258715375679640:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5707 = 258715375679640 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5707 = (13707:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5707
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5708) ≤ val WuPaper.ClassicalFourthData.Bq 5708
    have hp : val WuPaper.ClassicalFourthData.Bq 5708 = (258726561641223:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5708 = 258726561641223 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5708 = (3427:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5708
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5709) ≤ val WuPaper.ClassicalFourthData.Bq 5709
    have hp : val WuPaper.ClassicalFourthData.Bq 5709 = (258737742874936:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5709 = 258737742874936 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5709 = (13709:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5709
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5710) ≤ val WuPaper.ClassicalFourthData.Bq 5710
    have hp : val WuPaper.ClassicalFourthData.Bq 5710 = (258748919382451:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5710 = 258748919382451 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5710 = (1371:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5710
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5711) ≤ val WuPaper.ClassicalFourthData.Bq 5711
    have hp : val WuPaper.ClassicalFourthData.Bq 5711 = (258760091165439:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5711 = 258760091165439 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5711 = (13711:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5711
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_356
