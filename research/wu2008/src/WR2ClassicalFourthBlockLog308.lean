import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints308
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_308 (j : Fin 16) (hj : 16*308+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*308+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*308+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4928) ≤ val WuPaper.ClassicalFourthData.Bq 4928
    have hp : val WuPaper.ClassicalFourthData.Bq 4928 = (248421424665553:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4928 = 248421424665553 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4928 = (404:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4928
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4929) ≤ val WuPaper.ClassicalFourthData.Bq 4929
    have hp : val WuPaper.ClassicalFourthData.Bq 4929 = (248436861447967:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4929 = 248436861447967 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4929 = (12929:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4929
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4930) ≤ val WuPaper.ClassicalFourthData.Bq 4930
    have hp : val WuPaper.ClassicalFourthData.Bq 4930 = (248452291962419:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4930 = 248452291962419 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4930 = (1293:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4930
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4931) ≤ val WuPaper.ClassicalFourthData.Bq 4931
    have hp : val WuPaper.ClassicalFourthData.Bq 4931 = (248467716211232:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4931 = 248467716211232 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4931 = (12931:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4931
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4932) ≤ val WuPaper.ClassicalFourthData.Bq 4932
    have hp : val WuPaper.ClassicalFourthData.Bq 4932 = (248483134196728:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4932 = 248483134196728 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4932 = (3233:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4932
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4933) ≤ val WuPaper.ClassicalFourthData.Bq 4933
    have hp : val WuPaper.ClassicalFourthData.Bq 4933 = (248498545921229:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4933 = 248498545921229 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4933 = (12933:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4933
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4934) ≤ val WuPaper.ClassicalFourthData.Bq 4934
    have hp : val WuPaper.ClassicalFourthData.Bq 4934 = (248513951387054:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4934 = 248513951387054 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4934 = (6467:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4934
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4935) ≤ val WuPaper.ClassicalFourthData.Bq 4935
    have hp : val WuPaper.ClassicalFourthData.Bq 4935 = (248529350596522:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4935 = 248529350596522 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4935 = (2587:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4935
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4936) ≤ val WuPaper.ClassicalFourthData.Bq 4936
    have hp : val WuPaper.ClassicalFourthData.Bq 4936 = (248544743551951:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4936 = 248544743551951 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4936 = (1617:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4936
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4937) ≤ val WuPaper.ClassicalFourthData.Bq 4937
    have hp : val WuPaper.ClassicalFourthData.Bq 4937 = (248560130255659:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4937 = 248560130255659 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4937 = (12937:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4937
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4938) ≤ val WuPaper.ClassicalFourthData.Bq 4938
    have hp : val WuPaper.ClassicalFourthData.Bq 4938 = (248575510709962:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4938 = 248575510709962 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4938 = (6469:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4938
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4939) ≤ val WuPaper.ClassicalFourthData.Bq 4939
    have hp : val WuPaper.ClassicalFourthData.Bq 4939 = (248590884917173:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4939 = 248590884917173 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4939 = (12939:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4939
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4940) ≤ val WuPaper.ClassicalFourthData.Bq 4940
    have hp : val WuPaper.ClassicalFourthData.Bq 4940 = (248606252879609:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4940 = 248606252879609 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4940 = (647:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4940
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4941) ≤ val WuPaper.ClassicalFourthData.Bq 4941
    have hp : val WuPaper.ClassicalFourthData.Bq 4941 = (248621614599580:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4941 = 248621614599580 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4941 = (12941:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4941
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4942) ≤ val WuPaper.ClassicalFourthData.Bq 4942
    have hp : val WuPaper.ClassicalFourthData.Bq 4942 = (248636970079400:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4942 = 248636970079400 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4942 = (6471:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4942
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4943) ≤ val WuPaper.ClassicalFourthData.Bq 4943
    have hp : val WuPaper.ClassicalFourthData.Bq 4943 = (248652319321380:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4943 = 248652319321380 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4943 = (12943:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4943
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_308
