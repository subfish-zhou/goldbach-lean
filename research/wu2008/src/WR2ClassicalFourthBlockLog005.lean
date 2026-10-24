import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints005
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_005 (j : Fin 16) (hj : 16*5+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*5+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*5+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 80) ≤ val WuPaper.ClassicalFourthData.Bq 80
    have hp : val WuPaper.ClassicalFourthData.Bq 80 = (9803280839693:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 80 = 9803280839693 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 80 = (101:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_80
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 81) ≤ val WuPaper.ClassicalFourthData.Bq 81
    have hp : val WuPaper.ClassicalFourthData.Bq 81 = (9923373495250:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 81 = 9923373495250 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 81 = (8081:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_81
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 82) ≤ val WuPaper.ClassicalFourthData.Bq 82
    have hp : val WuPaper.ClassicalFourthData.Bq 82 = (10043406715052:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 82 = 10043406715052 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 82 = (4041:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_82
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 83) ≤ val WuPaper.ClassicalFourthData.Bq 83
    have hp : val WuPaper.ClassicalFourthData.Bq 83 = (10163380535716:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 83 = 10163380535716 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 83 = (8083:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_83
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 84) ≤ val WuPaper.ClassicalFourthData.Bq 84
    have hp : val WuPaper.ClassicalFourthData.Bq 84 = (10283294993830:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 84 = 10283294993830 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 84 = (2021:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_84
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 85) ≤ val WuPaper.ClassicalFourthData.Bq 85
    have hp : val WuPaper.ClassicalFourthData.Bq 85 = (10403150125950:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 85 = 10403150125950 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 85 = (1617:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_85
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 86) ≤ val WuPaper.ClassicalFourthData.Bq 86
    have hp : val WuPaper.ClassicalFourthData.Bq 86 = (10522945968608:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 86 = 10522945968608 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 86 = (4043:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_86
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 87) ≤ val WuPaper.ClassicalFourthData.Bq 87
    have hp : val WuPaper.ClassicalFourthData.Bq 87 = (10642682558304:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 87 = 10642682558304 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 87 = (8087:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_87
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 88) ≤ val WuPaper.ClassicalFourthData.Bq 88
    have hp : val WuPaper.ClassicalFourthData.Bq 88 = (10762359931510:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 88 = 10762359931510 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 88 = (1011:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_88
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 89) ≤ val WuPaper.ClassicalFourthData.Bq 89
    have hp : val WuPaper.ClassicalFourthData.Bq 89 = (10881978124671:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 89 = 10881978124671 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 89 = (8089:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_89
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 90) ≤ val WuPaper.ClassicalFourthData.Bq 90
    have hp : val WuPaper.ClassicalFourthData.Bq 90 = (11001537174201:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 90 = 11001537174201 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 90 = (809:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_90
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 91) ≤ val WuPaper.ClassicalFourthData.Bq 91
    have hp : val WuPaper.ClassicalFourthData.Bq 91 = (11121037116486:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 91 = 11121037116486 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 91 = (8091:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_91
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 92) ≤ val WuPaper.ClassicalFourthData.Bq 92
    have hp : val WuPaper.ClassicalFourthData.Bq 92 = (11240477987885:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 92 = 11240477987885 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 92 = (2023:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_92
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 93) ≤ val WuPaper.ClassicalFourthData.Bq 93
    have hp : val WuPaper.ClassicalFourthData.Bq 93 = (11359859824726:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 93 = 11359859824726 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 93 = (8093:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_93
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 94) ≤ val WuPaper.ClassicalFourthData.Bq 94
    have hp : val WuPaper.ClassicalFourthData.Bq 94 = (11479182663310:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 94 = 11479182663310 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 94 = (4047:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_94
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 95) ≤ val WuPaper.ClassicalFourthData.Bq 95
    have hp : val WuPaper.ClassicalFourthData.Bq 95 = (11598446539910:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 95 = 11598446539910 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 95 = (1619:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_95
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_005
