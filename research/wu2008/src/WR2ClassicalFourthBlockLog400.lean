import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints400
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_400 (j : Fin 16) (hj : 16*400+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*400+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*400+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6400) ≤ val WuPaper.ClassicalFourthData.Bq 6400
    have hp : val WuPaper.ClassicalFourthData.Bq 6400 = (265419845840970:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6400 = 265419845840970 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6400 = (18:ℝ)/5 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6400
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6401) ≤ val WuPaper.ClassicalFourthData.Bq 6401
    have hp : val WuPaper.ClassicalFourthData.Bq 6401 = (265428121450221:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6401 = 265428121450221 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6401 = (14401:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6401
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6402) ≤ val WuPaper.ClassicalFourthData.Bq 6402
    have hp : val WuPaper.ClassicalFourthData.Bq 6402 = (265436393342881:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6402 = 265436393342881 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6402 = (7201:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6402
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6403) ≤ val WuPaper.ClassicalFourthData.Bq 6403
    have hp : val WuPaper.ClassicalFourthData.Bq 6403 = (265444661520217:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6403 = 265444661520217 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6403 = (14403:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6403
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6404) ≤ val WuPaper.ClassicalFourthData.Bq 6404
    have hp : val WuPaper.ClassicalFourthData.Bq 6404 = (265452925983496:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6404 = 265452925983496 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6404 = (3601:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6404
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6405) ≤ val WuPaper.ClassicalFourthData.Bq 6405
    have hp : val WuPaper.ClassicalFourthData.Bq 6405 = (265461186733985:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6405 = 265461186733985 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6405 = (2881:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6405
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6406) ≤ val WuPaper.ClassicalFourthData.Bq 6406
    have hp : val WuPaper.ClassicalFourthData.Bq 6406 = (265469443772949:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6406 = 265469443772949 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6406 = (7203:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6406
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6407) ≤ val WuPaper.ClassicalFourthData.Bq 6407
    have hp : val WuPaper.ClassicalFourthData.Bq 6407 = (265477697101655:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6407 = 265477697101655 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6407 = (14407:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6407
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6408) ≤ val WuPaper.ClassicalFourthData.Bq 6408
    have hp : val WuPaper.ClassicalFourthData.Bq 6408 = (265485946721368:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6408 = 265485946721368 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6408 = (1801:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6408
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6409) ≤ val WuPaper.ClassicalFourthData.Bq 6409
    have hp : val WuPaper.ClassicalFourthData.Bq 6409 = (265494192633353:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6409 = 265494192633353 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6409 = (14409:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6409
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6410) ≤ val WuPaper.ClassicalFourthData.Bq 6410
    have hp : val WuPaper.ClassicalFourthData.Bq 6410 = (265502434838874:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6410 = 265502434838874 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6410 = (1441:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6410
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6411) ≤ val WuPaper.ClassicalFourthData.Bq 6411
    have hp : val WuPaper.ClassicalFourthData.Bq 6411 = (265510673339194:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6411 = 265510673339194 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6411 = (14411:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6411
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6412) ≤ val WuPaper.ClassicalFourthData.Bq 6412
    have hp : val WuPaper.ClassicalFourthData.Bq 6412 = (265518908135577:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6412 = 265518908135577 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6412 = (3603:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6412
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6413) ≤ val WuPaper.ClassicalFourthData.Bq 6413
    have hp : val WuPaper.ClassicalFourthData.Bq 6413 = (265527139229286:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6413 = 265527139229286 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6413 = (14413:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6413
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6414) ≤ val WuPaper.ClassicalFourthData.Bq 6414
    have hp : val WuPaper.ClassicalFourthData.Bq 6414 = (265535366621583:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6414 = 265535366621583 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6414 = (7207:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6414
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6415) ≤ val WuPaper.ClassicalFourthData.Bq 6415
    have hp : val WuPaper.ClassicalFourthData.Bq 6415 = (265543590313729:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6415 = 265543590313729 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6415 = (2883:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6415
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_400
