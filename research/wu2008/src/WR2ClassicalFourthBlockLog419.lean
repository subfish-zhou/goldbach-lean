import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints419
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_419 (j : Fin 16) (hj : 16*419+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*419+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*419+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6704) ≤ val WuPaper.ClassicalFourthData.Bq 6704
    have hp : val WuPaper.ClassicalFourthData.Bq 6704 = (267770169278048:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6704 = 267770169278048 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6704 = (919:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6704
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6705) ≤ val WuPaper.ClassicalFourthData.Bq 6705
    have hp : val WuPaper.ClassicalFourthData.Bq 6705 = (267777371213023:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6705 = 267777371213023 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6705 = (2941:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6705
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6706) ≤ val WuPaper.ClassicalFourthData.Bq 6706
    have hp : val WuPaper.ClassicalFourthData.Bq 6706 = (267784569795028:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6706 = 267784569795028 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6706 = (7353:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6706
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6707) ≤ val WuPaper.ClassicalFourthData.Bq 6707
    have hp : val WuPaper.ClassicalFourthData.Bq 6707 = (267791765025189:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6707 = 267791765025189 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6707 = (14707:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6707
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6708) ≤ val WuPaper.ClassicalFourthData.Bq 6708
    have hp : val WuPaper.ClassicalFourthData.Bq 6708 = (267798956904634:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6708 = 267798956904634 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6708 = (3677:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6708
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6709) ≤ val WuPaper.ClassicalFourthData.Bq 6709
    have hp : val WuPaper.ClassicalFourthData.Bq 6709 = (267806145434488:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6709 = 267806145434488 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6709 = (14709:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6709
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6710) ≤ val WuPaper.ClassicalFourthData.Bq 6710
    have hp : val WuPaper.ClassicalFourthData.Bq 6710 = (267813330615878:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6710 = 267813330615878 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6710 = (1471:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6710
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6711) ≤ val WuPaper.ClassicalFourthData.Bq 6711
    have hp : val WuPaper.ClassicalFourthData.Bq 6711 = (267820512449929:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6711 = 267820512449929 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6711 = (14711:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6711
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6712) ≤ val WuPaper.ClassicalFourthData.Bq 6712
    have hp : val WuPaper.ClassicalFourthData.Bq 6712 = (267827690937766:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6712 = 267827690937766 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6712 = (1839:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6712
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6713) ≤ val WuPaper.ClassicalFourthData.Bq 6713
    have hp : val WuPaper.ClassicalFourthData.Bq 6713 = (267834866080515:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6713 = 267834866080515 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6713 = (14713:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6713
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6714) ≤ val WuPaper.ClassicalFourthData.Bq 6714
    have hp : val WuPaper.ClassicalFourthData.Bq 6714 = (267842037879299:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6714 = 267842037879299 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6714 = (7357:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6714
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6715) ≤ val WuPaper.ClassicalFourthData.Bq 6715
    have hp : val WuPaper.ClassicalFourthData.Bq 6715 = (267849206335243:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6715 = 267849206335243 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6715 = (2943:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6715
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6716) ≤ val WuPaper.ClassicalFourthData.Bq 6716
    have hp : val WuPaper.ClassicalFourthData.Bq 6716 = (267856371449469:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6716 = 267856371449469 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6716 = (3679:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6716
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6717) ≤ val WuPaper.ClassicalFourthData.Bq 6717
    have hp : val WuPaper.ClassicalFourthData.Bq 6717 = (267863533223101:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6717 = 267863533223101 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6717 = (14717:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6717
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6718) ≤ val WuPaper.ClassicalFourthData.Bq 6718
    have hp : val WuPaper.ClassicalFourthData.Bq 6718 = (267870691657262:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6718 = 267870691657262 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6718 = (7359:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6718
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6719) ≤ val WuPaper.ClassicalFourthData.Bq 6719
    have hp : val WuPaper.ClassicalFourthData.Bq 6719 = (267877846753072:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6719 = 267877846753072 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6719 = (14719:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6719
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_419
