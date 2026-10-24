import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints542
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_542 (j : Fin 16) (hj : 16*542+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*542+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*542+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8672) ≤ val WuPaper.ClassicalFourthData.Bq 8672
    have hp : val WuPaper.ClassicalFourthData.Bq 8672 = (276655583963993:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8672 = 276655583963993 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8672 = (521:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8672
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8673) ≤ val WuPaper.ClassicalFourthData.Bq 8673
    have hp : val WuPaper.ClassicalFourthData.Bq 8673 = (276657922387045:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8673 = 276657922387045 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8673 = (16673:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8673
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8674) ≤ val WuPaper.ClassicalFourthData.Bq 8674
    have hp : val WuPaper.ClassicalFourthData.Bq 8674 = (276660259035916:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8674 = 276660259035916 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8674 = (8337:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8674
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8675) ≤ val WuPaper.ClassicalFourthData.Bq 8675
    have hp : val WuPaper.ClassicalFourthData.Bq 8675 = (276662593911162:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8675 = 276662593911162 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8675 = (667:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8675
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8676) ≤ val WuPaper.ClassicalFourthData.Bq 8676
    have hp : val WuPaper.ClassicalFourthData.Bq 8676 = (276664927013337:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8676 = 276664927013337 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8676 = (4169:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8676
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8677) ≤ val WuPaper.ClassicalFourthData.Bq 8677
    have hp : val WuPaper.ClassicalFourthData.Bq 8677 = (276667258342996:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8677 = 276667258342996 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8677 = (16677:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8677
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8678) ≤ val WuPaper.ClassicalFourthData.Bq 8678
    have hp : val WuPaper.ClassicalFourthData.Bq 8678 = (276669587900693:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8678 = 276669587900693 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8678 = (8339:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8678
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8679) ≤ val WuPaper.ClassicalFourthData.Bq 8679
    have hp : val WuPaper.ClassicalFourthData.Bq 8679 = (276671915686982:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8679 = 276671915686982 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8679 = (16679:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8679
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8680) ≤ val WuPaper.ClassicalFourthData.Bq 8680
    have hp : val WuPaper.ClassicalFourthData.Bq 8680 = (276674241702418:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8680 = 276674241702418 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8680 = (417:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8680
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8681) ≤ val WuPaper.ClassicalFourthData.Bq 8681
    have hp : val WuPaper.ClassicalFourthData.Bq 8681 = (276676565947553:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8681 = 276676565947553 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8681 = (16681:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8681
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8682) ≤ val WuPaper.ClassicalFourthData.Bq 8682
    have hp : val WuPaper.ClassicalFourthData.Bq 8682 = (276678888422942:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8682 = 276678888422942 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8682 = (8341:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8682
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8683) ≤ val WuPaper.ClassicalFourthData.Bq 8683
    have hp : val WuPaper.ClassicalFourthData.Bq 8683 = (276681209129137:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8683 = 276681209129137 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8683 = (16683:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8683
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8684) ≤ val WuPaper.ClassicalFourthData.Bq 8684
    have hp : val WuPaper.ClassicalFourthData.Bq 8684 = (276683528066693:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8684 = 276683528066693 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8684 = (4171:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8684
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8685) ≤ val WuPaper.ClassicalFourthData.Bq 8685
    have hp : val WuPaper.ClassicalFourthData.Bq 8685 = (276685845236162:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8685 = 276685845236162 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8685 = (3337:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8685
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8686) ≤ val WuPaper.ClassicalFourthData.Bq 8686
    have hp : val WuPaper.ClassicalFourthData.Bq 8686 = (276688160638096:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8686 = 276688160638096 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8686 = (8343:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8686
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8687) ≤ val WuPaper.ClassicalFourthData.Bq 8687
    have hp : val WuPaper.ClassicalFourthData.Bq 8687 = (276690474273049:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8687 = 276690474273049 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8687 = (16687:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8687
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_542
