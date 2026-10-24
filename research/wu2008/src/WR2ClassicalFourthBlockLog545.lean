import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints545
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_545 (j : Fin 16) (hj : 16*545+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*545+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*545+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8720) ≤ val WuPaper.ClassicalFourthData.Bq 8720
    have hp : val WuPaper.ClassicalFourthData.Bq 8720 = (276765836555682:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8720 = 276765836555682 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8720 = (209:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8720
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8721) ≤ val WuPaper.ClassicalFourthData.Bq 8721
    have hp : val WuPaper.ClassicalFourthData.Bq 8721 = (276768090440732:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8721 = 276768090440732 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8721 = (16721:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8721
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8722) ≤ val WuPaper.ClassicalFourthData.Bq 8722
    have hp : val WuPaper.ClassicalFourthData.Bq 8722 = (276770342578024:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8722 = 276770342578024 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8722 = (8361:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8722
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8723) ≤ val WuPaper.ClassicalFourthData.Bq 8723
    have hp : val WuPaper.ClassicalFourthData.Bq 8723 = (276772592968103:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8723 = 276772592968103 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8723 = (16723:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8723
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8724) ≤ val WuPaper.ClassicalFourthData.Bq 8724
    have hp : val WuPaper.ClassicalFourthData.Bq 8724 = (276774841611517:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8724 = 276774841611517 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8724 = (4181:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8724
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8725) ≤ val WuPaper.ClassicalFourthData.Bq 8725
    have hp : val WuPaper.ClassicalFourthData.Bq 8725 = (276777088508810:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8725 = 276777088508810 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8725 = (669:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8725
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8726) ≤ val WuPaper.ClassicalFourthData.Bq 8726
    have hp : val WuPaper.ClassicalFourthData.Bq 8726 = (276779333660528:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8726 = 276779333660528 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8726 = (8363:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8726
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8727) ≤ val WuPaper.ClassicalFourthData.Bq 8727
    have hp : val WuPaper.ClassicalFourthData.Bq 8727 = (276781577067215:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8727 = 276781577067215 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8727 = (16727:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8727
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8728) ≤ val WuPaper.ClassicalFourthData.Bq 8728
    have hp : val WuPaper.ClassicalFourthData.Bq 8728 = (276783818729417:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8728 = 276783818729417 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8728 = (2091:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8728
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8729) ≤ val WuPaper.ClassicalFourthData.Bq 8729
    have hp : val WuPaper.ClassicalFourthData.Bq 8729 = (276786058647679:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8729 = 276786058647679 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8729 = (16729:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8729
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8730) ≤ val WuPaper.ClassicalFourthData.Bq 8730
    have hp : val WuPaper.ClassicalFourthData.Bq 8730 = (276788296822544:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8730 = 276788296822544 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8730 = (1673:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8730
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8731) ≤ val WuPaper.ClassicalFourthData.Bq 8731
    have hp : val WuPaper.ClassicalFourthData.Bq 8731 = (276790533254559:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8731 = 276790533254559 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8731 = (16731:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8731
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8732) ≤ val WuPaper.ClassicalFourthData.Bq 8732
    have hp : val WuPaper.ClassicalFourthData.Bq 8732 = (276792767944266:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8732 = 276792767944266 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8732 = (4183:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8732
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8733) ≤ val WuPaper.ClassicalFourthData.Bq 8733
    have hp : val WuPaper.ClassicalFourthData.Bq 8733 = (276795000892210:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8733 = 276795000892210 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8733 = (16733:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8733
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8734) ≤ val WuPaper.ClassicalFourthData.Bq 8734
    have hp : val WuPaper.ClassicalFourthData.Bq 8734 = (276797232098934:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8734 = 276797232098934 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8734 = (8367:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8734
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8735) ≤ val WuPaper.ClassicalFourthData.Bq 8735
    have hp : val WuPaper.ClassicalFourthData.Bq 8735 = (276799461564983:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8735 = 276799461564983 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8735 = (3347:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8735
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_545
