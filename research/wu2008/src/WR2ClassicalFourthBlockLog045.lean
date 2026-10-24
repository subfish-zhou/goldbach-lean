import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints045
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_045 (j : Fin 16) (hj : 16*45+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*45+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*45+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 720) ≤ val WuPaper.ClassicalFourthData.Bq 720
    have hp : val WuPaper.ClassicalFourthData.Bq 720 = (75924054347511:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 720 = 75924054347511 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 720 = (109:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_720
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 721) ≤ val WuPaper.ClassicalFourthData.Bq 721
    have hp : val WuPaper.ClassicalFourthData.Bq 721 = (76012512530334:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 721 = 76012512530334 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 721 = (8721:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_721
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 722) ≤ val WuPaper.ClassicalFourthData.Bq 722
    have hp : val WuPaper.ClassicalFourthData.Bq 722 = (76100929852525:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 722 = 76100929852525 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 722 = (4361:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_722
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 723) ≤ val WuPaper.ClassicalFourthData.Bq 723
    have hp : val WuPaper.ClassicalFourthData.Bq 723 = (76189306336852:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 723 = 76189306336852 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 723 = (8723:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_723
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 724) ≤ val WuPaper.ClassicalFourthData.Bq 724
    have hp : val WuPaper.ClassicalFourthData.Bq 724 = (76277642006064:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 724 = 76277642006064 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 724 = (2181:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_724
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 725) ≤ val WuPaper.ClassicalFourthData.Bq 725
    have hp : val WuPaper.ClassicalFourthData.Bq 725 = (76365936882896:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 725 = 76365936882896 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 725 = (349:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_725
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 726) ≤ val WuPaper.ClassicalFourthData.Bq 726
    have hp : val WuPaper.ClassicalFourthData.Bq 726 = (76454190990065:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 726 = 76454190990065 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 726 = (4363:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_726
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 727) ≤ val WuPaper.ClassicalFourthData.Bq 727
    have hp : val WuPaper.ClassicalFourthData.Bq 727 = (76542404350274:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 727 = 76542404350274 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 727 = (8727:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_727
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 728) ≤ val WuPaper.ClassicalFourthData.Bq 728
    have hp : val WuPaper.ClassicalFourthData.Bq 728 = (76630576986209:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 728 = 76630576986209 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 728 = (1091:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_728
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 729) ≤ val WuPaper.ClassicalFourthData.Bq 729
    have hp : val WuPaper.ClassicalFourthData.Bq 729 = (76718708920540:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 729 = 76718708920540 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 729 = (8729:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_729
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 730) ≤ val WuPaper.ClassicalFourthData.Bq 730
    have hp : val WuPaper.ClassicalFourthData.Bq 730 = (76806800175923:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 730 = 76806800175923 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 730 = (873:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_730
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 731) ≤ val WuPaper.ClassicalFourthData.Bq 731
    have hp : val WuPaper.ClassicalFourthData.Bq 731 = (76894850774996:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 731 = 76894850774996 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 731 = (8731:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_731
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 732) ≤ val WuPaper.ClassicalFourthData.Bq 732
    have hp : val WuPaper.ClassicalFourthData.Bq 732 = (76982860740381:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 732 = 76982860740381 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 732 = (2183:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_732
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 733) ≤ val WuPaper.ClassicalFourthData.Bq 733
    have hp : val WuPaper.ClassicalFourthData.Bq 733 = (77070830094685:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 733 = 77070830094685 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 733 = (8733:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_733
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 734) ≤ val WuPaper.ClassicalFourthData.Bq 734
    have hp : val WuPaper.ClassicalFourthData.Bq 734 = (77158758860500:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 734 = 77158758860500 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 734 = (4367:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_734
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 735) ≤ val WuPaper.ClassicalFourthData.Bq 735
    have hp : val WuPaper.ClassicalFourthData.Bq 735 = (77246647060402:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 735 = 77246647060402 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 735 = (1747:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_735
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_045
