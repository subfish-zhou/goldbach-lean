import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints106
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_106 (j : Fin 16) (hj : 16*106+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*106+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*106+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1696) ≤ val WuPaper.ClassicalFourthData.Bq 1696
    have hp : val WuPaper.ClassicalFourthData.Bq 1696 = (145820879946281:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1696 = 145820879946281 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1696 = (303:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1696
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1697) ≤ val WuPaper.ClassicalFourthData.Bq 1697
    have hp : val WuPaper.ClassicalFourthData.Bq 1697 = (145878254874031:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1697 = 145878254874031 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1697 = (9697:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1697
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1698) ≤ val WuPaper.ClassicalFourthData.Bq 1698
    have hp : val WuPaper.ClassicalFourthData.Bq 1698 = (145935605261220:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1698 = 145935605261220 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1698 = (4849:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1698
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1699) ≤ val WuPaper.ClassicalFourthData.Bq 1699
    have hp : val WuPaper.ClassicalFourthData.Bq 1699 = (145992931119898:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1699 = 145992931119898 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1699 = (9699:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1699
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1700) ≤ val WuPaper.ClassicalFourthData.Bq 1700
    have hp : val WuPaper.ClassicalFourthData.Bq 1700 = (146050232462109:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1700 = 146050232462109 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1700 = (97:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1700
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1701) ≤ val WuPaper.ClassicalFourthData.Bq 1701
    have hp : val WuPaper.ClassicalFourthData.Bq 1701 = (146107509299889:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1701 = 146107509299889 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1701 = (9701:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1701
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1702) ≤ val WuPaper.ClassicalFourthData.Bq 1702
    have hp : val WuPaper.ClassicalFourthData.Bq 1702 = (146164761645265:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1702 = 146164761645265 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1702 = (4851:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1702
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1703) ≤ val WuPaper.ClassicalFourthData.Bq 1703
    have hp : val WuPaper.ClassicalFourthData.Bq 1703 = (146221989510260:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1703 = 146221989510260 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1703 = (9703:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1703
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1704) ≤ val WuPaper.ClassicalFourthData.Bq 1704
    have hp : val WuPaper.ClassicalFourthData.Bq 1704 = (146279192906886:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1704 = 146279192906886 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1704 = (1213:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1704
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1705) ≤ val WuPaper.ClassicalFourthData.Bq 1705
    have hp : val WuPaper.ClassicalFourthData.Bq 1705 = (146336371847151:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1705 = 146336371847151 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1705 = (1941:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1705
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1706) ≤ val WuPaper.ClassicalFourthData.Bq 1706
    have hp : val WuPaper.ClassicalFourthData.Bq 1706 = (146393526343053:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1706 = 146393526343053 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1706 = (4853:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1706
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1707) ≤ val WuPaper.ClassicalFourthData.Bq 1707
    have hp : val WuPaper.ClassicalFourthData.Bq 1707 = (146450656406586:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1707 = 146450656406586 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1707 = (9707:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1707
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1708) ≤ val WuPaper.ClassicalFourthData.Bq 1708
    have hp : val WuPaper.ClassicalFourthData.Bq 1708 = (146507762049732:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1708 = 146507762049732 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1708 = (2427:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1708
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1709) ≤ val WuPaper.ClassicalFourthData.Bq 1709
    have hp : val WuPaper.ClassicalFourthData.Bq 1709 = (146564843284471:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1709 = 146564843284471 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1709 = (9709:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1709
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1710) ≤ val WuPaper.ClassicalFourthData.Bq 1710
    have hp : val WuPaper.ClassicalFourthData.Bq 1710 = (146621900122772:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1710 = 146621900122772 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1710 = (971:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1710
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1711) ≤ val WuPaper.ClassicalFourthData.Bq 1711
    have hp : val WuPaper.ClassicalFourthData.Bq 1711 = (146678932576598:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1711 = 146678932576598 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1711 = (9711:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1711
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_106
