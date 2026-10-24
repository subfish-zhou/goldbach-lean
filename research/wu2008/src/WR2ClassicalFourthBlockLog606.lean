import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints606
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_606 (j : Fin 16) (hj : 16*606+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*606+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*606+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9696) ≤ val WuPaper.ClassicalFourthData.Bq 9696
    have hp : val WuPaper.ClassicalFourthData.Bq 9696 = (278211902879332:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9696 = 278211902879332 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9696 = (553:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9696
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9697) ≤ val WuPaper.ClassicalFourthData.Bq 9697
    have hp : val WuPaper.ClassicalFourthData.Bq 9697 = (278212684566098:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9697 = 278212684566098 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9697 = (17697:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9697
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9698) ≤ val WuPaper.ClassicalFourthData.Bq 9698
    have hp : val WuPaper.ClassicalFourthData.Bq 9698 = (278213464959811:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9698 = 278213464959811 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9698 = (8849:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9698
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9699) ≤ val WuPaper.ClassicalFourthData.Bq 9699
    have hp : val WuPaper.ClassicalFourthData.Bq 9699 = (278214244060867:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9699 = 278214244060867 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9699 = (17699:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9699
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9700) ≤ val WuPaper.ClassicalFourthData.Bq 9700
    have hp : val WuPaper.ClassicalFourthData.Bq 9700 = (278215021869659:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9700 = 278215021869659 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9700 = (177:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9700
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9701) ≤ val WuPaper.ClassicalFourthData.Bq 9701
    have hp : val WuPaper.ClassicalFourthData.Bq 9701 = (278215798386584:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9701 = 278215798386584 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9701 = (17701:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9701
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9702) ≤ val WuPaper.ClassicalFourthData.Bq 9702
    have hp : val WuPaper.ClassicalFourthData.Bq 9702 = (278216573612035:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9702 = 278216573612035 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9702 = (8851:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9702
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9703) ≤ val WuPaper.ClassicalFourthData.Bq 9703
    have hp : val WuPaper.ClassicalFourthData.Bq 9703 = (278217347546408:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9703 = 278217347546408 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9703 = (17703:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9703
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9704) ≤ val WuPaper.ClassicalFourthData.Bq 9704
    have hp : val WuPaper.ClassicalFourthData.Bq 9704 = (278218120190096:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9704 = 278218120190096 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9704 = (2213:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9704
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9705) ≤ val WuPaper.ClassicalFourthData.Bq 9705
    have hp : val WuPaper.ClassicalFourthData.Bq 9705 = (278218891543495:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9705 = 278218891543495 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9705 = (3541:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9705
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9706) ≤ val WuPaper.ClassicalFourthData.Bq 9706
    have hp : val WuPaper.ClassicalFourthData.Bq 9706 = (278219661606997:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9706 = 278219661606997 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9706 = (8853:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9706
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9707) ≤ val WuPaper.ClassicalFourthData.Bq 9707
    have hp : val WuPaper.ClassicalFourthData.Bq 9707 = (278220430380998:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9707 = 278220430380998 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9707 = (17707:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9707
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9708) ≤ val WuPaper.ClassicalFourthData.Bq 9708
    have hp : val WuPaper.ClassicalFourthData.Bq 9708 = (278221197865891:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9708 = 278221197865891 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9708 = (4427:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9708
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9709) ≤ val WuPaper.ClassicalFourthData.Bq 9709
    have hp : val WuPaper.ClassicalFourthData.Bq 9709 = (278221964062069:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9709 = 278221964062069 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9709 = (17709:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9709
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9710) ≤ val WuPaper.ClassicalFourthData.Bq 9710
    have hp : val WuPaper.ClassicalFourthData.Bq 9710 = (278222728969927:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9710 = 278222728969927 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9710 = (1771:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9710
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9711) ≤ val WuPaper.ClassicalFourthData.Bq 9711
    have hp : val WuPaper.ClassicalFourthData.Bq 9711 = (278223492589858:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9711 = 278223492589858 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9711 = (17711:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9711
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_606
