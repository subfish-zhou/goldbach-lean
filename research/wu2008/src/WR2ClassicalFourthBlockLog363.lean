import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints363
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_363 (j : Fin 16) (hj : 16*363+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*363+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*363+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5808) ≤ val WuPaper.ClassicalFourthData.Bq 5808
    have hp : val WuPaper.ClassicalFourthData.Bq 5808 = (259821557958857:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5808 = 259821557958857 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5808 = (863:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5808
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5809) ≤ val WuPaper.ClassicalFourthData.Bq 5809
    have hp : val WuPaper.ClassicalFourthData.Bq 5809 = (259832274737432:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5809 = 259832274737432 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5809 = (13809:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5809
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5810) ≤ val WuPaper.ClassicalFourthData.Bq 5810
    have hp : val WuPaper.ClassicalFourthData.Bq 5810 = (259842986953625:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5810 = 259842986953625 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5810 = (1381:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5810
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5811) ≤ val WuPaper.ClassicalFourthData.Bq 5811
    have hp : val WuPaper.ClassicalFourthData.Bq 5811 = (259853694609043:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5811 = 259853694609043 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5811 = (13811:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5811
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5812) ≤ val WuPaper.ClassicalFourthData.Bq 5812
    have hp : val WuPaper.ClassicalFourthData.Bq 5812 = (259864397705289:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5812 = 259864397705289 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5812 = (3453:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5812
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5813) ≤ val WuPaper.ClassicalFourthData.Bq 5813
    have hp : val WuPaper.ClassicalFourthData.Bq 5813 = (259875096243966:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5813 = 259875096243966 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5813 = (13813:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5813
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5814) ≤ val WuPaper.ClassicalFourthData.Bq 5814
    have hp : val WuPaper.ClassicalFourthData.Bq 5814 = (259885790226678:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5814 = 259885790226678 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5814 = (6907:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5814
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5815) ≤ val WuPaper.ClassicalFourthData.Bq 5815
    have hp : val WuPaper.ClassicalFourthData.Bq 5815 = (259896479655026:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5815 = 259896479655026 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5815 = (2763:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5815
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5816) ≤ val WuPaper.ClassicalFourthData.Bq 5816
    have hp : val WuPaper.ClassicalFourthData.Bq 5816 = (259907164530611:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5816 = 259907164530611 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5816 = (1727:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5816
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5817) ≤ val WuPaper.ClassicalFourthData.Bq 5817
    have hp : val WuPaper.ClassicalFourthData.Bq 5817 = (259917844855035:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5817 = 259917844855035 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5817 = (13817:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5817
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5818) ≤ val WuPaper.ClassicalFourthData.Bq 5818
    have hp : val WuPaper.ClassicalFourthData.Bq 5818 = (259928520629898:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5818 = 259928520629898 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5818 = (6909:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5818
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5819) ≤ val WuPaper.ClassicalFourthData.Bq 5819
    have hp : val WuPaper.ClassicalFourthData.Bq 5819 = (259939191856798:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5819 = 259939191856798 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5819 = (13819:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5819
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5820) ≤ val WuPaper.ClassicalFourthData.Bq 5820
    have hp : val WuPaper.ClassicalFourthData.Bq 5820 = (259949858537336:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5820 = 259949858537336 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5820 = (691:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5820
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5821) ≤ val WuPaper.ClassicalFourthData.Bq 5821
    have hp : val WuPaper.ClassicalFourthData.Bq 5821 = (259960520673108:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5821 = 259960520673108 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5821 = (13821:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5821
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5822) ≤ val WuPaper.ClassicalFourthData.Bq 5822
    have hp : val WuPaper.ClassicalFourthData.Bq 5822 = (259971178265714:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5822 = 259971178265714 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5822 = (6911:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5822
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5823) ≤ val WuPaper.ClassicalFourthData.Bq 5823
    have hp : val WuPaper.ClassicalFourthData.Bq 5823 = (259981831316748:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5823 = 259981831316748 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5823 = (13823:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5823
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_363
