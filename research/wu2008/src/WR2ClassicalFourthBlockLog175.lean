import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints175
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_175 (j : Fin 16) (hj : 16*175+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*175+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*175+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2800) ≤ val WuPaper.ClassicalFourthData.Bq 2800
    have hp : val WuPaper.ClassicalFourthData.Bq 2800 = (196528981874878:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2800 = 196528981874878 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2800 = (27:ℝ)/10 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2800
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2801) ≤ val WuPaper.ClassicalFourthData.Bq 2801
    have hp : val WuPaper.ClassicalFourthData.Bq 2801 = (196565243615818:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2801 = 196565243615818 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2801 = (10801:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2801
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2802) ≤ val WuPaper.ClassicalFourthData.Bq 2802
    have hp : val WuPaper.ClassicalFourthData.Bq 2802 = (196601490636961:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2802 = 196601490636961 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2802 = (5401:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2802
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2803) ≤ val WuPaper.ClassicalFourthData.Bq 2803
    have hp : val WuPaper.ClassicalFourthData.Bq 2803 = (196637722944750:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2803 = 196637722944750 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2803 = (10803:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2803
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2804) ≤ val WuPaper.ClassicalFourthData.Bq 2804
    have hp : val WuPaper.ClassicalFourthData.Bq 2804 = (196673940545622:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2804 = 196673940545622 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2804 = (2701:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2804
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2805) ≤ val WuPaper.ClassicalFourthData.Bq 2805
    have hp : val WuPaper.ClassicalFourthData.Bq 2805 = (196710143446012:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2805 = 196710143446012 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2805 = (2161:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2805
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2806) ≤ val WuPaper.ClassicalFourthData.Bq 2806
    have hp : val WuPaper.ClassicalFourthData.Bq 2806 = (196746331652350:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2806 = 196746331652350 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2806 = (5403:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2806
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2807) ≤ val WuPaper.ClassicalFourthData.Bq 2807
    have hp : val WuPaper.ClassicalFourthData.Bq 2807 = (196782505171065:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2807 = 196782505171065 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2807 = (10807:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2807
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2808) ≤ val WuPaper.ClassicalFourthData.Bq 2808
    have hp : val WuPaper.ClassicalFourthData.Bq 2808 = (196818664008580:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2808 = 196818664008580 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2808 = (1351:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2808
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2809) ≤ val WuPaper.ClassicalFourthData.Bq 2809
    have hp : val WuPaper.ClassicalFourthData.Bq 2809 = (196854808171317:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2809 = 196854808171317 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2809 = (10809:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2809
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2810) ≤ val WuPaper.ClassicalFourthData.Bq 2810
    have hp : val WuPaper.ClassicalFourthData.Bq 2810 = (196890937665692:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2810 = 196890937665692 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2810 = (1081:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2810
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2811) ≤ val WuPaper.ClassicalFourthData.Bq 2811
    have hp : val WuPaper.ClassicalFourthData.Bq 2811 = (196927052498119:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2811 = 196927052498119 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2811 = (10811:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2811
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2812) ≤ val WuPaper.ClassicalFourthData.Bq 2812
    have hp : val WuPaper.ClassicalFourthData.Bq 2812 = (196963152675010:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2812 = 196963152675010 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2812 = (2703:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2812
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2813) ≤ val WuPaper.ClassicalFourthData.Bq 2813
    have hp : val WuPaper.ClassicalFourthData.Bq 2813 = (196999238202771:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2813 = 196999238202771 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2813 = (10813:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2813
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2814) ≤ val WuPaper.ClassicalFourthData.Bq 2814
    have hp : val WuPaper.ClassicalFourthData.Bq 2814 = (197035309087807:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2814 = 197035309087807 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2814 = (5407:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2814
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2815) ≤ val WuPaper.ClassicalFourthData.Bq 2815
    have hp : val WuPaper.ClassicalFourthData.Bq 2815 = (197071365336517:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2815 = 197071365336517 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2815 = (2163:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2815
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_175
