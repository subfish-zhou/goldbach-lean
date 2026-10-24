import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints180
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_180 (j : Fin 16) (hj : 16*180+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*180+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*180+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2880) ≤ val WuPaper.ClassicalFourthData.Bq 2880
    have hp : val WuPaper.ClassicalFourthData.Bq 2880 = (199383930450501:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2880 = 199383930450501 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2880 = (68:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2880
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2881) ≤ val WuPaper.ClassicalFourthData.Bq 2881
    have hp : val WuPaper.ClassicalFourthData.Bq 2881 = (199419034684479:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2881 = 199419034684479 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2881 = (10881:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2881
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2882) ≤ val WuPaper.ClassicalFourthData.Bq 2882
    have hp : val WuPaper.ClassicalFourthData.Bq 2882 = (199454124703326:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2882 = 199454124703326 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2882 = (5441:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2882
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2883) ≤ val WuPaper.ClassicalFourthData.Bq 2883
    have hp : val WuPaper.ClassicalFourthData.Bq 2883 = (199489200513218:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2883 = 199489200513218 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2883 = (10883:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2883
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2884) ≤ val WuPaper.ClassicalFourthData.Bq 2884
    have hp : val WuPaper.ClassicalFourthData.Bq 2884 = (199524262120325:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2884 = 199524262120325 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2884 = (2721:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2884
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2885) ≤ val WuPaper.ClassicalFourthData.Bq 2885
    have hp : val WuPaper.ClassicalFourthData.Bq 2885 = (199559309530814:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2885 = 199559309530814 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2885 = (2177:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2885
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2886) ≤ val WuPaper.ClassicalFourthData.Bq 2886
    have hp : val WuPaper.ClassicalFourthData.Bq 2886 = (199594342750852:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2886 = 199594342750852 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2886 = (5443:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2886
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2887) ≤ val WuPaper.ClassicalFourthData.Bq 2887
    have hp : val WuPaper.ClassicalFourthData.Bq 2887 = (199629361786598:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2887 = 199629361786598 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2887 = (10887:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2887
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2888) ≤ val WuPaper.ClassicalFourthData.Bq 2888
    have hp : val WuPaper.ClassicalFourthData.Bq 2888 = (199664366644210:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2888 = 199664366644210 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2888 = (1361:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2888
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2889) ≤ val WuPaper.ClassicalFourthData.Bq 2889
    have hp : val WuPaper.ClassicalFourthData.Bq 2889 = (199699357329845:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2889 = 199699357329845 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2889 = (10889:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2889
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2890) ≤ val WuPaper.ClassicalFourthData.Bq 2890
    have hp : val WuPaper.ClassicalFourthData.Bq 2890 = (199734333849652:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2890 = 199734333849652 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2890 = (1089:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2890
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2891) ≤ val WuPaper.ClassicalFourthData.Bq 2891
    have hp : val WuPaper.ClassicalFourthData.Bq 2891 = (199769296209781:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2891 = 199769296209781 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2891 = (10891:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2891
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2892) ≤ val WuPaper.ClassicalFourthData.Bq 2892
    have hp : val WuPaper.ClassicalFourthData.Bq 2892 = (199804244416377:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2892 = 199804244416377 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2892 = (2723:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2892
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2893) ≤ val WuPaper.ClassicalFourthData.Bq 2893
    have hp : val WuPaper.ClassicalFourthData.Bq 2893 = (199839178475581:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2893 = 199839178475581 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2893 = (10893:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2893
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2894) ≤ val WuPaper.ClassicalFourthData.Bq 2894
    have hp : val WuPaper.ClassicalFourthData.Bq 2894 = (199874098393532:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2894 = 199874098393532 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2894 = (5447:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2894
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2895) ≤ val WuPaper.ClassicalFourthData.Bq 2895
    have hp : val WuPaper.ClassicalFourthData.Bq 2895 = (199909004176366:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2895 = 199909004176366 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2895 = (2179:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2895
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_180
