import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints051
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_051 (j : Fin 16) : upperValue ((point (16*51+j.val)+point ((16*51+j.val)+1))/2) ≤ payment (16*51+j.val) := by
  fin_cases j
  · change upperValue ((point (816)+point ((816)+1))/2) ≤ payment (816)
    have hp : payment 816 = (2609164259699:ℝ)/1000000000000 := rfl
    have hx : (point 816+point 817)/2 = (2905891:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_816
  · change upperValue ((point (817)+point ((817)+1))/2) ≤ payment (817)
    have hp : payment 817 = (2605960873481:ℝ)/1000000000000 := rfl
    have hx : (point 817+point 818)/2 = (969315:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_817
  · change upperValue ((point (818)+point ((818)+1))/2) ≤ payment (818)
    have hp : payment 818 = (2602761138714:ℝ)/1000000000000 := rfl
    have hx : (point 818+point 819)/2 = (2909999:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_818
  · change upperValue ((point (819)+point ((819)+1))/2) ≤ payment (819)
    have hp : payment 819 = (2599565047037:ℝ)/1000000000000 := rfl
    have hx : (point 819+point 820)/2 = (2912053:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_819
  · change upperValue ((point (820)+point ((820)+1))/2) ≤ payment (820)
    have hp : payment 820 = (2596372590112:ℝ)/1000000000000 := rfl
    have hx : (point 820+point 821)/2 = (971369:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_820
  · change upperValue ((point (821)+point ((821)+1))/2) ≤ payment (821)
    have hp : payment 821 = (2593183759623:ℝ)/1000000000000 := rfl
    have hx : (point 821+point 822)/2 = (2916161:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_821
  · change upperValue ((point (822)+point ((822)+1))/2) ≤ payment (822)
    have hp : payment 822 = (2589998547279:ℝ)/1000000000000 := rfl
    have hx : (point 822+point 823)/2 = (2918215:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_822
  · change upperValue ((point (823)+point ((823)+1))/2) ≤ payment (823)
    have hp : payment 823 = (2586816944810:ℝ)/1000000000000 := rfl
    have hx : (point 823+point 824)/2 = (973423:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_823
  · change upperValue ((point (824)+point ((824)+1))/2) ≤ payment (824)
    have hp : payment 824 = (2583638943970:ℝ)/1000000000000 := rfl
    have hx : (point 824+point 825)/2 = (2922323:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_824
  · change upperValue ((point (825)+point ((825)+1))/2) ≤ payment (825)
    have hp : payment 825 = (2580464536533:ℝ)/1000000000000 := rfl
    have hx : (point 825+point 826)/2 = (2924377:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_825
  · change upperValue ((point (826)+point ((826)+1))/2) ≤ payment (826)
    have hp : payment 826 = (2577293714300:ℝ)/1000000000000 := rfl
    have hx : (point 826+point 827)/2 = (975477:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_826
  · change upperValue ((point (827)+point ((827)+1))/2) ≤ payment (827)
    have hp : payment 827 = (2574126469089:ℝ)/1000000000000 := rfl
    have hx : (point 827+point 828)/2 = (2928485:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_827
  · change upperValue ((point (828)+point ((828)+1))/2) ≤ payment (828)
    have hp : payment 828 = (2570962792745:ℝ)/1000000000000 := rfl
    have hx : (point 828+point 829)/2 = (2930539:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_828
  · change upperValue ((point (829)+point ((829)+1))/2) ≤ payment (829)
    have hp : payment 829 = (2567802677133:ℝ)/1000000000000 := rfl
    have hx : (point 829+point 830)/2 = (977531:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_829
  · change upperValue ((point (830)+point ((830)+1))/2) ≤ payment (830)
    have hp : payment 830 = (2564646114140:ℝ)/1000000000000 := rfl
    have hx : (point 830+point 831)/2 = (2934647:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_830
  · change upperValue ((point (831)+point ((831)+1))/2) ≤ payment (831)
    have hp : payment 831 = (2561493095677:ℝ)/1000000000000 := rfl
    have hx : (point 831+point 832)/2 = (2936701:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_831
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_051
