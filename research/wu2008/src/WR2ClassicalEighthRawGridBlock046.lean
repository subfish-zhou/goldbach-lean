import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints046
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_046 (j : Fin 16) : upperValue ((point (16*46+j.val)+point ((16*46+j.val)+1))/2) ≤ payment (16*46+j.val) := by
  fin_cases j
  · change upperValue ((point (736)+point ((736)+1))/2) ≤ payment (736)
    have hp : payment 736 = (2878051256413:ℝ)/1000000000000 := rfl
    have hx : (point 736+point 737)/2 = (913857:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_736
  · change upperValue ((point (737)+point ((737)+1))/2) ≤ payment (737)
    have hp : payment 737 = (2874526466018:ℝ)/1000000000000 := rfl
    have hx : (point 737+point 738)/2 = (2743625:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_737
  · change upperValue ((point (738)+point ((738)+1))/2) ≤ payment (738)
    have hp : payment 738 = (2871006078400:ℝ)/1000000000000 := rfl
    have hx : (point 738+point 739)/2 = (2745679:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_738
  · change upperValue ((point (739)+point ((739)+1))/2) ≤ payment (739)
    have hp : payment 739 = (2867490083058:ℝ)/1000000000000 := rfl
    have hx : (point 739+point 740)/2 = (915911:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_739
  · change upperValue ((point (740)+point ((740)+1))/2) ≤ payment (740)
    have hp : payment 740 = (2863978469524:ℝ)/1000000000000 := rfl
    have hx : (point 740+point 741)/2 = (2749787:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_740
  · change upperValue ((point (741)+point ((741)+1))/2) ≤ payment (741)
    have hp : payment 741 = (2860471227360:ℝ)/1000000000000 := rfl
    have hx : (point 741+point 742)/2 = (2751841:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_741
  · change upperValue ((point (742)+point ((742)+1))/2) ≤ payment (742)
    have hp : payment 742 = (2856968346158:ℝ)/1000000000000 := rfl
    have hx : (point 742+point 743)/2 = (917965:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_742
  · change upperValue ((point (743)+point ((743)+1))/2) ≤ payment (743)
    have hp : payment 743 = (2853469815541:ℝ)/1000000000000 := rfl
    have hx : (point 743+point 744)/2 = (2755949:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_743
  · change upperValue ((point (744)+point ((744)+1))/2) ≤ payment (744)
    have hp : payment 744 = (2849975625163:ℝ)/1000000000000 := rfl
    have hx : (point 744+point 745)/2 = (2758003:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_744
  · change upperValue ((point (745)+point ((745)+1))/2) ≤ payment (745)
    have hp : payment 745 = (2846485764707:ℝ)/1000000000000 := rfl
    have hx : (point 745+point 746)/2 = (920019:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_745
  · change upperValue ((point (746)+point ((746)+1))/2) ≤ payment (746)
    have hp : payment 746 = (2843000223887:ℝ)/1000000000000 := rfl
    have hx : (point 746+point 747)/2 = (2762111:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_746
  · change upperValue ((point (747)+point ((747)+1))/2) ≤ payment (747)
    have hp : payment 747 = (2839518992447:ℝ)/1000000000000 := rfl
    have hx : (point 747+point 748)/2 = (2764165:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_747
  · change upperValue ((point (748)+point ((748)+1))/2) ≤ payment (748)
    have hp : payment 748 = (2836042060160:ℝ)/1000000000000 := rfl
    have hx : (point 748+point 749)/2 = (922073:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_748
  · change upperValue ((point (749)+point ((749)+1))/2) ≤ payment (749)
    have hp : payment 749 = (2832569416830:ℝ)/1000000000000 := rfl
    have hx : (point 749+point 750)/2 = (2768273:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_749
  · change upperValue ((point (750)+point ((750)+1))/2) ≤ payment (750)
    have hp : payment 750 = (2829101052289:ℝ)/1000000000000 := rfl
    have hx : (point 750+point 751)/2 = (2770327:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_750
  · change upperValue ((point (751)+point ((751)+1))/2) ≤ payment (751)
    have hp : payment 751 = (2825636956402:ℝ)/1000000000000 := rfl
    have hx : (point 751+point 752)/2 = (924127:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_751
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_046
