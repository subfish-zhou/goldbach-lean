import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints062
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_062 (j : Fin 16) : upperValue ((point (16*62+j.val)+point ((16*62+j.val)+1))/2) ≤ payment (16*62+j.val) := by
  fin_cases j
  · change upperValue ((point (992)+point ((992)+1))/2) ≤ payment (992)
    have hp : payment 992 = (2094924370361:ℝ)/1000000000000 := rfl
    have hx : (point 992+point 993)/2 = (3267395:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_992
  · change upperValue ((point (993)+point ((993)+1))/2) ≤ payment (993)
    have hp : payment 993 = (2092252673523:ℝ)/1000000000000 := rfl
    have hx : (point 993+point 994)/2 = (3269449:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_993
  · change upperValue ((point (994)+point ((994)+1))/2) ≤ payment (994)
    have hp : payment 994 = (2089583449278:ℝ)/1000000000000 := rfl
    have hx : (point 994+point 995)/2 = (1090501:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_994
  · change upperValue ((point (995)+point ((995)+1))/2) ≤ payment (995)
    have hp : payment 995 = (2086916692308:ℝ)/1000000000000 := rfl
    have hx : (point 995+point 996)/2 = (3273557:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_995
  · change upperValue ((point (996)+point ((996)+1))/2) ≤ payment (996)
    have hp : payment 996 = (2084252397311:ℝ)/1000000000000 := rfl
    have hx : (point 996+point 997)/2 = (3275611:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_996
  · change upperValue ((point (997)+point ((997)+1))/2) ≤ payment (997)
    have hp : payment 997 = (2081590558992:ℝ)/1000000000000 := rfl
    have hx : (point 997+point 998)/2 = (1092555:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_997
  · change upperValue ((point (998)+point ((998)+1))/2) ≤ payment (998)
    have hp : payment 998 = (2078931172074:ℝ)/1000000000000 := rfl
    have hx : (point 998+point 999)/2 = (3279719:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_998
  · change upperValue ((point (999)+point ((999)+1))/2) ≤ payment (999)
    have hp : payment 999 = (2076274231290:ℝ)/1000000000000 := rfl
    have hx : (point 999+point 1000)/2 = (3281773:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_999
  · change upperValue ((point (1000)+point ((1000)+1))/2) ≤ payment (1000)
    have hp : payment 1000 = (2073619731386:ℝ)/1000000000000 := rfl
    have hx : (point 1000+point 1001)/2 = (1094609:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1000
  · change upperValue ((point (1001)+point ((1001)+1))/2) ≤ payment (1001)
    have hp : payment 1001 = (2070967667120:ℝ)/1000000000000 := rfl
    have hx : (point 1001+point 1002)/2 = (3285881:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1001
  · change upperValue ((point (1002)+point ((1002)+1))/2) ≤ payment (1002)
    have hp : payment 1002 = (2068318033264:ℝ)/1000000000000 := rfl
    have hx : (point 1002+point 1003)/2 = (3287935:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1002
  · change upperValue ((point (1003)+point ((1003)+1))/2) ≤ payment (1003)
    have hp : payment 1003 = (2065670824600:ℝ)/1000000000000 := rfl
    have hx : (point 1003+point 1004)/2 = (1096663:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1003
  · change upperValue ((point (1004)+point ((1004)+1))/2) ≤ payment (1004)
    have hp : payment 1004 = (2063026035925:ℝ)/1000000000000 := rfl
    have hx : (point 1004+point 1005)/2 = (3292043:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1004
  · change upperValue ((point (1005)+point ((1005)+1))/2) ≤ payment (1005)
    have hp : payment 1005 = (2060383662047:ℝ)/1000000000000 := rfl
    have hx : (point 1005+point 1006)/2 = (3294097:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1005
  · change upperValue ((point (1006)+point ((1006)+1))/2) ≤ payment (1006)
    have hp : payment 1006 = (2057743697786:ℝ)/1000000000000 := rfl
    have hx : (point 1006+point 1007)/2 = (1098717:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1006
  · change upperValue ((point (1007)+point ((1007)+1))/2) ≤ payment (1007)
    have hp : payment 1007 = (2055106137975:ℝ)/1000000000000 := rfl
    have hx : (point 1007+point 1008)/2 = (3298205:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1007
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_062
