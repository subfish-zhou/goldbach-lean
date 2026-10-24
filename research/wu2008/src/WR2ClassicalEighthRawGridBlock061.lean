import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints061
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_061 (j : Fin 16) : upperValue ((point (16*61+j.val)+point ((16*61+j.val)+1))/2) ≤ payment (16*61+j.val) := by
  fin_cases j
  · change upperValue ((point (976)+point ((976)+1))/2) ≤ payment (976)
    have hp : payment 976 = (2138012181214:ℝ)/1000000000000 := rfl
    have hx : (point 976+point 977)/2 = (1078177:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_976
  · change upperValue ((point (977)+point ((977)+1))/2) ≤ payment (977)
    have hp : payment 977 = (2135300189207:ℝ)/1000000000000 := rfl
    have hx : (point 977+point 978)/2 = (3236585:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_977
  · change upperValue ((point (978)+point ((978)+1))/2) ≤ payment (978)
    have hp : payment 978 = (2132590756633:ℝ)/1000000000000 := rfl
    have hx : (point 978+point 979)/2 = (3238639:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_978
  · change upperValue ((point (979)+point ((979)+1))/2) ≤ payment (979)
    have hp : payment 979 = (2129883877964:ℝ)/1000000000000 := rfl
    have hx : (point 979+point 980)/2 = (1080231:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_979
  · change upperValue ((point (980)+point ((980)+1))/2) ≤ payment (980)
    have hp : payment 980 = (2127179547687:ℝ)/1000000000000 := rfl
    have hx : (point 980+point 981)/2 = (3242747:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_980
  · change upperValue ((point (981)+point ((981)+1))/2) ≤ payment (981)
    have hp : payment 981 = (2124477760304:ℝ)/1000000000000 := rfl
    have hx : (point 981+point 982)/2 = (3244801:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_981
  · change upperValue ((point (982)+point ((982)+1))/2) ≤ payment (982)
    have hp : payment 982 = (2121778510327:ℝ)/1000000000000 := rfl
    have hx : (point 982+point 983)/2 = (1082285:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_982
  · change upperValue ((point (983)+point ((983)+1))/2) ≤ payment (983)
    have hp : payment 983 = (2119081792284:ℝ)/1000000000000 := rfl
    have hx : (point 983+point 984)/2 = (3248909:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_983
  · change upperValue ((point (984)+point ((984)+1))/2) ≤ payment (984)
    have hp : payment 984 = (2116387600714:ℝ)/1000000000000 := rfl
    have hx : (point 984+point 985)/2 = (3250963:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_984
  · change upperValue ((point (985)+point ((985)+1))/2) ≤ payment (985)
    have hp : payment 985 = (2113695930172:ℝ)/1000000000000 := rfl
    have hx : (point 985+point 986)/2 = (1084339:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_985
  · change upperValue ((point (986)+point ((986)+1))/2) ≤ payment (986)
    have hp : payment 986 = (2111006775223:ℝ)/1000000000000 := rfl
    have hx : (point 986+point 987)/2 = (3255071:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_986
  · change upperValue ((point (987)+point ((987)+1))/2) ≤ payment (987)
    have hp : payment 987 = (2108320130448:ℝ)/1000000000000 := rfl
    have hx : (point 987+point 988)/2 = (3257125:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_987
  · change upperValue ((point (988)+point ((988)+1))/2) ≤ payment (988)
    have hp : payment 988 = (2105635990438:ℝ)/1000000000000 := rfl
    have hx : (point 988+point 989)/2 = (1086393:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_988
  · change upperValue ((point (989)+point ((989)+1))/2) ≤ payment (989)
    have hp : payment 989 = (2102954349799:ℝ)/1000000000000 := rfl
    have hx : (point 989+point 990)/2 = (3261233:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_989
  · change upperValue ((point (990)+point ((990)+1))/2) ≤ payment (990)
    have hp : payment 990 = (2100275203150:ℝ)/1000000000000 := rfl
    have hx : (point 990+point 991)/2 = (3263287:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_990
  · change upperValue ((point (991)+point ((991)+1))/2) ≤ payment (991)
    have hp : payment 991 = (2097598545123:ℝ)/1000000000000 := rfl
    have hx : (point 991+point 992)/2 = (1088447:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_991
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_061
