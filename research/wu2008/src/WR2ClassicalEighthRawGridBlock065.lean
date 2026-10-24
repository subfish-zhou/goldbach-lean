import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints065
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_065 (j : Fin 16) : upperValue ((point (16*65+j.val)+point ((16*65+j.val)+1))/2) ≤ payment (16*65+j.val) := by
  fin_cases j
  · change upperValue ((point (1040)+point ((1040)+1))/2) ≤ payment (1040)
    have hp : payment 1040 = (1969382448139:ℝ)/1000000000000 := rfl
    have hx : (point 1040+point 1041)/2 = (3365987:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1040
  · change upperValue ((point (1041)+point ((1041)+1))/2) ≤ payment (1041)
    have hp : payment 1041 = (1966823650322:ℝ)/1000000000000 := rfl
    have hx : (point 1041+point 1042)/2 = (3368041:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1041
  · change upperValue ((point (1042)+point ((1042)+1))/2) ≤ payment (1042)
    have hp : payment 1042 = (1964267083548:ℝ)/1000000000000 := rfl
    have hx : (point 1042+point 1043)/2 = (1123365:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1042
  · change upperValue ((point (1043)+point ((1043)+1))/2) ≤ payment (1043)
    have hp : payment 1043 = (1961712743065:ℝ)/1000000000000 := rfl
    have hx : (point 1043+point 1044)/2 = (3372149:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1043
  · change upperValue ((point (1044)+point ((1044)+1))/2) ≤ payment (1044)
    have hp : payment 1044 = (1959160624136:ℝ)/1000000000000 := rfl
    have hx : (point 1044+point 1045)/2 = (3374203:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1044
  · change upperValue ((point (1045)+point ((1045)+1))/2) ≤ payment (1045)
    have hp : payment 1045 = (1956610722031:ℝ)/1000000000000 := rfl
    have hx : (point 1045+point 1046)/2 = (1125419:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1045
  · change upperValue ((point (1046)+point ((1046)+1))/2) ≤ payment (1046)
    have hp : payment 1046 = (1954063032034:ℝ)/1000000000000 := rfl
    have hx : (point 1046+point 1047)/2 = (3378311:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1046
  · change upperValue ((point (1047)+point ((1047)+1))/2) ≤ payment (1047)
    have hp : payment 1047 = (1951517549439:ℝ)/1000000000000 := rfl
    have hx : (point 1047+point 1048)/2 = (3380365:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1047
  · change upperValue ((point (1048)+point ((1048)+1))/2) ≤ payment (1048)
    have hp : payment 1048 = (1948974269550:ℝ)/1000000000000 := rfl
    have hx : (point 1048+point 1049)/2 = (1127473:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1048
  · change upperValue ((point (1049)+point ((1049)+1))/2) ≤ payment (1049)
    have hp : payment 1049 = (1946433187681:ℝ)/1000000000000 := rfl
    have hx : (point 1049+point 1050)/2 = (3384473:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1049
  · change upperValue ((point (1050)+point ((1050)+1))/2) ≤ payment (1050)
    have hp : payment 1050 = (1943894299159:ℝ)/1000000000000 := rfl
    have hx : (point 1050+point 1051)/2 = (3386527:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1050
  · change upperValue ((point (1051)+point ((1051)+1))/2) ≤ payment (1051)
    have hp : payment 1051 = (1941357599321:ℝ)/1000000000000 := rfl
    have hx : (point 1051+point 1052)/2 = (1129527:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1051
  · change upperValue ((point (1052)+point ((1052)+1))/2) ≤ payment (1052)
    have hp : payment 1052 = (1938823083513:ℝ)/1000000000000 := rfl
    have hx : (point 1052+point 1053)/2 = (3390635:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1052
  · change upperValue ((point (1053)+point ((1053)+1))/2) ≤ payment (1053)
    have hp : payment 1053 = (1936290747094:ℝ)/1000000000000 := rfl
    have hx : (point 1053+point 1054)/2 = (3392689:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1053
  · change upperValue ((point (1054)+point ((1054)+1))/2) ≤ payment (1054)
    have hp : payment 1054 = (1933760585433:ℝ)/1000000000000 := rfl
    have hx : (point 1054+point 1055)/2 = (1131581:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1054
  · change upperValue ((point (1055)+point ((1055)+1))/2) ≤ payment (1055)
    have hp : payment 1055 = (1931232593907:ℝ)/1000000000000 := rfl
    have hx : (point 1055+point 1056)/2 = (3396797:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1055
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_065
