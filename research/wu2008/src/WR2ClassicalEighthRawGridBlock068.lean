import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints068
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_068 (j : Fin 16) : upperValue ((point (16*68+j.val)+point ((16*68+j.val)+1))/2) ≤ payment (16*68+j.val) := by
  fin_cases j
  · change upperValue ((point (1088)+point ((1088)+1))/2) ≤ payment (1088)
    have hp : payment 1088 = (1848996684335:ℝ)/1000000000000 := rfl
    have hx : (point 1088+point 1089)/2 = (3464579:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1088
  · change upperValue ((point (1089)+point ((1089)+1))/2) ≤ payment (1089)
    have hp : payment 1089 = (1846539801314:ℝ)/1000000000000 := rfl
    have hx : (point 1089+point 1090)/2 = (3466633:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1089
  · change upperValue ((point (1090)+point ((1090)+1))/2) ≤ payment (1090)
    have hp : payment 1090 = (1844084933107:ℝ)/1000000000000 := rfl
    have hx : (point 1090+point 1091)/2 = (1156229:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1090
  · change upperValue ((point (1091)+point ((1091)+1))/2) ≤ payment (1091)
    have hp : payment 1091 = (1841632075452:ℝ)/1000000000000 := rfl
    have hx : (point 1091+point 1092)/2 = (3470741:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1091
  · change upperValue ((point (1092)+point ((1092)+1))/2) ≤ payment (1092)
    have hp : payment 1092 = (1839181224097:ℝ)/1000000000000 := rfl
    have hx : (point 1092+point 1093)/2 = (3472795:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1092
  · change upperValue ((point (1093)+point ((1093)+1))/2) ≤ payment (1093)
    have hp : payment 1093 = (1836732374800:ℝ)/1000000000000 := rfl
    have hx : (point 1093+point 1094)/2 = (1158283:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1093
  · change upperValue ((point (1094)+point ((1094)+1))/2) ≤ payment (1094)
    have hp : payment 1094 = (1834285523326:ℝ)/1000000000000 := rfl
    have hx : (point 1094+point 1095)/2 = (3476903:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1094
  · change upperValue ((point (1095)+point ((1095)+1))/2) ≤ payment (1095)
    have hp : payment 1095 = (1831840665453:ℝ)/1000000000000 := rfl
    have hx : (point 1095+point 1096)/2 = (3478957:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1095
  · change upperValue ((point (1096)+point ((1096)+1))/2) ≤ payment (1096)
    have hp : payment 1096 = (1829397796966:ℝ)/1000000000000 := rfl
    have hx : (point 1096+point 1097)/2 = (1160337:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1096
  · change upperValue ((point (1097)+point ((1097)+1))/2) ≤ payment (1097)
    have hp : payment 1097 = (1826956913660:ℝ)/1000000000000 := rfl
    have hx : (point 1097+point 1098)/2 = (3483065:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1097
  · change upperValue ((point (1098)+point ((1098)+1))/2) ≤ payment (1098)
    have hp : payment 1098 = (1824518011338:ℝ)/1000000000000 := rfl
    have hx : (point 1098+point 1099)/2 = (3485119:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1098
  · change upperValue ((point (1099)+point ((1099)+1))/2) ≤ payment (1099)
    have hp : payment 1099 = (1822081085813:ℝ)/1000000000000 := rfl
    have hx : (point 1099+point 1100)/2 = (1162391:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1099
  · change upperValue ((point (1100)+point ((1100)+1))/2) ≤ payment (1100)
    have hp : payment 1100 = (1819646132909:ℝ)/1000000000000 := rfl
    have hx : (point 1100+point 1101)/2 = (3489227:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1100
  · change upperValue ((point (1101)+point ((1101)+1))/2) ≤ payment (1101)
    have hp : payment 1101 = (1817213148456:ℝ)/1000000000000 := rfl
    have hx : (point 1101+point 1102)/2 = (3491281:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1101
  · change upperValue ((point (1102)+point ((1102)+1))/2) ≤ payment (1102)
    have hp : payment 1102 = (1814782128296:ℝ)/1000000000000 := rfl
    have hx : (point 1102+point 1103)/2 = (1164445:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1102
  · change upperValue ((point (1103)+point ((1103)+1))/2) ≤ payment (1103)
    have hp : payment 1103 = (1812353068278:ℝ)/1000000000000 := rfl
    have hx : (point 1103+point 1104)/2 = (3495389:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1103
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_068
