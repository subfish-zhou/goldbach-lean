import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints069
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_069 (j : Fin 16) : upperValue ((point (16*69+j.val)+point ((16*69+j.val)+1))/2) ≤ payment (16*69+j.val) := by
  fin_cases j
  · change upperValue ((point (1104)+point ((1104)+1))/2) ≤ payment (1104)
    have hp : payment 1104 = (1809925964262:ℝ)/1000000000000 := rfl
    have hx : (point 1104+point 1105)/2 = (3497443:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1104
  · change upperValue ((point (1105)+point ((1105)+1))/2) ≤ payment (1105)
    have hp : payment 1105 = (1807500812114:ℝ)/1000000000000 := rfl
    have hx : (point 1105+point 1106)/2 = (1166499:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1105
  · change upperValue ((point (1106)+point ((1106)+1))/2) ≤ payment (1106)
    have hp : payment 1106 = (1805077607714:ℝ)/1000000000000 := rfl
    have hx : (point 1106+point 1107)/2 = (3501551:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1106
  · change upperValue ((point (1107)+point ((1107)+1))/2) ≤ payment (1107)
    have hp : payment 1107 = (1802656346945:ℝ)/1000000000000 := rfl
    have hx : (point 1107+point 1108)/2 = (3503605:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1107
  · change upperValue ((point (1108)+point ((1108)+1))/2) ≤ payment (1108)
    have hp : payment 1108 = (1800237025704:ℝ)/1000000000000 := rfl
    have hx : (point 1108+point 1109)/2 = (1168553:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1108
  · change upperValue ((point (1109)+point ((1109)+1))/2) ≤ payment (1109)
    have hp : payment 1109 = (1797819639895:ℝ)/1000000000000 := rfl
    have hx : (point 1109+point 1110)/2 = (3507713:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1109
  · change upperValue ((point (1110)+point ((1110)+1))/2) ≤ payment (1110)
    have hp : payment 1110 = (1795404185431:ℝ)/1000000000000 := rfl
    have hx : (point 1110+point 1111)/2 = (3509767:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1110
  · change upperValue ((point (1111)+point ((1111)+1))/2) ≤ payment (1111)
    have hp : payment 1111 = (1792990658232:ℝ)/1000000000000 := rfl
    have hx : (point 1111+point 1112)/2 = (1170607:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1111
  · change upperValue ((point (1112)+point ((1112)+1))/2) ≤ payment (1112)
    have hp : payment 1112 = (1790579054231:ℝ)/1000000000000 := rfl
    have hx : (point 1112+point 1113)/2 = (3513875:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1112
  · change upperValue ((point (1113)+point ((1113)+1))/2) ≤ payment (1113)
    have hp : payment 1113 = (1788169369367:ℝ)/1000000000000 := rfl
    have hx : (point 1113+point 1114)/2 = (3515929:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1113
  · change upperValue ((point (1114)+point ((1114)+1))/2) ≤ payment (1114)
    have hp : payment 1114 = (1785761599587:ℝ)/1000000000000 := rfl
    have hx : (point 1114+point 1115)/2 = (1172661:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1114
  · change upperValue ((point (1115)+point ((1115)+1))/2) ≤ payment (1115)
    have hp : payment 1115 = (1783355740850:ℝ)/1000000000000 := rfl
    have hx : (point 1115+point 1116)/2 = (3520037:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1115
  · change upperValue ((point (1116)+point ((1116)+1))/2) ≤ payment (1116)
    have hp : payment 1116 = (1780951789122:ℝ)/1000000000000 := rfl
    have hx : (point 1116+point 1117)/2 = (3522091:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1116
  · change upperValue ((point (1117)+point ((1117)+1))/2) ≤ payment (1117)
    have hp : payment 1117 = (1778549740376:ℝ)/1000000000000 := rfl
    have hx : (point 1117+point 1118)/2 = (1174715:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1117
  · change upperValue ((point (1118)+point ((1118)+1))/2) ≤ payment (1118)
    have hp : payment 1118 = (1776149590597:ℝ)/1000000000000 := rfl
    have hx : (point 1118+point 1119)/2 = (3526199:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1118
  · change upperValue ((point (1119)+point ((1119)+1))/2) ≤ payment (1119)
    have hp : payment 1119 = (1773751335777:ℝ)/1000000000000 := rfl
    have hx : (point 1119+point 1120)/2 = (3528253:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1119
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_069
