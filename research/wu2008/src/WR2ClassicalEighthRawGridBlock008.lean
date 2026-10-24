import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints008
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_008 (j : Fin 16) : upperValue ((point (16*8+j.val)+point ((16*8+j.val)+1))/2) ≤ payment (16*8+j.val) := by
  fin_cases j
  · change upperValue ((point (128)+point ((128)+1))/2) ≤ payment (128)
    have hp : payment 128 = (6558601781780:ℝ)/1000000000000 := rfl
    have hx : (point 128+point 129)/2 = (1492739:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_128
  · change upperValue ((point (129)+point ((129)+1))/2) ≤ payment (129)
    have hp : payment 129 = (6547867212413:ℝ)/1000000000000 := rfl
    have hx : (point 129+point 130)/2 = (1494793:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_129
  · change upperValue ((point (130)+point ((130)+1))/2) ≤ payment (130)
    have hp : payment 130 = (6537161050611:ℝ)/1000000000000 := rfl
    have hx : (point 130+point 131)/2 = (498949:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_130
  · change upperValue ((point (131)+point ((131)+1))/2) ≤ payment (131)
    have hp : payment 131 = (6526483178902:ℝ)/1000000000000 := rfl
    have hx : (point 131+point 132)/2 = (1498901:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_131
  · change upperValue ((point (132)+point ((132)+1))/2) ≤ payment (132)
    have hp : payment 132 = (6515833480454:ℝ)/1000000000000 := rfl
    have hx : (point 132+point 133)/2 = (1500955:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_132
  · change upperValue ((point (133)+point ((133)+1))/2) ≤ payment (133)
    have hp : payment 133 = (6505211839075:ℝ)/1000000000000 := rfl
    have hx : (point 133+point 134)/2 = (501003:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_133
  · change upperValue ((point (134)+point ((134)+1))/2) ≤ payment (134)
    have hp : payment 134 = (6494618139205:ℝ)/1000000000000 := rfl
    have hx : (point 134+point 135)/2 = (1505063:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_134
  · change upperValue ((point (135)+point ((135)+1))/2) ≤ payment (135)
    have hp : payment 135 = (6484052265915:ℝ)/1000000000000 := rfl
    have hx : (point 135+point 136)/2 = (1507117:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_135
  · change upperValue ((point (136)+point ((136)+1))/2) ≤ payment (136)
    have hp : payment 136 = (6473514104901:ℝ)/1000000000000 := rfl
    have hx : (point 136+point 137)/2 = (503057:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_136
  · change upperValue ((point (137)+point ((137)+1))/2) ≤ payment (137)
    have hp : payment 137 = (6463003542478:ℝ)/1000000000000 := rfl
    have hx : (point 137+point 138)/2 = (1511225:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_137
  · change upperValue ((point (138)+point ((138)+1))/2) ≤ payment (138)
    have hp : payment 138 = (6452520465581:ℝ)/1000000000000 := rfl
    have hx : (point 138+point 139)/2 = (1513279:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_138
  · change upperValue ((point (139)+point ((139)+1))/2) ≤ payment (139)
    have hp : payment 139 = (6442064761754:ℝ)/1000000000000 := rfl
    have hx : (point 139+point 140)/2 = (505111:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_139
  · change upperValue ((point (140)+point ((140)+1))/2) ≤ payment (140)
    have hp : payment 140 = (6431636319151:ℝ)/1000000000000 := rfl
    have hx : (point 140+point 141)/2 = (1517387:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_140
  · change upperValue ((point (141)+point ((141)+1))/2) ≤ payment (141)
    have hp : payment 141 = (6421235026531:ℝ)/1000000000000 := rfl
    have hx : (point 141+point 142)/2 = (1519441:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_141
  · change upperValue ((point (142)+point ((142)+1))/2) ≤ payment (142)
    have hp : payment 142 = (6410860773253:ℝ)/1000000000000 := rfl
    have hx : (point 142+point 143)/2 = (507165:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_142
  · change upperValue ((point (143)+point ((143)+1))/2) ≤ payment (143)
    have hp : payment 143 = (6400513449269:ℝ)/1000000000000 := rfl
    have hx : (point 143+point 144)/2 = (1523549:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_143
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_008
