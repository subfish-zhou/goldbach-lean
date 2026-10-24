import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints003
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_003 (j : Fin 16) : upperValue ((point (16*3+j.val)+point ((16*3+j.val)+1))/2) ≤ payment (16*3+j.val) := by
  fin_cases j
  · change upperValue ((point (48)+point ((48)+1))/2) ≤ payment (48)
    have hp : payment 48 = (7521145283212:ℝ)/1000000000000 := rfl
    have hx : (point 48+point 49)/2 = (1328419:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_48
  · change upperValue ((point (49)+point ((49)+1))/2) ≤ payment (49)
    have hp : payment 49 = (7507691245384:ℝ)/1000000000000 := rfl
    have hx : (point 49+point 50)/2 = (443491:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_49
  · change upperValue ((point (50)+point ((50)+1))/2) ≤ payment (50)
    have hp : payment 50 = (7494277562040:ℝ)/1000000000000 := rfl
    have hx : (point 50+point 51)/2 = (1332527:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_50
  · change upperValue ((point (51)+point ((51)+1))/2) ≤ payment (51)
    have hp : payment 51 = (7480904046129:ℝ)/1000000000000 := rfl
    have hx : (point 51+point 52)/2 = (1334581:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_51
  · change upperValue ((point (52)+point ((52)+1))/2) ≤ payment (52)
    have hp : payment 52 = (7467570511749:ℝ)/1000000000000 := rfl
    have hx : (point 52+point 53)/2 = (445545:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_52
  · change upperValue ((point (53)+point ((53)+1))/2) ≤ payment (53)
    have hp : payment 53 = (7454276774139:ℝ)/1000000000000 := rfl
    have hx : (point 53+point 54)/2 = (1338689:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_53
  · change upperValue ((point (54)+point ((54)+1))/2) ≤ payment (54)
    have hp : payment 54 = (7441022649670:ℝ)/1000000000000 := rfl
    have hx : (point 54+point 55)/2 = (1340743:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_54
  · change upperValue ((point (55)+point ((55)+1))/2) ≤ payment (55)
    have hp : payment 55 = (7427807955834:ℝ)/1000000000000 := rfl
    have hx : (point 55+point 56)/2 = (447599:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_55
  · change upperValue ((point (56)+point ((56)+1))/2) ≤ payment (56)
    have hp : payment 56 = (7414632511240:ℝ)/1000000000000 := rfl
    have hx : (point 56+point 57)/2 = (1344851:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_56
  · change upperValue ((point (57)+point ((57)+1))/2) ≤ payment (57)
    have hp : payment 57 = (7401496135600:ℝ)/1000000000000 := rfl
    have hx : (point 57+point 58)/2 = (1015:ℝ)/12288 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_57
  · change upperValue ((point (58)+point ((58)+1))/2) ≤ payment (58)
    have hp : payment 58 = (7388398649727:ℝ)/1000000000000 := rfl
    have hx : (point 58+point 59)/2 = (449653:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_58
  · change upperValue ((point (59)+point ((59)+1))/2) ≤ payment (59)
    have hp : payment 59 = (7375339875520:ℝ)/1000000000000 := rfl
    have hx : (point 59+point 60)/2 = (1351013:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_59
  · change upperValue ((point (60)+point ((60)+1))/2) ≤ payment (60)
    have hp : payment 60 = (7362319635961:ℝ)/1000000000000 := rfl
    have hx : (point 60+point 61)/2 = (1353067:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_60
  · change upperValue ((point (61)+point ((61)+1))/2) ≤ payment (61)
    have hp : payment 61 = (7349337755103:ℝ)/1000000000000 := rfl
    have hx : (point 61+point 62)/2 = (451707:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_61
  · change upperValue ((point (62)+point ((62)+1))/2) ≤ payment (62)
    have hp : payment 62 = (7336394058065:ℝ)/1000000000000 := rfl
    have hx : (point 62+point 63)/2 = (1357175:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_62
  · change upperValue ((point (63)+point ((63)+1))/2) ≤ payment (63)
    have hp : payment 63 = (7323488371022:ℝ)/1000000000000 := rfl
    have hx : (point 63+point 64)/2 = (1359229:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_63
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_003
