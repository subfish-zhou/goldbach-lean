import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints004
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_004 (j : Fin 16) : upperValue ((point (16*4+j.val)+point ((16*4+j.val)+1))/2) ≤ payment (16*4+j.val) := by
  fin_cases j
  · change upperValue ((point (64)+point ((64)+1))/2) ≤ payment (64)
    have hp : payment 64 = (7310620521196:ℝ)/1000000000000 := rfl
    have hx : (point 64+point 65)/2 = (453761:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_64
  · change upperValue ((point (65)+point ((65)+1))/2) ≤ payment (65)
    have hp : payment 65 = (7297790336853:ℝ)/1000000000000 := rfl
    have hx : (point 65+point 66)/2 = (1363337:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_65
  · change upperValue ((point (66)+point ((66)+1))/2) ≤ payment (66)
    have hp : payment 66 = (7284997647290:ℝ)/1000000000000 := rfl
    have hx : (point 66+point 67)/2 = (1365391:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_66
  · change upperValue ((point (67)+point ((67)+1))/2) ≤ payment (67)
    have hp : payment 67 = (7272242282827:ℝ)/1000000000000 := rfl
    have hx : (point 67+point 68)/2 = (455815:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_67
  · change upperValue ((point (68)+point ((68)+1))/2) ≤ payment (68)
    have hp : payment 68 = (7259524074805:ℝ)/1000000000000 := rfl
    have hx : (point 68+point 69)/2 = (1369499:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_68
  · change upperValue ((point (69)+point ((69)+1))/2) ≤ payment (69)
    have hp : payment 69 = (7246842855573:ℝ)/1000000000000 := rfl
    have hx : (point 69+point 70)/2 = (1371553:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_69
  · change upperValue ((point (70)+point ((70)+1))/2) ≤ payment (70)
    have hp : payment 70 = (7234198458483:ℝ)/1000000000000 := rfl
    have hx : (point 70+point 71)/2 = (457869:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_70
  · change upperValue ((point (71)+point ((71)+1))/2) ≤ payment (71)
    have hp : payment 71 = (7221590717879:ℝ)/1000000000000 := rfl
    have hx : (point 71+point 72)/2 = (1375661:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_71
  · change upperValue ((point (72)+point ((72)+1))/2) ≤ payment (72)
    have hp : payment 72 = (7209019469096:ℝ)/1000000000000 := rfl
    have hx : (point 72+point 73)/2 = (1377715:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_72
  · change upperValue ((point (73)+point ((73)+1))/2) ≤ payment (73)
    have hp : payment 73 = (7196484548448:ℝ)/1000000000000 := rfl
    have hx : (point 73+point 74)/2 = (459923:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_73
  · change upperValue ((point (74)+point ((74)+1))/2) ≤ payment (74)
    have hp : payment 74 = (7183985793219:ℝ)/1000000000000 := rfl
    have hx : (point 74+point 75)/2 = (1381823:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_74
  · change upperValue ((point (75)+point ((75)+1))/2) ≤ payment (75)
    have hp : payment 75 = (7171523041662:ℝ)/1000000000000 := rfl
    have hx : (point 75+point 76)/2 = (1383877:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_75
  · change upperValue ((point (76)+point ((76)+1))/2) ≤ payment (76)
    have hp : payment 76 = (7159096132987:ℝ)/1000000000000 := rfl
    have hx : (point 76+point 77)/2 = (461977:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_76
  · change upperValue ((point (77)+point ((77)+1))/2) ≤ payment (77)
    have hp : payment 77 = (7146704907354:ℝ)/1000000000000 := rfl
    have hx : (point 77+point 78)/2 = (1387985:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_77
  · change upperValue ((point (78)+point ((78)+1))/2) ≤ payment (78)
    have hp : payment 78 = (7134349205869:ℝ)/1000000000000 := rfl
    have hx : (point 78+point 79)/2 = (1390039:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_78
  · change upperValue ((point (79)+point ((79)+1))/2) ≤ payment (79)
    have hp : payment 79 = (7122028870574:ℝ)/1000000000000 := rfl
    have hx : (point 79+point 80)/2 = (464031:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_79
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_004
