import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints005
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_005 (j : Fin 16) : upperValue ((point (16*5+j.val)+point ((16*5+j.val)+1))/2) ≤ payment (16*5+j.val) := by
  fin_cases j
  · change upperValue ((point (80)+point ((80)+1))/2) ≤ payment (80)
    have hp : payment 80 = (7109743744442:ℝ)/1000000000000 := rfl
    have hx : (point 80+point 81)/2 = (1394147:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_80
  · change upperValue ((point (81)+point ((81)+1))/2) ≤ payment (81)
    have hp : payment 81 = (7097493671370:ℝ)/1000000000000 := rfl
    have hx : (point 81+point 82)/2 = (1396201:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_81
  · change upperValue ((point (82)+point ((82)+1))/2) ≤ payment (82)
    have hp : payment 82 = (7085278496169:ℝ)/1000000000000 := rfl
    have hx : (point 82+point 83)/2 = (466085:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_82
  · change upperValue ((point (83)+point ((83)+1))/2) ≤ payment (83)
    have hp : payment 83 = (7073098064564:ℝ)/1000000000000 := rfl
    have hx : (point 83+point 84)/2 = (1400309:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_83
  · change upperValue ((point (84)+point ((84)+1))/2) ≤ payment (84)
    have hp : payment 84 = (7060952223179:ℝ)/1000000000000 := rfl
    have hx : (point 84+point 85)/2 = (1402363:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_84
  · change upperValue ((point (85)+point ((85)+1))/2) ≤ payment (85)
    have hp : payment 85 = (7048840819539:ℝ)/1000000000000 := rfl
    have hx : (point 85+point 86)/2 = (468139:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_85
  · change upperValue ((point (86)+point ((86)+1))/2) ≤ payment (86)
    have hp : payment 86 = (7036763702056:ℝ)/1000000000000 := rfl
    have hx : (point 86+point 87)/2 = (1406471:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_86
  · change upperValue ((point (87)+point ((87)+1))/2) ≤ payment (87)
    have hp : payment 87 = (7024720720026:ℝ)/1000000000000 := rfl
    have hx : (point 87+point 88)/2 = (1408525:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_87
  · change upperValue ((point (88)+point ((88)+1))/2) ≤ payment (88)
    have hp : payment 88 = (7012711723625:ℝ)/1000000000000 := rfl
    have hx : (point 88+point 89)/2 = (470193:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_88
  · change upperValue ((point (89)+point ((89)+1))/2) ≤ payment (89)
    have hp : payment 89 = (7000736563896:ℝ)/1000000000000 := rfl
    have hx : (point 89+point 90)/2 = (1412633:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_89
  · change upperValue ((point (90)+point ((90)+1))/2) ≤ payment (90)
    have hp : payment 90 = (6988795092748:ℝ)/1000000000000 := rfl
    have hx : (point 90+point 91)/2 = (1414687:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_90
  · change upperValue ((point (91)+point ((91)+1))/2) ≤ payment (91)
    have hp : payment 91 = (6976887162950:ℝ)/1000000000000 := rfl
    have hx : (point 91+point 92)/2 = (472247:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_91
  · change upperValue ((point (92)+point ((92)+1))/2) ≤ payment (92)
    have hp : payment 92 = (6965012628121:ℝ)/1000000000000 := rfl
    have hx : (point 92+point 93)/2 = (1418795:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_92
  · change upperValue ((point (93)+point ((93)+1))/2) ≤ payment (93)
    have hp : payment 93 = (6953171342726:ℝ)/1000000000000 := rfl
    have hx : (point 93+point 94)/2 = (1420849:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_93
  · change upperValue ((point (94)+point ((94)+1))/2) ≤ payment (94)
    have hp : payment 94 = (6941363162070:ℝ)/1000000000000 := rfl
    have hx : (point 94+point 95)/2 = (474301:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_94
  · change upperValue ((point (95)+point ((95)+1))/2) ≤ payment (95)
    have hp : payment 95 = (6929587942293:ℝ)/1000000000000 := rfl
    have hx : (point 95+point 96)/2 = (1424957:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_95
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_005
