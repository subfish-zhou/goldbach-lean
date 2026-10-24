import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints007
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_007 (j : Fin 16) : upperValue ((point (16*7+j.val)+point ((16*7+j.val)+1))/2) ≤ payment (16*7+j.val) := by
  fin_cases j
  · change upperValue ((point (112)+point ((112)+1))/2) ≤ payment (112)
    have hp : payment 112 = (6734316739152:ℝ)/1000000000000 := rfl
    have hx : (point 112+point 113)/2 = (486625:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_112
  · change upperValue ((point (113)+point ((113)+1))/2) ≤ payment (113)
    have hp : payment 113 = (6723111130502:ℝ)/1000000000000 := rfl
    have hx : (point 113+point 114)/2 = (1461929:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_113
  · change upperValue ((point (114)+point ((114)+1))/2) ≤ payment (114)
    have hp : payment 114 = (6711935900096:ℝ)/1000000000000 := rfl
    have hx : (point 114+point 115)/2 = (1463983:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_114
  · change upperValue ((point (115)+point ((115)+1))/2) ≤ payment (115)
    have hp : payment 115 = (6700790919554:ℝ)/1000000000000 := rfl
    have hx : (point 115+point 116)/2 = (488679:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_115
  · change upperValue ((point (116)+point ((116)+1))/2) ≤ payment (116)
    have hp : payment 116 = (6689676061212:ℝ)/1000000000000 := rfl
    have hx : (point 116+point 117)/2 = (1468091:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_116
  · change upperValue ((point (117)+point ((117)+1))/2) ≤ payment (117)
    have hp : payment 117 = (6678591198120:ℝ)/1000000000000 := rfl
    have hx : (point 117+point 118)/2 = (1470145:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_117
  · change upperValue ((point (118)+point ((118)+1))/2) ≤ payment (118)
    have hp : payment 118 = (6667536204036:ℝ)/1000000000000 := rfl
    have hx : (point 118+point 119)/2 = (490733:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_118
  · change upperValue ((point (119)+point ((119)+1))/2) ≤ payment (119)
    have hp : payment 119 = (6656510953421:ℝ)/1000000000000 := rfl
    have hx : (point 119+point 120)/2 = (1474253:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_119
  · change upperValue ((point (120)+point ((120)+1))/2) ≤ payment (120)
    have hp : payment 120 = (6645515321434:ℝ)/1000000000000 := rfl
    have hx : (point 120+point 121)/2 = (1476307:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_120
  · change upperValue ((point (121)+point ((121)+1))/2) ≤ payment (121)
    have hp : payment 121 = (6634549183927:ℝ)/1000000000000 := rfl
    have hx : (point 121+point 122)/2 = (492787:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_121
  · change upperValue ((point (122)+point ((122)+1))/2) ≤ payment (122)
    have hp : payment 122 = (6623612417440:ℝ)/1000000000000 := rfl
    have hx : (point 122+point 123)/2 = (1480415:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_122
  · change upperValue ((point (123)+point ((123)+1))/2) ≤ payment (123)
    have hp : payment 123 = (6612704899199:ℝ)/1000000000000 := rfl
    have hx : (point 123+point 124)/2 = (1482469:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_123
  · change upperValue ((point (124)+point ((124)+1))/2) ≤ payment (124)
    have hp : payment 124 = (6601826507105:ℝ)/1000000000000 := rfl
    have hx : (point 124+point 125)/2 = (494841:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_124
  · change upperValue ((point (125)+point ((125)+1))/2) ≤ payment (125)
    have hp : payment 125 = (6590977119738:ℝ)/1000000000000 := rfl
    have hx : (point 125+point 126)/2 = (1486577:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_125
  · change upperValue ((point (126)+point ((126)+1))/2) ≤ payment (126)
    have hp : payment 126 = (6580156616343:ℝ)/1000000000000 := rfl
    have hx : (point 126+point 127)/2 = (1488631:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_126
  · change upperValue ((point (127)+point ((127)+1))/2) ≤ payment (127)
    have hp : payment 127 = (6569364876833:ℝ)/1000000000000 := rfl
    have hx : (point 127+point 128)/2 = (496895:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_127
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_007
