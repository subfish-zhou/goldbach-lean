import WR2ClassicalEighthCorrectionPayments
import WR2ClassicalEighthCorrectionPoints009
noncomputable section
namespace WuPaper.ClassicalEighthCorrection
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_009 (j : Fin 16) : step*payment (16*9+j.val) ≤ cellPayment (point (16*9+j.val)) (point ((16*9+j.val)+1)) := by
  fin_cases j
  · change step*payment (144) ≤ cellPayment (point (144)) (point ((144)+1))
    have hp : payment 144 = (143176401203:ℝ)/1000000000000 := rfl
    have hl : point 144 = (34943:ℝ)/424640 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 145 = (111883:ℝ)/1358848 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_144
  · change step*payment (145) ≤ cellPayment (point (145)) (point ((145)+1))
    have hp : payment 145 = (142697416301:ℝ)/1000000000000 := rfl
    have hl : point 145 = (111883:ℝ)/1358848 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 146 = (279871:ℝ)/3397120 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_145
  · change step*payment (146) ≤ cellPayment (point (146)) (point ((146)+1))
    have hp : payment 146 = (142219019543:ℝ)/1000000000000 := rfl
    have hl : point 146 = (279871:ℝ)/3397120 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 147 = (560069:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_146
  · change step*payment (147) ≤ cellPayment (point (147)) (point ((147)+1))
    have hp : payment 147 = (141741209929:ℝ)/1000000000000 := rfl
    have hl : point 147 = (560069:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 148 = (140099:ℝ)/1698560 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_147
  · change step*payment (148) ≤ cellPayment (point (148)) (point ((148)+1))
    have hp : payment 148 = (141263986461:ℝ)/1000000000000 := rfl
    have hl : point 148 = (140099:ℝ)/1698560 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 149 = (560723:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_148
  · change step*payment (149) ≤ cellPayment (point (149)) (point ((149)+1))
    have hp : payment 149 = (140787348145:ℝ)/1000000000000 := rfl
    have hl : point 149 = (560723:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 150 = (56105:ℝ)/679424 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_149
  · change step*payment (150) ≤ cellPayment (point (150)) (point ((150)+1))
    have hp : payment 150 = (140311293986:ℝ)/1000000000000 := rfl
    have hl : point 150 = (56105:ℝ)/679424 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 151 = (561377:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_150
  · change step*payment (151) ≤ cellPayment (point (151)) (point ((151)+1))
    have hp : payment 151 = (139835822994:ℝ)/1000000000000 := rfl
    have hl : point 151 = (561377:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 152 = (70213:ℝ)/849280 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_151
  · change step*payment (152) ≤ cellPayment (point (152)) (point ((152)+1))
    have hp : payment 152 = (139360934180:ℝ)/1000000000000 := rfl
    have hl : point 152 = (70213:ℝ)/849280 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 153 = (562031:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_152
  · change step*payment (153) ≤ cellPayment (point (153)) (point ((153)+1))
    have hp : payment 153 = (138886626559:ℝ)/1000000000000 := rfl
    have hl : point 153 = (562031:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 154 = (281179:ℝ)/3397120 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_153
  · change step*payment (154) ≤ cellPayment (point (154)) (point ((154)+1))
    have hp : payment 154 = (138412899146:ℝ)/1000000000000 := rfl
    have hl : point 154 = (281179:ℝ)/3397120 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 155 = (112537:ℝ)/1358848 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_154
  · change step*payment (155) ≤ cellPayment (point (155)) (point ((155)+1))
    have hp : payment 155 = (137939750960:ℝ)/1000000000000 := rfl
    have hl : point 155 = (112537:ℝ)/1358848 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 156 = (140753:ℝ)/1698560 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_155
  · change step*payment (156) ≤ cellPayment (point (156)) (point ((156)+1))
    have hp : payment 156 = (137467181021:ℝ)/1000000000000 := rfl
    have hl : point 156 = (140753:ℝ)/1698560 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 157 = (563339:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_156
  · change step*payment (157) ≤ cellPayment (point (157)) (point ((157)+1))
    have hp : payment 157 = (136995188353:ℝ)/1000000000000 := rfl
    have hl : point 157 = (563339:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 158 = (281833:ℝ)/3397120 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_157
  · change step*payment (158) ≤ cellPayment (point (158)) (point ((158)+1))
    have hp : payment 158 = (136523771981:ℝ)/1000000000000 := rfl
    have hl : point 158 = (281833:ℝ)/3397120 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 159 = (563993:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_158
  · change step*payment (159) ≤ cellPayment (point (159)) (point ((159)+1))
    have hp : payment 159 = (136052930932:ℝ)/1000000000000 := rfl
    have hl : point 159 = (563993:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hr : point 160 = (3527:ℝ)/42464 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    have hs : step = (327:ℝ)/6794240 := by norm_num [point,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
    rw [hp,hl,hr,hs]
    exact point_paid_159
end WuPaper.ClassicalEighthCorrection
#print axioms WuPaper.ClassicalEighthCorrection.grid_block_009
