import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints073
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_073 (j : Fin 16) : lowerPayment (16*73+j.val) ≤
    lowerValue ((point 2 split 4096 (16*73+j.val)+point 2 split 4096 (16*73+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1168 ≤ lowerValue ((point 2 split 4096 1168+point 2 split 4096 1169)/2)
    have hp : lowerPayment 1168 = (151647332820:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1168+point 2 split 4096 1169)/2 = (405589547:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((405589547:ℝ)/168755200)/ClassicalSixthBranch.v ((405589547:ℝ)/168755200) = (144734829727:ℝ)/72896248504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1168
  · change lowerPayment 1169 ≤ lowerValue ((point 2 split 4096 1169+point 2 split 4096 1170)/2)
    have hp : lowerPayment 1169 = (151753484159:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1169+point 2 split 4096 1170)/2 = (405647809:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((405647809:ℝ)/168755200)/ClassicalSixthBranch.v ((405647809:ℝ)/168755200) = (723596834961:ℝ)/364433234632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1169
  · change lowerPayment 1170 ≤ lowerValue ((point 2 split 4096 1170+point 2 split 4096 1171)/2)
    have hp : lowerPayment 1170 = (151859608121:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1170+point 2 split 4096 1171)/2 = (405706071:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((405706071:ℝ)/168755200)/ClassicalSixthBranch.v ((405706071:ℝ)/168755200) = (723519521287:ℝ)/364385226744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1170
  · change lowerPayment 1171 ≤ lowerValue ((point 2 split 4096 1171+point 2 split 4096 1172)/2)
    have hp : lowerPayment 1171 = (151965704733:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1171+point 2 split 4096 1172)/2 = (405764333:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((405764333:ℝ)/168755200)/ClassicalSixthBranch.v ((405764333:ℝ)/168755200) = (723442207613:ℝ)/364337218856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1171
  · change lowerPayment 1172 ≤ lowerValue ((point 2 split 4096 1172+point 2 split 4096 1173)/2)
    have hp : lowerPayment 1172 = (152071774022:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1172+point 2 split 4096 1173)/2 = (81164519:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((81164519:ℝ)/33751040)/ClassicalSixthBranch.v ((81164519:ℝ)/33751040) = (723364893939:ℝ)/364289210968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1172
  · change lowerPayment 1173 ≤ lowerValue ((point 2 split 4096 1173+point 2 split 4096 1174)/2)
    have hp : lowerPayment 1173 = (152177816012:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1173+point 2 split 4096 1174)/2 = (405880857:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((405880857:ℝ)/168755200)/ClassicalSixthBranch.v ((405880857:ℝ)/168755200) = (144657516053:ℝ)/72848240616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1173
  · change lowerPayment 1174 ≤ lowerValue ((point 2 split 4096 1174+point 2 split 4096 1175)/2)
    have hp : lowerPayment 1174 = (152283830730:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1174+point 2 split 4096 1175)/2 = (405939119:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((405939119:ℝ)/168755200)/ClassicalSixthBranch.v ((405939119:ℝ)/168755200) = (723210266591:ℝ)/364193195192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1174
  · change lowerPayment 1175 ≤ lowerValue ((point 2 split 4096 1175+point 2 split 4096 1176)/2)
    have hp : lowerPayment 1175 = (152389818203:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1175+point 2 split 4096 1176)/2 = (405997381:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((405997381:ℝ)/168755200)/ClassicalSixthBranch.v ((405997381:ℝ)/168755200) = (723132952917:ℝ)/364145187304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1175
  · change lowerPayment 1176 ≤ lowerValue ((point 2 split 4096 1176+point 2 split 4096 1177)/2)
    have hp : lowerPayment 1176 = (152495778457:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1176+point 2 split 4096 1177)/2 = (406055643:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((406055643:ℝ)/168755200)/ClassicalSixthBranch.v ((406055643:ℝ)/168755200) = (723055639243:ℝ)/364097179416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1176
  · change lowerPayment 1177 ≤ lowerValue ((point 2 split 4096 1177+point 2 split 4096 1178)/2)
    have hp : lowerPayment 1177 = (152601711517:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1177+point 2 split 4096 1178)/2 = (81222781:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((81222781:ℝ)/33751040)/ClassicalSixthBranch.v ((81222781:ℝ)/33751040) = (722978325569:ℝ)/364049171528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1177
  · change lowerPayment 1178 ≤ lowerValue ((point 2 split 4096 1178+point 2 split 4096 1179)/2)
    have hp : lowerPayment 1178 = (152707617411:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1178+point 2 split 4096 1179)/2 = (406172167:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((406172167:ℝ)/168755200)/ClassicalSixthBranch.v ((406172167:ℝ)/168755200) = (144580202379:ℝ)/72800232728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1178
  · change lowerPayment 1179 ≤ lowerValue ((point 2 split 4096 1179+point 2 split 4096 1180)/2)
    have hp : lowerPayment 1179 = (152813496163:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1179+point 2 split 4096 1180)/2 = (406230429:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((406230429:ℝ)/168755200)/ClassicalSixthBranch.v ((406230429:ℝ)/168755200) = (722823698221:ℝ)/363953155752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1179
  · change lowerPayment 1180 ≤ lowerValue ((point 2 split 4096 1180+point 2 split 4096 1181)/2)
    have hp : lowerPayment 1180 = (152919347801:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1180+point 2 split 4096 1181)/2 = (406288691:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((406288691:ℝ)/168755200)/ClassicalSixthBranch.v ((406288691:ℝ)/168755200) = (722746384547:ℝ)/363905147864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1180
  · change lowerPayment 1181 ≤ lowerValue ((point 2 split 4096 1181+point 2 split 4096 1182)/2)
    have hp : lowerPayment 1181 = (153025172349:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1181+point 2 split 4096 1182)/2 = (406346953:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((406346953:ℝ)/168755200)/ClassicalSixthBranch.v ((406346953:ℝ)/168755200) = (722669070873:ℝ)/363857139976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1181
  · change lowerPayment 1182 ≤ lowerValue ((point 2 split 4096 1182+point 2 split 4096 1183)/2)
    have hp : lowerPayment 1182 = (153130969835:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1182+point 2 split 4096 1183)/2 = (81281043:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((81281043:ℝ)/33751040)/ClassicalSixthBranch.v ((81281043:ℝ)/33751040) = (722591757199:ℝ)/363809132088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1182
  · change lowerPayment 1183 ≤ lowerValue ((point 2 split 4096 1183+point 2 split 4096 1184)/2)
    have hp : lowerPayment 1183 = (153236740284:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1183+point 2 split 4096 1184)/2 = (406463477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((406463477:ℝ)/168755200)/ClassicalSixthBranch.v ((406463477:ℝ)/168755200) = (28900577741:ℝ)/14550444968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1183
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_073
