import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints072
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_072 (j : Fin 16) : lowerPayment (16*72+j.val) ≤
    lowerValue ((point 2 split 4096 (16*72+j.val)+point 2 split 4096 (16*72+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1152 ≤ lowerValue ((point 2 split 4096 1152+point 2 split 4096 1153)/2)
    have hp : lowerPayment 1152 = (149945166697:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1152+point 2 split 4096 1153)/2 = (80931471:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((80931471:ℝ)/33751040)/ClassicalSixthBranch.v ((80931471:ℝ)/33751040) = (724911167419:ℝ)/365249368728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1152
  · change lowerPayment 1153 ≤ lowerValue ((point 2 split 4096 1153+point 2 split 4096 1154)/2)
    have hp : lowerPayment 1153 = (150051759645:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1153+point 2 split 4096 1154)/2 = (404715617:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((404715617:ℝ)/168755200)/ClassicalSixthBranch.v ((404715617:ℝ)/168755200) = (144966770749:ℝ)/73040272168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1153
  · change lowerPayment 1154 ≤ lowerValue ((point 2 split 4096 1154+point 2 split 4096 1155)/2)
    have hp : lowerPayment 1154 = (150158324794:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1154+point 2 split 4096 1155)/2 = (404773879:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((404773879:ℝ)/168755200)/ClassicalSixthBranch.v ((404773879:ℝ)/168755200) = (724756540071:ℝ)/365153352952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1154
  · change lowerPayment 1155 ≤ lowerValue ((point 2 split 4096 1155+point 2 split 4096 1156)/2)
    have hp : lowerPayment 1155 = (150264862171:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1155+point 2 split 4096 1156)/2 = (404832141:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((404832141:ℝ)/168755200)/ClassicalSixthBranch.v ((404832141:ℝ)/168755200) = (724679226397:ℝ)/365105345064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1155
  · change lowerPayment 1156 ≤ lowerValue ((point 2 split 4096 1156+point 2 split 4096 1157)/2)
    have hp : lowerPayment 1156 = (150371371802:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1156+point 2 split 4096 1157)/2 = (404890403:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((404890403:ℝ)/168755200)/ClassicalSixthBranch.v ((404890403:ℝ)/168755200) = (724601912723:ℝ)/365057337176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1156
  · change lowerPayment 1157 ≤ lowerValue ((point 2 split 4096 1157+point 2 split 4096 1158)/2)
    have hp : lowerPayment 1157 = (150477853713:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1157+point 2 split 4096 1158)/2 = (80989733:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((80989733:ℝ)/33751040)/ClassicalSixthBranch.v ((80989733:ℝ)/33751040) = (724524599049:ℝ)/365009329288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1157
  · change lowerPayment 1158 ≤ lowerValue ((point 2 split 4096 1158+point 2 split 4096 1159)/2)
    have hp : lowerPayment 1158 = (150584307932:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1158+point 2 split 4096 1159)/2 = (405006927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((405006927:ℝ)/168755200)/ClassicalSixthBranch.v ((405006927:ℝ)/168755200) = (28977891415:ℝ)/14598452856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1158
  · change lowerPayment 1159 ≤ lowerValue ((point 2 split 4096 1159+point 2 split 4096 1160)/2)
    have hp : lowerPayment 1159 = (150690734484:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1159+point 2 split 4096 1160)/2 = (405065189:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((405065189:ℝ)/168755200)/ClassicalSixthBranch.v ((405065189:ℝ)/168755200) = (724369971701:ℝ)/364913313512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1159
  · change lowerPayment 1160 ≤ lowerValue ((point 2 split 4096 1160+point 2 split 4096 1161)/2)
    have hp : lowerPayment 1160 = (150797133396:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1160+point 2 split 4096 1161)/2 = (405123451:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((405123451:ℝ)/168755200)/ClassicalSixthBranch.v ((405123451:ℝ)/168755200) = (724292658027:ℝ)/364865305624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1160
  · change lowerPayment 1161 ≤ lowerValue ((point 2 split 4096 1161+point 2 split 4096 1162)/2)
    have hp : lowerPayment 1161 = (150903504694:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1161+point 2 split 4096 1162)/2 = (405181713:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((405181713:ℝ)/168755200)/ClassicalSixthBranch.v ((405181713:ℝ)/168755200) = (724215344353:ℝ)/364817297736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1161
  · change lowerPayment 1162 ≤ lowerValue ((point 2 split 4096 1162+point 2 split 4096 1163)/2)
    have hp : lowerPayment 1162 = (151009848406:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1162+point 2 split 4096 1163)/2 = (16209599:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((16209599:ℝ)/6750208)/ClassicalSixthBranch.v ((16209599:ℝ)/6750208) = (724138030679:ℝ)/364769289848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1162
  · change lowerPayment 1163 ≤ lowerValue ((point 2 split 4096 1163+point 2 split 4096 1164)/2)
    have hp : lowerPayment 1163 = (151116164556:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1163+point 2 split 4096 1164)/2 = (405298237:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((405298237:ℝ)/168755200)/ClassicalSixthBranch.v ((405298237:ℝ)/168755200) = (144812143401:ℝ)/72944256392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1163
  · change lowerPayment 1164 ≤ lowerValue ((point 2 split 4096 1164+point 2 split 4096 1165)/2)
    have hp : lowerPayment 1164 = (151222453172:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1164+point 2 split 4096 1165)/2 = (405356499:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((405356499:ℝ)/168755200)/ClassicalSixthBranch.v ((405356499:ℝ)/168755200) = (723983403331:ℝ)/364673274072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1164
  · change lowerPayment 1165 ≤ lowerValue ((point 2 split 4096 1165+point 2 split 4096 1166)/2)
    have hp : lowerPayment 1165 = (151328714281:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1165+point 2 split 4096 1166)/2 = (405414761:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((405414761:ℝ)/168755200)/ClassicalSixthBranch.v ((405414761:ℝ)/168755200) = (723906089657:ℝ)/364625266184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1165
  · change lowerPayment 1166 ≤ lowerValue ((point 2 split 4096 1166+point 2 split 4096 1167)/2)
    have hp : lowerPayment 1166 = (151434947907:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1166+point 2 split 4096 1167)/2 = (405473023:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((405473023:ℝ)/168755200)/ClassicalSixthBranch.v ((405473023:ℝ)/168755200) = (723828775983:ℝ)/364577258296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1166
  · change lowerPayment 1167 ≤ lowerValue ((point 2 split 4096 1167+point 2 split 4096 1168)/2)
    have hp : lowerPayment 1167 = (151541154078:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1167+point 2 split 4096 1168)/2 = (81106257:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((81106257:ℝ)/33751040)/ClassicalSixthBranch.v ((81106257:ℝ)/33751040) = (723751462309:ℝ)/364529250408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1167
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_072
