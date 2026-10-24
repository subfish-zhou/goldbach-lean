import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints072
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_072 (j : Fin 16) : upperPayment (16*72+j.val) ≤
    upperValue ((point split endpoint 4096 (16*72+j.val)+point split endpoint 4096 (16*72+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1152 ≤ upperValue ((point split endpoint 4096 1152+point split endpoint 4096 1153)/2)
    have hp : upperPayment 1152 = (348587915505:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1152+point split endpoint 4096 1153)/2 = (605136927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605136927:ℝ)/168755200)*ClassicalSixthBranch.v ((605136927:ℝ)/168755200)/ClassicalSixthBranch.r = (134327121882705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1152
  · change upperPayment 1153 ≤ upperValue ((point split endpoint 4096 1153+point split endpoint 4096 1154)/2)
    have hp : upperPayment 1153 = (348509946014:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1153+point split endpoint 4096 1154)/2 = (605162077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605162077:ℝ)/168755200)*ClassicalSixthBranch.v ((605162077:ℝ)/168755200)/ClassicalSixthBranch.r = (134303438320857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1153
  · change upperPayment 1154 ≤ upperValue ((point split endpoint 4096 1154+point split endpoint 4096 1155)/2)
    have hp : upperPayment 1154 = (348431954006:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1154+point split endpoint 4096 1155)/2 = (605187227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605187227:ℝ)/168755200)*ClassicalSixthBranch.v ((605187227:ℝ)/168755200)/ClassicalSixthBranch.r = (134279756783081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1154
  · change upperPayment 1155 ≤ upperValue ((point split endpoint 4096 1155+point split endpoint 4096 1156)/2)
    have hp : upperPayment 1155 = (348353939478:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1155+point split endpoint 4096 1156)/2 = (605212377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605212377:ℝ)/168755200)*ClassicalSixthBranch.v ((605212377:ℝ)/168755200)/ClassicalSixthBranch.r = (134256077269377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1155
  · change upperPayment 1156 ≤ upperValue ((point split endpoint 4096 1156+point split endpoint 4096 1157)/2)
    have hp : upperPayment 1156 = (348275902426:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1156+point split endpoint 4096 1157)/2 = (605237527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605237527:ℝ)/168755200)*ClassicalSixthBranch.v ((605237527:ℝ)/168755200)/ClassicalSixthBranch.r = (134232399779745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1156
  · change upperPayment 1157 ≤ upperValue ((point split endpoint 4096 1157+point split endpoint 4096 1158)/2)
    have hp : upperPayment 1157 = (348197842847:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1157+point split endpoint 4096 1158)/2 = (605262677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605262677:ℝ)/168755200)*ClassicalSixthBranch.v ((605262677:ℝ)/168755200)/ClassicalSixthBranch.r = (134208724314185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1157
  · change upperPayment 1158 ≤ upperValue ((point split endpoint 4096 1158+point split endpoint 4096 1159)/2)
    have hp : upperPayment 1158 = (348119760737:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1158+point split endpoint 4096 1159)/2 = (605287827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605287827:ℝ)/168755200)*ClassicalSixthBranch.v ((605287827:ℝ)/168755200)/ClassicalSixthBranch.r = (134185050872697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1158
  · change upperPayment 1159 ≤ upperValue ((point split endpoint 4096 1159+point split endpoint 4096 1160)/2)
    have hp : upperPayment 1159 = (348041656093:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1159+point split endpoint 4096 1160)/2 = (605312977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605312977:ℝ)/168755200)*ClassicalSixthBranch.v ((605312977:ℝ)/168755200)/ClassicalSixthBranch.r = (134161379455281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1159
  · change upperPayment 1160 ≤ upperValue ((point split endpoint 4096 1160+point split endpoint 4096 1161)/2)
    have hp : upperPayment 1160 = (347963528910:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1160+point split endpoint 4096 1161)/2 = (605338127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605338127:ℝ)/168755200)*ClassicalSixthBranch.v ((605338127:ℝ)/168755200)/ClassicalSixthBranch.r = (1302307864679:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1160
  · change upperPayment 1161 ≤ upperValue ((point split endpoint 4096 1161+point split endpoint 4096 1162)/2)
    have hp : upperPayment 1161 = (347885379185:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1161+point split endpoint 4096 1162)/2 = (605363277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605363277:ℝ)/168755200)*ClassicalSixthBranch.v ((605363277:ℝ)/168755200)/ClassicalSixthBranch.r = (134114042692665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1161
  · change upperPayment 1162 ≤ upperValue ((point split endpoint 4096 1162+point split endpoint 4096 1163)/2)
    have hp : upperPayment 1162 = (347807206914:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1162+point split endpoint 4096 1163)/2 = (605388427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605388427:ℝ)/168755200)*ClassicalSixthBranch.v ((605388427:ℝ)/168755200)/ClassicalSixthBranch.r = (134090377347465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1162
  · change upperPayment 1163 ≤ upperValue ((point split endpoint 4096 1163+point split endpoint 4096 1164)/2)
    have hp : upperPayment 1163 = (347729012094:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1163+point split endpoint 4096 1164)/2 = (605413577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605413577:ℝ)/168755200)*ClassicalSixthBranch.v ((605413577:ℝ)/168755200)/ClassicalSixthBranch.r = (134066714026337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1163
  · change upperPayment 1164 ≤ upperValue ((point split endpoint 4096 1164+point split endpoint 4096 1165)/2)
    have hp : upperPayment 1164 = (347650794721:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1164+point split endpoint 4096 1165)/2 = (605438727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605438727:ℝ)/168755200)*ClassicalSixthBranch.v ((605438727:ℝ)/168755200)/ClassicalSixthBranch.r = (134043052729281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1164
  · change upperPayment 1165 ≤ upperValue ((point split endpoint 4096 1165+point split endpoint 4096 1166)/2)
    have hp : upperPayment 1165 = (347572554792:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1165+point split endpoint 4096 1166)/2 = (605463877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605463877:ℝ)/168755200)*ClassicalSixthBranch.v ((605463877:ℝ)/168755200)/ClassicalSixthBranch.r = (134019393456297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1165
  · change upperPayment 1166 ≤ upperValue ((point split endpoint 4096 1166+point split endpoint 4096 1167)/2)
    have hp : upperPayment 1166 = (347494292302:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1166+point split endpoint 4096 1167)/2 = (605489027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605489027:ℝ)/168755200)*ClassicalSixthBranch.v ((605489027:ℝ)/168755200)/ClassicalSixthBranch.r = (133995736207385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1166
  · change upperPayment 1167 ≤ upperValue ((point split endpoint 4096 1167+point split endpoint 4096 1168)/2)
    have hp : upperPayment 1167 = (347416007248:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1167+point split endpoint 4096 1168)/2 = (605514177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605514177:ℝ)/168755200)*ClassicalSixthBranch.v ((605514177:ℝ)/168755200)/ClassicalSixthBranch.r = (133972080982545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1167
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_072
