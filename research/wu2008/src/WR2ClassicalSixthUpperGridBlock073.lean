import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints073
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_073 (j : Fin 16) : upperPayment (16*73+j.val) ≤
    upperValue ((point split endpoint 4096 (16*73+j.val)+point split endpoint 4096 (16*73+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1168 ≤ upperValue ((point split endpoint 4096 1168+point split endpoint 4096 1169)/2)
    have hp : upperPayment 1168 = (347337699626:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1168+point split endpoint 4096 1169)/2 = (605539327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605539327:ℝ)/168755200)*ClassicalSixthBranch.v ((605539327:ℝ)/168755200)/ClassicalSixthBranch.r = (133948427781777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1168
  · change upperPayment 1169 ≤ upperValue ((point split endpoint 4096 1169+point split endpoint 4096 1170)/2)
    have hp : upperPayment 1169 = (347259369434:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1169+point split endpoint 4096 1170)/2 = (605564477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605564477:ℝ)/168755200)*ClassicalSixthBranch.v ((605564477:ℝ)/168755200)/ClassicalSixthBranch.r = (133924776605081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1169
  · change upperPayment 1170 ≤ upperValue ((point split endpoint 4096 1170+point split endpoint 4096 1171)/2)
    have hp : upperPayment 1170 = (347181016666:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1170+point split endpoint 4096 1171)/2 = (605589627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605589627:ℝ)/168755200)*ClassicalSixthBranch.v ((605589627:ℝ)/168755200)/ClassicalSixthBranch.r = (133901127452457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1170
  · change upperPayment 1171 ≤ upperValue ((point split endpoint 4096 1171+point split endpoint 4096 1172)/2)
    have hp : upperPayment 1171 = (347102641319:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1171+point split endpoint 4096 1172)/2 = (605614777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605614777:ℝ)/168755200)*ClassicalSixthBranch.v ((605614777:ℝ)/168755200)/ClassicalSixthBranch.r = (133877480323905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1171
  · change upperPayment 1172 ≤ upperValue ((point split endpoint 4096 1172+point split endpoint 4096 1173)/2)
    have hp : upperPayment 1172 = (347024243391:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1172+point split endpoint 4096 1173)/2 = (605639927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605639927:ℝ)/168755200)*ClassicalSixthBranch.v ((605639927:ℝ)/168755200)/ClassicalSixthBranch.r = (133853835219425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1172
  · change upperPayment 1173 ≤ upperValue ((point split endpoint 4096 1173+point split endpoint 4096 1174)/2)
    have hp : upperPayment 1173 = (346945822876:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1173+point split endpoint 4096 1174)/2 = (605665077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605665077:ℝ)/168755200)*ClassicalSixthBranch.v ((605665077:ℝ)/168755200)/ClassicalSixthBranch.r = (133830192139017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1173
  · change upperPayment 1174 ≤ upperValue ((point split endpoint 4096 1174+point split endpoint 4096 1175)/2)
    have hp : upperPayment 1174 = (346867379772:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1174+point split endpoint 4096 1175)/2 = (605690227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605690227:ℝ)/168755200)*ClassicalSixthBranch.v ((605690227:ℝ)/168755200)/ClassicalSixthBranch.r = (133806551082681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1174
  · change upperPayment 1175 ≤ upperValue ((point split endpoint 4096 1175+point split endpoint 4096 1176)/2)
    have hp : upperPayment 1175 = (346788914074:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1175+point split endpoint 4096 1176)/2 = (605715377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605715377:ℝ)/168755200)*ClassicalSixthBranch.v ((605715377:ℝ)/168755200)/ClassicalSixthBranch.r = (133782912050417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1175
  · change upperPayment 1176 ≤ upperValue ((point split endpoint 4096 1176+point split endpoint 4096 1177)/2)
    have hp : upperPayment 1176 = (346710425779:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1176+point split endpoint 4096 1177)/2 = (605740527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605740527:ℝ)/168755200)*ClassicalSixthBranch.v ((605740527:ℝ)/168755200)/ClassicalSixthBranch.r = (133759275042225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1176
  · change upperPayment 1177 ≤ upperValue ((point split endpoint 4096 1177+point split endpoint 4096 1178)/2)
    have hp : upperPayment 1177 = (346631914884:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1177+point split endpoint 4096 1178)/2 = (605765677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605765677:ℝ)/168755200)*ClassicalSixthBranch.v ((605765677:ℝ)/168755200)/ClassicalSixthBranch.r = (133735640058105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1177
  · change upperPayment 1178 ≤ upperValue ((point split endpoint 4096 1178+point split endpoint 4096 1179)/2)
    have hp : upperPayment 1178 = (346553381384:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1178+point split endpoint 4096 1179)/2 = (605790827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605790827:ℝ)/168755200)*ClassicalSixthBranch.v ((605790827:ℝ)/168755200)/ClassicalSixthBranch.r = (133712007098057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1178
  · change upperPayment 1179 ≤ upperValue ((point split endpoint 4096 1179+point split endpoint 4096 1180)/2)
    have hp : upperPayment 1179 = (346474825276:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1179+point split endpoint 4096 1180)/2 = (605815977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605815977:ℝ)/168755200)*ClassicalSixthBranch.v ((605815977:ℝ)/168755200)/ClassicalSixthBranch.r = (133688376162081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1179
  · change upperPayment 1180 ≤ upperValue ((point split endpoint 4096 1180+point split endpoint 4096 1181)/2)
    have hp : upperPayment 1180 = (346396246556:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1180+point split endpoint 4096 1181)/2 = (605841127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605841127:ℝ)/168755200)*ClassicalSixthBranch.v ((605841127:ℝ)/168755200)/ClassicalSixthBranch.r = (133664747250177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1180
  · change upperPayment 1181 ≤ upperValue ((point split endpoint 4096 1181+point split endpoint 4096 1182)/2)
    have hp : upperPayment 1181 = (346317645221:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1181+point split endpoint 4096 1182)/2 = (605866277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605866277:ℝ)/168755200)*ClassicalSixthBranch.v ((605866277:ℝ)/168755200)/ClassicalSixthBranch.r = (133641120362345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1181
  · change upperPayment 1182 ≤ upperValue ((point split endpoint 4096 1182+point split endpoint 4096 1183)/2)
    have hp : upperPayment 1182 = (346239021267:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1182+point split endpoint 4096 1183)/2 = (605891427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605891427:ℝ)/168755200)*ClassicalSixthBranch.v ((605891427:ℝ)/168755200)/ClassicalSixthBranch.r = (133617495498585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1182
  · change upperPayment 1183 ≤ upperValue ((point split endpoint 4096 1183+point split endpoint 4096 1184)/2)
    have hp : upperPayment 1183 = (346160374690:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1183+point split endpoint 4096 1184)/2 = (605916577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605916577:ℝ)/168755200)*ClassicalSixthBranch.v ((605916577:ℝ)/168755200)/ClassicalSixthBranch.r = (133593872658897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1183
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_073
