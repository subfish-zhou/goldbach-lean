import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints075
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_075 (j : Fin 16) : upperPayment (16*75+j.val) ≤
    upperValue ((point split endpoint 4096 (16*75+j.val)+point split endpoint 4096 (16*75+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1200 ≤ upperValue ((point split endpoint 4096 1200+point split endpoint 4096 1201)/2)
    have hp : upperPayment 1200 = (344819918006:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1200+point split endpoint 4096 1201)/2 = (606344127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606344127:ℝ)/168755200)*ClassicalSixthBranch.v ((606344127:ℝ)/168755200)/ClassicalSixthBranch.r = (133192594067217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1200
  · change upperPayment 1201 ≤ upperValue ((point split endpoint 4096 1201+point split endpoint 4096 1202)/2)
    have hp : upperPayment 1201 = (344740863586:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1201+point split endpoint 4096 1202)/2 = (606369277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606369277:ℝ)/168755200)*ClassicalSixthBranch.v ((606369277:ℝ)/168755200)/ClassicalSixthBranch.r = (133169007660825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1201
  · change upperPayment 1202 ≤ upperValue ((point split endpoint 4096 1202+point split endpoint 4096 1203)/2)
    have hp : upperPayment 1202 = (344661786472:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1202+point split endpoint 4096 1203)/2 = (606394427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606394427:ℝ)/168755200)*ClassicalSixthBranch.v ((606394427:ℝ)/168755200)/ClassicalSixthBranch.r = (133145423278505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1202
  · change upperPayment 1203 ≤ upperValue ((point split endpoint 4096 1203+point split endpoint 4096 1204)/2)
    have hp : upperPayment 1203 = (344582686661:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1203+point split endpoint 4096 1204)/2 = (606419577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606419577:ℝ)/168755200)*ClassicalSixthBranch.v ((606419577:ℝ)/168755200)/ClassicalSixthBranch.r = (133121840920257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1203
  · change upperPayment 1204 ≤ upperValue ((point split endpoint 4096 1204+point split endpoint 4096 1205)/2)
    have hp : upperPayment 1204 = (344503564150:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1204+point split endpoint 4096 1205)/2 = (606444727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606444727:ℝ)/168755200)*ClassicalSixthBranch.v ((606444727:ℝ)/168755200)/ClassicalSixthBranch.r = (133098260586081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1204
  · change upperPayment 1205 ≤ upperValue ((point split endpoint 4096 1205+point split endpoint 4096 1206)/2)
    have hp : upperPayment 1205 = (344424418934:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1205+point split endpoint 4096 1206)/2 = (606469877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606469877:ℝ)/168755200)*ClassicalSixthBranch.v ((606469877:ℝ)/168755200)/ClassicalSixthBranch.r = (133074682275977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1205
  · change upperPayment 1206 ≤ upperValue ((point split endpoint 4096 1206+point split endpoint 4096 1207)/2)
    have hp : upperPayment 1206 = (344345251010:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1206+point split endpoint 4096 1207)/2 = (606495027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606495027:ℝ)/168755200)*ClassicalSixthBranch.v ((606495027:ℝ)/168755200)/ClassicalSixthBranch.r = (133051105989945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1206
  · change upperPayment 1207 ≤ upperValue ((point split endpoint 4096 1207+point split endpoint 4096 1208)/2)
    have hp : upperPayment 1207 = (344266060374:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1207+point split endpoint 4096 1208)/2 = (606520177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606520177:ℝ)/168755200)*ClassicalSixthBranch.v ((606520177:ℝ)/168755200)/ClassicalSixthBranch.r = (133027531727985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1207
  · change upperPayment 1208 ≤ upperValue ((point split endpoint 4096 1208+point split endpoint 4096 1209)/2)
    have hp : upperPayment 1208 = (344186847022:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1208+point split endpoint 4096 1209)/2 = (606545327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606545327:ℝ)/168755200)*ClassicalSixthBranch.v ((606545327:ℝ)/168755200)/ClassicalSixthBranch.r = (133003959490097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1208
  · change upperPayment 1209 ≤ upperValue ((point split endpoint 4096 1209+point split endpoint 4096 1210)/2)
    have hp : upperPayment 1209 = (344107610952:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1209+point split endpoint 4096 1210)/2 = (606570477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606570477:ℝ)/168755200)*ClassicalSixthBranch.v ((606570477:ℝ)/168755200)/ClassicalSixthBranch.r = (132980389276281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1209
  · change upperPayment 1210 ≤ upperValue ((point split endpoint 4096 1210+point split endpoint 4096 1211)/2)
    have hp : upperPayment 1210 = (344028352158:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1210+point split endpoint 4096 1211)/2 = (606595627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606595627:ℝ)/168755200)*ClassicalSixthBranch.v ((606595627:ℝ)/168755200)/ClassicalSixthBranch.r = (132956821086537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1210
  · change upperPayment 1211 ≤ upperValue ((point split endpoint 4096 1211+point split endpoint 4096 1212)/2)
    have hp : upperPayment 1211 = (343949070637:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1211+point split endpoint 4096 1212)/2 = (606620777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606620777:ℝ)/168755200)*ClassicalSixthBranch.v ((606620777:ℝ)/168755200)/ClassicalSixthBranch.r = (132933254920865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1211
  · change upperPayment 1212 ≤ upperValue ((point split endpoint 4096 1212+point split endpoint 4096 1213)/2)
    have hp : upperPayment 1212 = (343869766386:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1212+point split endpoint 4096 1213)/2 = (606645927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606645927:ℝ)/168755200)*ClassicalSixthBranch.v ((606645927:ℝ)/168755200)/ClassicalSixthBranch.r = (132909690779265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1212
  · change upperPayment 1213 ≤ upperValue ((point split endpoint 4096 1213+point split endpoint 4096 1214)/2)
    have hp : upperPayment 1213 = (343790439401:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1213+point split endpoint 4096 1214)/2 = (606671077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606671077:ℝ)/168755200)*ClassicalSixthBranch.v ((606671077:ℝ)/168755200)/ClassicalSixthBranch.r = (132886128661737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1213
  · change upperPayment 1214 ≤ upperValue ((point split endpoint 4096 1214+point split endpoint 4096 1215)/2)
    have hp : upperPayment 1214 = (343711089677:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1214+point split endpoint 4096 1215)/2 = (606696227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606696227:ℝ)/168755200)*ClassicalSixthBranch.v ((606696227:ℝ)/168755200)/ClassicalSixthBranch.r = (132862568568281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1214
  · change upperPayment 1215 ≤ upperValue ((point split endpoint 4096 1215+point split endpoint 4096 1216)/2)
    have hp : upperPayment 1215 = (343631717212:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1215+point split endpoint 4096 1216)/2 = (606721377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606721377:ℝ)/168755200)*ClassicalSixthBranch.v ((606721377:ℝ)/168755200)/ClassicalSixthBranch.r = (132839010498897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1215
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_075
