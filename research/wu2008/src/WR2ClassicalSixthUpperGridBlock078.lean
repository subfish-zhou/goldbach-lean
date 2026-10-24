import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints078
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_078 (j : Fin 16) : upperPayment (16*78+j.val) ≤
    upperValue ((point split endpoint 4096 (16*78+j.val)+point split endpoint 4096 (16*78+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1248 ≤ upperValue ((point split endpoint 4096 1248+point split endpoint 4096 1249)/2)
    have hp : upperPayment 1248 = (340999643165:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1248+point split endpoint 4096 1249)/2 = (607551327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607551327:ℝ)/168755200)*ClassicalSixthBranch.v ((607551327:ℝ)/168755200)/ClassicalSixthBranch.r = (132062729713617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1248
  · change upperPayment 1249 ≤ upperValue ((point split endpoint 4096 1249+point split endpoint 4096 1250)/2)
    have hp : upperPayment 1249 = (340919495243:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1249+point split endpoint 4096 1250)/2 = (607576477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607576477:ℝ)/168755200)*ClassicalSixthBranch.v ((607576477:ℝ)/168755200)/ClassicalSixthBranch.r = (132039240462681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1249
  · change upperPayment 1250 ≤ upperValue ((point split endpoint 4096 1250+point split endpoint 4096 1251)/2)
    have hp : upperPayment 1250 = (340839324448:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1250+point split endpoint 4096 1251)/2 = (607601627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607601627:ℝ)/168755200)*ClassicalSixthBranch.v ((607601627:ℝ)/168755200)/ClassicalSixthBranch.r = (132015753235817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1250
  · change upperPayment 1251 ≤ upperValue ((point split endpoint 4096 1251+point split endpoint 4096 1252)/2)
    have hp : upperPayment 1251 = (340759130775:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1251+point split endpoint 4096 1252)/2 = (607626777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607626777:ℝ)/168755200)*ClassicalSixthBranch.v ((607626777:ℝ)/168755200)/ClassicalSixthBranch.r = (131992268033025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1251
  · change upperPayment 1252 ≤ upperValue ((point split endpoint 4096 1252+point split endpoint 4096 1253)/2)
    have hp : upperPayment 1252 = (340678914221:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1252+point split endpoint 4096 1253)/2 = (607651927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607651927:ℝ)/168755200)*ClassicalSixthBranch.v ((607651927:ℝ)/168755200)/ClassicalSixthBranch.r = (131968784854305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1252
  · change upperPayment 1253 ≤ upperValue ((point split endpoint 4096 1253+point split endpoint 4096 1254)/2)
    have hp : upperPayment 1253 = (340598674782:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1253+point split endpoint 4096 1254)/2 = (607677077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607677077:ℝ)/168755200)*ClassicalSixthBranch.v ((607677077:ℝ)/168755200)/ClassicalSixthBranch.r = (131945303699657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1253
  · change upperPayment 1254 ≤ upperValue ((point split endpoint 4096 1254+point split endpoint 4096 1255)/2)
    have hp : upperPayment 1254 = (340518412454:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1254+point split endpoint 4096 1255)/2 = (607702227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607702227:ℝ)/168755200)*ClassicalSixthBranch.v ((607702227:ℝ)/168755200)/ClassicalSixthBranch.r = (131921824569081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1254
  · change upperPayment 1255 ≤ upperValue ((point split endpoint 4096 1255+point split endpoint 4096 1256)/2)
    have hp : upperPayment 1255 = (340438127233:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1255+point split endpoint 4096 1256)/2 = (607727377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607727377:ℝ)/168755200)*ClassicalSixthBranch.v ((607727377:ℝ)/168755200)/ClassicalSixthBranch.r = (131898347462577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1255
  · change upperPayment 1256 ≤ upperValue ((point split endpoint 4096 1256+point split endpoint 4096 1257)/2)
    have hp : upperPayment 1256 = (340357819115:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1256+point split endpoint 4096 1257)/2 = (607752527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607752527:ℝ)/168755200)*ClassicalSixthBranch.v ((607752527:ℝ)/168755200)/ClassicalSixthBranch.r = (131874872380145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1256
  · change upperPayment 1257 ≤ upperValue ((point split endpoint 4096 1257+point split endpoint 4096 1258)/2)
    have hp : upperPayment 1257 = (340277488098:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1257+point split endpoint 4096 1258)/2 = (607777677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607777677:ℝ)/168755200)*ClassicalSixthBranch.v ((607777677:ℝ)/168755200)/ClassicalSixthBranch.r = (131851399321785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1257
  · change upperPayment 1258 ≤ upperValue ((point split endpoint 4096 1258+point split endpoint 4096 1259)/2)
    have hp : upperPayment 1258 = (340197134176:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1258+point split endpoint 4096 1259)/2 = (607802827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607802827:ℝ)/168755200)*ClassicalSixthBranch.v ((607802827:ℝ)/168755200)/ClassicalSixthBranch.r = (131827928287497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1258
  · change upperPayment 1259 ≤ upperValue ((point split endpoint 4096 1259+point split endpoint 4096 1260)/2)
    have hp : upperPayment 1259 = (340116757346:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1259+point split endpoint 4096 1260)/2 = (607827977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607827977:ℝ)/168755200)*ClassicalSixthBranch.v ((607827977:ℝ)/168755200)/ClassicalSixthBranch.r = (131804459277281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1259
  · change upperPayment 1260 ≤ upperValue ((point split endpoint 4096 1260+point split endpoint 4096 1261)/2)
    have hp : upperPayment 1260 = (340036357605:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1260+point split endpoint 4096 1261)/2 = (607853127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607853127:ℝ)/168755200)*ClassicalSixthBranch.v ((607853127:ℝ)/168755200)/ClassicalSixthBranch.r = (131780992291137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1260
  · change upperPayment 1261 ≤ upperValue ((point split endpoint 4096 1261+point split endpoint 4096 1262)/2)
    have hp : upperPayment 1261 = (339955934948:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1261+point split endpoint 4096 1262)/2 = (607878277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607878277:ℝ)/168755200)*ClassicalSixthBranch.v ((607878277:ℝ)/168755200)/ClassicalSixthBranch.r = (131757527329065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1261
  · change upperPayment 1262 ≤ upperValue ((point split endpoint 4096 1262+point split endpoint 4096 1263)/2)
    have hp : upperPayment 1262 = (339875489371:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1262+point split endpoint 4096 1263)/2 = (607903427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607903427:ℝ)/168755200)*ClassicalSixthBranch.v ((607903427:ℝ)/168755200)/ClassicalSixthBranch.r = (131734064391065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1262
  · change upperPayment 1263 ≤ upperValue ((point split endpoint 4096 1263+point split endpoint 4096 1264)/2)
    have hp : upperPayment 1263 = (339795020872:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1263+point split endpoint 4096 1264)/2 = (607928577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607928577:ℝ)/168755200)*ClassicalSixthBranch.v ((607928577:ℝ)/168755200)/ClassicalSixthBranch.r = (1278743723079:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1263
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_078
