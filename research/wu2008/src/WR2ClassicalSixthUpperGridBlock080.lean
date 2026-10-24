import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints080
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_080 (j : Fin 16) : upperPayment (16*80+j.val) ≤
    upperValue ((point split endpoint 4096 (16*80+j.val)+point split endpoint 4096 (16*80+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1280 ≤ upperValue ((point split endpoint 4096 1280+point split endpoint 4096 1281)/2)
    have hp : upperPayment 1280 = (338423545422:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1280+point split endpoint 4096 1281)/2 = (608356127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608356127:ℝ)/168755200)*ClassicalSixthBranch.v ((608356127:ℝ)/168755200)/ClassicalSixthBranch.r = (131312077623377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1280
  · change upperPayment 1281 ≤ upperValue ((point split endpoint 4096 1281+point split endpoint 4096 1282)/2)
    have hp : upperPayment 1281 = (338342663650:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1281+point split endpoint 4096 1282)/2 = (608381277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608381277:ℝ)/168755200)*ClassicalSixthBranch.v ((608381277:ℝ)/168755200)/ClassicalSixthBranch.r = (131288653142745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1281
  · change upperPayment 1282 ≤ upperValue ((point split endpoint 4096 1282+point split endpoint 4096 1283)/2)
    have hp : upperPayment 1282 = (338261758882:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1282+point split endpoint 4096 1283)/2 = (608406427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608406427:ℝ)/168755200)*ClassicalSixthBranch.v ((608406427:ℝ)/168755200)/ClassicalSixthBranch.r = (131265230686185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1282
  · change upperPayment 1283 ≤ upperValue ((point split endpoint 4096 1283+point split endpoint 4096 1284)/2)
    have hp : upperPayment 1283 = (338180831114:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1283+point split endpoint 4096 1284)/2 = (608431577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608431577:ℝ)/168755200)*ClassicalSixthBranch.v ((608431577:ℝ)/168755200)/ClassicalSixthBranch.r = (131241810253697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1283
  · change upperPayment 1284 ≤ upperValue ((point split endpoint 4096 1284+point split endpoint 4096 1285)/2)
    have hp : upperPayment 1284 = (338099880342:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1284+point split endpoint 4096 1285)/2 = (608456727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608456727:ℝ)/168755200)*ClassicalSixthBranch.v ((608456727:ℝ)/168755200)/ClassicalSixthBranch.r = (131218391845281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1284
  · change upperPayment 1285 ≤ upperValue ((point split endpoint 4096 1285+point split endpoint 4096 1286)/2)
    have hp : upperPayment 1285 = (338018906563:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1285+point split endpoint 4096 1286)/2 = (608481877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608481877:ℝ)/168755200)*ClassicalSixthBranch.v ((608481877:ℝ)/168755200)/ClassicalSixthBranch.r = (131194975460937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1285
  · change upperPayment 1286 ≤ upperValue ((point split endpoint 4096 1286+point split endpoint 4096 1287)/2)
    have hp : upperPayment 1286 = (337937909773:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1286+point split endpoint 4096 1287)/2 = (608507027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608507027:ℝ)/168755200)*ClassicalSixthBranch.v ((608507027:ℝ)/168755200)/ClassicalSixthBranch.r = (131171561100665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1286
  · change upperPayment 1287 ≤ upperValue ((point split endpoint 4096 1287+point split endpoint 4096 1288)/2)
    have hp : upperPayment 1287 = (337856889967:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1287+point split endpoint 4096 1288)/2 = (608532177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608532177:ℝ)/168755200)*ClassicalSixthBranch.v ((608532177:ℝ)/168755200)/ClassicalSixthBranch.r = (131148148764465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1287
  · change upperPayment 1288 ≤ upperValue ((point split endpoint 4096 1288+point split endpoint 4096 1289)/2)
    have hp : upperPayment 1288 = (337775847142:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1288+point split endpoint 4096 1289)/2 = (608557327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608557327:ℝ)/168755200)*ClassicalSixthBranch.v ((608557327:ℝ)/168755200)/ClassicalSixthBranch.r = (131124738452337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1288
  · change upperPayment 1289 ≤ upperValue ((point split endpoint 4096 1289+point split endpoint 4096 1290)/2)
    have hp : upperPayment 1289 = (337694781293:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1289+point split endpoint 4096 1290)/2 = (608582477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608582477:ℝ)/168755200)*ClassicalSixthBranch.v ((608582477:ℝ)/168755200)/ClassicalSixthBranch.r = (131101330164281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1289
  · change upperPayment 1290 ≤ upperValue ((point split endpoint 4096 1290+point split endpoint 4096 1291)/2)
    have hp : upperPayment 1290 = (337613692418:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1290+point split endpoint 4096 1291)/2 = (608607627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608607627:ℝ)/168755200)*ClassicalSixthBranch.v ((608607627:ℝ)/168755200)/ClassicalSixthBranch.r = (131077923900297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1290
  · change upperPayment 1291 ≤ upperValue ((point split endpoint 4096 1291+point split endpoint 4096 1292)/2)
    have hp : upperPayment 1291 = (337532580512:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1291+point split endpoint 4096 1292)/2 = (608632777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608632777:ℝ)/168755200)*ClassicalSixthBranch.v ((608632777:ℝ)/168755200)/ClassicalSixthBranch.r = (131054519660385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1291
  · change upperPayment 1292 ≤ upperValue ((point split endpoint 4096 1292+point split endpoint 4096 1293)/2)
    have hp : upperPayment 1292 = (337451445572:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1292+point split endpoint 4096 1293)/2 = (608657927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608657927:ℝ)/168755200)*ClassicalSixthBranch.v ((608657927:ℝ)/168755200)/ClassicalSixthBranch.r = (131031117444545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1292
  · change upperPayment 1293 ≤ upperValue ((point split endpoint 4096 1293+point split endpoint 4096 1294)/2)
    have hp : upperPayment 1293 = (337370287593:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1293+point split endpoint 4096 1294)/2 = (608683077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608683077:ℝ)/168755200)*ClassicalSixthBranch.v ((608683077:ℝ)/168755200)/ClassicalSixthBranch.r = (131007717252777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1293
  · change upperPayment 1294 ≤ upperValue ((point split endpoint 4096 1294+point split endpoint 4096 1295)/2)
    have hp : upperPayment 1294 = (337289106572:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1294+point split endpoint 4096 1295)/2 = (608708227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608708227:ℝ)/168755200)*ClassicalSixthBranch.v ((608708227:ℝ)/168755200)/ClassicalSixthBranch.r = (130984319085081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1294
  · change upperPayment 1295 ≤ upperValue ((point split endpoint 4096 1295+point split endpoint 4096 1296)/2)
    have hp : upperPayment 1295 = (337207902504:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1295+point split endpoint 4096 1296)/2 = (608733377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608733377:ℝ)/168755200)*ClassicalSixthBranch.v ((608733377:ℝ)/168755200)/ClassicalSixthBranch.r = (130960922941457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1295
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_080
