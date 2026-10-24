import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints203
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_203 (j : Fin 16) : upperPayment (16*203+j.val) ≤
    upperValue ((point split endpoint 4096 (16*203+j.val)+point split endpoint 4096 (16*203+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3248 ≤ upperValue ((point split endpoint 4096 3248+point split endpoint 4096 3249)/2)
    have hp : upperPayment 3248 = (128684391922:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3248+point split endpoint 4096 3249)/2 = (657851327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657851327:ℝ)/168755200)*ClassicalSixthBranch.v ((657851327:ℝ)/168755200)/ClassicalSixthBranch.r = (89130347769617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3248
  · change upperPayment 3249 ≤ upperValue ((point split endpoint 4096 3249+point split endpoint 4096 3250)/2)
    have hp : upperPayment 3249 = (128548323025:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3249+point split endpoint 4096 3250)/2 = (657876477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657876477:ℝ)/168755200)*ClassicalSixthBranch.v ((657876477:ℝ)/168755200)/ClassicalSixthBranch.r = (89110906662681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3249
  · change upperPayment 3250 ≤ upperValue ((point split endpoint 4096 3250+point split endpoint 4096 3251)/2)
    have hp : upperPayment 3250 = (128412219509:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3250+point split endpoint 4096 3251)/2 = (657901627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657901627:ℝ)/168755200)*ClassicalSixthBranch.v ((657901627:ℝ)/168755200)/ClassicalSixthBranch.r = (89091467579817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3250
  · change upperPayment 3251 ≤ upperValue ((point split endpoint 4096 3251+point split endpoint 4096 3252)/2)
    have hp : upperPayment 3251 = (128276081365:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3251+point split endpoint 4096 3252)/2 = (657926777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657926777:ℝ)/168755200)*ClassicalSixthBranch.v ((657926777:ℝ)/168755200)/ClassicalSixthBranch.r = (89072030521025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3251
  · change upperPayment 3252 ≤ upperValue ((point split endpoint 4096 3252+point split endpoint 4096 3253)/2)
    have hp : upperPayment 3252 = (128139908584:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3252+point split endpoint 4096 3253)/2 = (657951927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657951927:ℝ)/168755200)*ClassicalSixthBranch.v ((657951927:ℝ)/168755200)/ClassicalSixthBranch.r = (89052595486305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3252
  · change upperPayment 3253 ≤ upperValue ((point split endpoint 4096 3253+point split endpoint 4096 3254)/2)
    have hp : upperPayment 3253 = (128003701157:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3253+point split endpoint 4096 3254)/2 = (657977077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657977077:ℝ)/168755200)*ClassicalSixthBranch.v ((657977077:ℝ)/168755200)/ClassicalSixthBranch.r = (89033162475657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3253
  · change upperPayment 3254 ≤ upperValue ((point split endpoint 4096 3254+point split endpoint 4096 3255)/2)
    have hp : upperPayment 3254 = (127867459077:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3254+point split endpoint 4096 3255)/2 = (658002227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658002227:ℝ)/168755200)*ClassicalSixthBranch.v ((658002227:ℝ)/168755200)/ClassicalSixthBranch.r = (89013731489081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3254
  · change upperPayment 3255 ≤ upperValue ((point split endpoint 4096 3255+point split endpoint 4096 3256)/2)
    have hp : upperPayment 3255 = (127731182334:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3255+point split endpoint 4096 3256)/2 = (658027377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658027377:ℝ)/168755200)*ClassicalSixthBranch.v ((658027377:ℝ)/168755200)/ClassicalSixthBranch.r = (88994302526577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3255
  · change upperPayment 3256 ≤ upperValue ((point split endpoint 4096 3256+point split endpoint 4096 3257)/2)
    have hp : upperPayment 3256 = (127594870921:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3256+point split endpoint 4096 3257)/2 = (658052527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658052527:ℝ)/168755200)*ClassicalSixthBranch.v ((658052527:ℝ)/168755200)/ClassicalSixthBranch.r = (88974875588145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3256
  · change upperPayment 3257 ≤ upperValue ((point split endpoint 4096 3257+point split endpoint 4096 3258)/2)
    have hp : upperPayment 3257 = (127458524828:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3257+point split endpoint 4096 3258)/2 = (658077677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658077677:ℝ)/168755200)*ClassicalSixthBranch.v ((658077677:ℝ)/168755200)/ClassicalSixthBranch.r = (88955450673785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3257
  · change upperPayment 3258 ≤ upperValue ((point split endpoint 4096 3258+point split endpoint 4096 3259)/2)
    have hp : upperPayment 3258 = (127322144046:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3258+point split endpoint 4096 3259)/2 = (658102827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658102827:ℝ)/168755200)*ClassicalSixthBranch.v ((658102827:ℝ)/168755200)/ClassicalSixthBranch.r = (88936027783497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3258
  · change upperPayment 3259 ≤ upperValue ((point split endpoint 4096 3259+point split endpoint 4096 3260)/2)
    have hp : upperPayment 3259 = (127185728568:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3259+point split endpoint 4096 3260)/2 = (658127977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658127977:ℝ)/168755200)*ClassicalSixthBranch.v ((658127977:ℝ)/168755200)/ClassicalSixthBranch.r = (88916606917281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3259
  · change upperPayment 3260 ≤ upperValue ((point split endpoint 4096 3260+point split endpoint 4096 3261)/2)
    have hp : upperPayment 3260 = (127049278384:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3260+point split endpoint 4096 3261)/2 = (658153127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658153127:ℝ)/168755200)*ClassicalSixthBranch.v ((658153127:ℝ)/168755200)/ClassicalSixthBranch.r = (88897188075137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3260
  · change upperPayment 3261 ≤ upperValue ((point split endpoint 4096 3261+point split endpoint 4096 3262)/2)
    have hp : upperPayment 3261 = (126912793487:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3261+point split endpoint 4096 3262)/2 = (658178277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658178277:ℝ)/168755200)*ClassicalSixthBranch.v ((658178277:ℝ)/168755200)/ClassicalSixthBranch.r = (88877771257065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3261
  · change upperPayment 3262 ≤ upperValue ((point split endpoint 4096 3262+point split endpoint 4096 3263)/2)
    have hp : upperPayment 3262 = (126776273867:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3262+point split endpoint 4096 3263)/2 = (658203427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658203427:ℝ)/168755200)*ClassicalSixthBranch.v ((658203427:ℝ)/168755200)/ClassicalSixthBranch.r = (88858356463065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3262
  · change upperPayment 3263 ≤ upperValue ((point split endpoint 4096 3263+point split endpoint 4096 3264)/2)
    have hp : upperPayment 3263 = (126639719515:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3263+point split endpoint 4096 3264)/2 = (658228577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658228577:ℝ)/168755200)*ClassicalSixthBranch.v ((658228577:ℝ)/168755200)/ClassicalSixthBranch.r = (88838943693137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3263
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_203
