import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints016
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_016 (j : Fin 16) : upperPayment (16*16+j.val) ≤
    upperValue ((point split endpoint 4096 (16*16+j.val)+point split endpoint 4096 (16*16+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 256 ≤ upperValue ((point split endpoint 4096 256+point split endpoint 4096 257)/2)
    have hp : upperPayment 256 = (409798693839:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 256+point split endpoint 4096 257)/2 = (582602527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582602527:ℝ)/168755200)*ClassicalSixthBranch.v ((582602527:ℝ)/168755200)/ClassicalSixthBranch.r = (156360978776145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_256
  · change upperPayment 257 ≤ upperValue ((point split endpoint 4096 257+point split endpoint 4096 258)/2)
    have hp : upperPayment 257 = (409739610122:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 257+point split endpoint 4096 258)/2 = (582627677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582627677:ℝ)/168755200)*ClassicalSixthBranch.v ((582627677:ℝ)/168755200)/ClassicalSixthBranch.r = (156335481645785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_257
  · change upperPayment 258 ≤ upperValue ((point split endpoint 4096 258+point split endpoint 4096 259)/2)
    have hp : upperPayment 258 = (409680506579:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 258+point split endpoint 4096 259)/2 = (582652827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582652827:ℝ)/168755200)*ClassicalSixthBranch.v ((582652827:ℝ)/168755200)/ClassicalSixthBranch.r = (156309986539497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_258
  · change upperPayment 259 ≤ upperValue ((point split endpoint 4096 259+point split endpoint 4096 260)/2)
    have hp : upperPayment 259 = (409621383207:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 259+point split endpoint 4096 260)/2 = (582677977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582677977:ℝ)/168755200)*ClassicalSixthBranch.v ((582677977:ℝ)/168755200)/ClassicalSixthBranch.r = (156284493457281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_259
  · change upperPayment 260 ≤ upperValue ((point split endpoint 4096 260+point split endpoint 4096 261)/2)
    have hp : upperPayment 260 = (409562240003:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 260+point split endpoint 4096 261)/2 = (582703127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582703127:ℝ)/168755200)*ClassicalSixthBranch.v ((582703127:ℝ)/168755200)/ClassicalSixthBranch.r = (156259002399137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_260
  · change upperPayment 261 ≤ upperValue ((point split endpoint 4096 261+point split endpoint 4096 262)/2)
    have hp : upperPayment 261 = (409503076966:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 261+point split endpoint 4096 262)/2 = (582728277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582728277:ℝ)/168755200)*ClassicalSixthBranch.v ((582728277:ℝ)/168755200)/ClassicalSixthBranch.r = (156233513365065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_261
  · change upperPayment 262 ≤ upperValue ((point split endpoint 4096 262+point split endpoint 4096 263)/2)
    have hp : upperPayment 262 = (409443894093:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 262+point split endpoint 4096 263)/2 = (582753427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582753427:ℝ)/168755200)*ClassicalSixthBranch.v ((582753427:ℝ)/168755200)/ClassicalSixthBranch.r = (156208026355065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_262
  · change upperPayment 263 ≤ upperValue ((point split endpoint 4096 263+point split endpoint 4096 264)/2)
    have hp : upperPayment 263 = (409384691381:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 263+point split endpoint 4096 264)/2 = (582778577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582778577:ℝ)/168755200)*ClassicalSixthBranch.v ((582778577:ℝ)/168755200)/ClassicalSixthBranch.r = (156182541369137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_263
  · change upperPayment 264 ≤ upperValue ((point split endpoint 4096 264+point split endpoint 4096 265)/2)
    have hp : upperPayment 264 = (409325468828:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 264+point split endpoint 4096 265)/2 = (582803727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582803727:ℝ)/168755200)*ClassicalSixthBranch.v ((582803727:ℝ)/168755200)/ClassicalSixthBranch.r = (156157058407281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_264
  · change upperPayment 265 ≤ upperValue ((point split endpoint 4096 265+point split endpoint 4096 266)/2)
    have hp : upperPayment 265 = (409266226432:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 265+point split endpoint 4096 266)/2 = (582828877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582828877:ℝ)/168755200)*ClassicalSixthBranch.v ((582828877:ℝ)/168755200)/ClassicalSixthBranch.r = (156131577469497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_265
  · change upperPayment 266 ≤ upperValue ((point split endpoint 4096 266+point split endpoint 4096 267)/2)
    have hp : upperPayment 266 = (409206964189:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 266+point split endpoint 4096 267)/2 = (582854027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582854027:ℝ)/168755200)*ClassicalSixthBranch.v ((582854027:ℝ)/168755200)/ClassicalSixthBranch.r = (156106098555785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_266
  · change upperPayment 267 ≤ upperValue ((point split endpoint 4096 267+point split endpoint 4096 268)/2)
    have hp : upperPayment 267 = (409147682099:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 267+point split endpoint 4096 268)/2 = (582879177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582879177:ℝ)/168755200)*ClassicalSixthBranch.v ((582879177:ℝ)/168755200)/ClassicalSixthBranch.r = (156080621666145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_267
  · change upperPayment 268 ≤ upperValue ((point split endpoint 4096 268+point split endpoint 4096 269)/2)
    have hp : upperPayment 268 = (409088380158:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 268+point split endpoint 4096 269)/2 = (582904327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582904327:ℝ)/168755200)*ClassicalSixthBranch.v ((582904327:ℝ)/168755200)/ClassicalSixthBranch.r = (156055146800577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_268
  · change upperPayment 269 ≤ upperValue ((point split endpoint 4096 269+point split endpoint 4096 270)/2)
    have hp : upperPayment 269 = (409029058364:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 269+point split endpoint 4096 270)/2 = (582929477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582929477:ℝ)/168755200)*ClassicalSixthBranch.v ((582929477:ℝ)/168755200)/ClassicalSixthBranch.r = (156029673959081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_269
  · change upperPayment 270 ≤ upperValue ((point split endpoint 4096 270+point split endpoint 4096 271)/2)
    have hp : upperPayment 270 = (408969716714:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 270+point split endpoint 4096 271)/2 = (582954627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582954627:ℝ)/168755200)*ClassicalSixthBranch.v ((582954627:ℝ)/168755200)/ClassicalSixthBranch.r = (156004203141657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_270
  · change upperPayment 271 ≤ upperValue ((point split endpoint 4096 271+point split endpoint 4096 272)/2)
    have hp : upperPayment 271 = (408910355207:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 271+point split endpoint 4096 272)/2 = (582979777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582979777:ℝ)/168755200)*ClassicalSixthBranch.v ((582979777:ℝ)/168755200)/ClassicalSixthBranch.r = (155978734348305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_271
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_016
