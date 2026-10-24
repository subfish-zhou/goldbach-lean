import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints020
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_020 (j : Fin 16) : upperPayment (16*20+j.val) ≤
    upperValue ((point split endpoint 4096 (16*20+j.val)+point split endpoint 4096 (16*20+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 320 ≤ upperValue ((point split endpoint 4096 320+point split endpoint 4096 321)/2)
    have hp : upperPayment 320 = (405977264535:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 320+point split endpoint 4096 321)/2 = (584212127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584212127:ℝ)/168755200)*ClassicalSixthBranch.v ((584212127:ℝ)/168755200)/ClassicalSixthBranch.r = (154733242962257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_320
  · change upperPayment 321 ≤ upperValue ((point split endpoint 4096 321+point split endpoint 4096 322)/2)
    have hp : upperPayment 321 = (405916907012:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 321+point split endpoint 4096 322)/2 = (584237277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584237277:ℝ)/168755200)*ClassicalSixthBranch.v ((584237277:ℝ)/168755200)/ClassicalSixthBranch.r = (154707875372505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_321
  · change upperPayment 322 ≤ upperValue ((point split endpoint 4096 322+point split endpoint 4096 323)/2)
    have hp : upperPayment 322 = (405856529505:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 322+point split endpoint 4096 323)/2 = (584262427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584262427:ℝ)/168755200)*ClassicalSixthBranch.v ((584262427:ℝ)/168755200)/ClassicalSixthBranch.r = (154682509806825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_322
  · change upperPayment 323 ≤ upperValue ((point split endpoint 4096 323+point split endpoint 4096 324)/2)
    have hp : upperPayment 323 = (405796132013:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 323+point split endpoint 4096 324)/2 = (584287577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584287577:ℝ)/168755200)*ClassicalSixthBranch.v ((584287577:ℝ)/168755200)/ClassicalSixthBranch.r = (154657146265217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_323
  · change upperPayment 324 ≤ upperValue ((point split endpoint 4096 324+point split endpoint 4096 325)/2)
    have hp : upperPayment 324 = (405735714533:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 324+point split endpoint 4096 325)/2 = (584312727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584312727:ℝ)/168755200)*ClassicalSixthBranch.v ((584312727:ℝ)/168755200)/ClassicalSixthBranch.r = (154631784747681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_324
  · change upperPayment 325 ≤ upperValue ((point split endpoint 4096 325+point split endpoint 4096 326)/2)
    have hp : upperPayment 325 = (405675277062:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 325+point split endpoint 4096 326)/2 = (584337877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584337877:ℝ)/168755200)*ClassicalSixthBranch.v ((584337877:ℝ)/168755200)/ClassicalSixthBranch.r = (154606425254217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_325
  · change upperPayment 326 ≤ upperValue ((point split endpoint 4096 326+point split endpoint 4096 327)/2)
    have hp : upperPayment 326 = (405614819598:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 326+point split endpoint 4096 327)/2 = (584363027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584363027:ℝ)/168755200)*ClassicalSixthBranch.v ((584363027:ℝ)/168755200)/ClassicalSixthBranch.r = (154581067784825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_326
  · change upperPayment 327 ≤ upperValue ((point split endpoint 4096 327+point split endpoint 4096 328)/2)
    have hp : upperPayment 327 = (405554342138:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 327+point split endpoint 4096 328)/2 = (584388177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584388177:ℝ)/168755200)*ClassicalSixthBranch.v ((584388177:ℝ)/168755200)/ClassicalSixthBranch.r = (154555712339505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_327
  · change upperPayment 328 ≤ upperValue ((point split endpoint 4096 328+point split endpoint 4096 329)/2)
    have hp : upperPayment 328 = (405493844680:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 328+point split endpoint 4096 329)/2 = (584413327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584413327:ℝ)/168755200)*ClassicalSixthBranch.v ((584413327:ℝ)/168755200)/ClassicalSixthBranch.r = (154530358918257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_328
  · change upperPayment 329 ≤ upperValue ((point split endpoint 4096 329+point split endpoint 4096 330)/2)
    have hp : upperPayment 329 = (405433327221:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 329+point split endpoint 4096 330)/2 = (584438477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584438477:ℝ)/168755200)*ClassicalSixthBranch.v ((584438477:ℝ)/168755200)/ClassicalSixthBranch.r = (154505007521081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_329
  · change upperPayment 330 ≤ upperValue ((point split endpoint 4096 330+point split endpoint 4096 331)/2)
    have hp : upperPayment 330 = (405372789759:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 330+point split endpoint 4096 331)/2 = (584463627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584463627:ℝ)/168755200)*ClassicalSixthBranch.v ((584463627:ℝ)/168755200)/ClassicalSixthBranch.r = (154479658147977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_330
  · change upperPayment 331 ≤ upperValue ((point split endpoint 4096 331+point split endpoint 4096 332)/2)
    have hp : upperPayment 331 = (405312232292:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 331+point split endpoint 4096 332)/2 = (584488777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584488777:ℝ)/168755200)*ClassicalSixthBranch.v ((584488777:ℝ)/168755200)/ClassicalSixthBranch.r = (154454310798945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_331
  · change upperPayment 332 ≤ upperValue ((point split endpoint 4096 332+point split endpoint 4096 333)/2)
    have hp : upperPayment 332 = (405251654816:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 332+point split endpoint 4096 333)/2 = (584513927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584513927:ℝ)/168755200)*ClassicalSixthBranch.v ((584513927:ℝ)/168755200)/ClassicalSixthBranch.r = (154428965473985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_332
  · change upperPayment 333 ≤ upperValue ((point split endpoint 4096 333+point split endpoint 4096 334)/2)
    have hp : upperPayment 333 = (405191057330:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 333+point split endpoint 4096 334)/2 = (584539077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584539077:ℝ)/168755200)*ClassicalSixthBranch.v ((584539077:ℝ)/168755200)/ClassicalSixthBranch.r = (154403622173097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_333
  · change upperPayment 334 ≤ upperValue ((point split endpoint 4096 334+point split endpoint 4096 335)/2)
    have hp : upperPayment 334 = (405130439830:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 334+point split endpoint 4096 335)/2 = (584564227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584564227:ℝ)/168755200)*ClassicalSixthBranch.v ((584564227:ℝ)/168755200)/ClassicalSixthBranch.r = (154378280896281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_334
  · change upperPayment 335 ≤ upperValue ((point split endpoint 4096 335+point split endpoint 4096 336)/2)
    have hp : upperPayment 335 = (405069802315:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 335+point split endpoint 4096 336)/2 = (584589377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584589377:ℝ)/168755200)*ClassicalSixthBranch.v ((584589377:ℝ)/168755200)/ClassicalSixthBranch.r = (154352941643537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_335
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_020
