import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints023
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_023 (j : Fin 16) : upperPayment (16*23+j.val) ≤
    upperValue ((point split endpoint 4096 (16*23+j.val)+point split endpoint 4096 (16*23+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 368 ≤ upperValue ((point split endpoint 4096 368+point split endpoint 4096 369)/2)
    have hp : upperPayment 368 = (403057519050:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 368+point split endpoint 4096 369)/2 = (585419327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585419327:ℝ)/168755200)*ClassicalSixthBranch.v ((585419327:ℝ)/168755200)/ClassicalSixthBranch.r = (153517881807377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_368
  · change upperPayment 369 ≤ upperValue ((point split endpoint 4096 369+point split endpoint 4096 370)/2)
    have hp : upperPayment 369 = (402996199502:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 369+point split endpoint 4096 370)/2 = (585444477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585444477:ℝ)/168755200)*ClassicalSixthBranch.v ((585444477:ℝ)/168755200)/ClassicalSixthBranch.r = (153492611373081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_369
  · change upperPayment 370 ≤ upperValue ((point split endpoint 4096 370+point split endpoint 4096 371)/2)
    have hp : upperPayment 370 = (402934859851:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 370+point split endpoint 4096 371)/2 = (585469627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585469627:ℝ)/168755200)*ClassicalSixthBranch.v ((585469627:ℝ)/168755200)/ClassicalSixthBranch.r = (153467342962857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_370
  · change upperPayment 371 ≤ upperValue ((point split endpoint 4096 371+point split endpoint 4096 372)/2)
    have hp : upperPayment 371 = (402873500093:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 371+point split endpoint 4096 372)/2 = (585494777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585494777:ℝ)/168755200)*ClassicalSixthBranch.v ((585494777:ℝ)/168755200)/ClassicalSixthBranch.r = (153442076576705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_371
  · change upperPayment 372 ≤ upperValue ((point split endpoint 4096 372+point split endpoint 4096 373)/2)
    have hp : upperPayment 372 = (402812120226:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 372+point split endpoint 4096 373)/2 = (585519927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585519927:ℝ)/168755200)*ClassicalSixthBranch.v ((585519927:ℝ)/168755200)/ClassicalSixthBranch.r = (153416812214625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_372
  · change upperPayment 373 ≤ upperValue ((point split endpoint 4096 373+point split endpoint 4096 374)/2)
    have hp : upperPayment 373 = (402750720247:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 373+point split endpoint 4096 374)/2 = (585545077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585545077:ℝ)/168755200)*ClassicalSixthBranch.v ((585545077:ℝ)/168755200)/ClassicalSixthBranch.r = (153391549876617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_373
  · change upperPayment 374 ≤ upperValue ((point split endpoint 4096 374+point split endpoint 4096 375)/2)
    have hp : upperPayment 374 = (402689300153:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 374+point split endpoint 4096 375)/2 = (585570227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585570227:ℝ)/168755200)*ClassicalSixthBranch.v ((585570227:ℝ)/168755200)/ClassicalSixthBranch.r = (153366289562681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_374
  · change upperPayment 375 ≤ upperValue ((point split endpoint 4096 375+point split endpoint 4096 376)/2)
    have hp : upperPayment 375 = (402627859943:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 375+point split endpoint 4096 376)/2 = (585595377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585595377:ℝ)/168755200)*ClassicalSixthBranch.v ((585595377:ℝ)/168755200)/ClassicalSixthBranch.r = (153341031272817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_375
  · change upperPayment 376 ≤ upperValue ((point split endpoint 4096 376+point split endpoint 4096 377)/2)
    have hp : upperPayment 376 = (402566399614:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 376+point split endpoint 4096 377)/2 = (585620527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585620527:ℝ)/168755200)*ClassicalSixthBranch.v ((585620527:ℝ)/168755200)/ClassicalSixthBranch.r = (153315775007025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_376
  · change upperPayment 377 ≤ upperValue ((point split endpoint 4096 377+point split endpoint 4096 378)/2)
    have hp : upperPayment 377 = (402504919162:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 377+point split endpoint 4096 378)/2 = (585645677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585645677:ℝ)/168755200)*ClassicalSixthBranch.v ((585645677:ℝ)/168755200)/ClassicalSixthBranch.r = (153290520765305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_377
  · change upperPayment 378 ≤ upperValue ((point split endpoint 4096 378+point split endpoint 4096 379)/2)
    have hp : upperPayment 378 = (402443418586:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 378+point split endpoint 4096 379)/2 = (585670827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585670827:ℝ)/168755200)*ClassicalSixthBranch.v ((585670827:ℝ)/168755200)/ClassicalSixthBranch.r = (153265268547657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_378
  · change upperPayment 379 ≤ upperValue ((point split endpoint 4096 379+point split endpoint 4096 380)/2)
    have hp : upperPayment 379 = (402381897883:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 379+point split endpoint 4096 380)/2 = (585695977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585695977:ℝ)/168755200)*ClassicalSixthBranch.v ((585695977:ℝ)/168755200)/ClassicalSixthBranch.r = (153240018354081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_379
  · change upperPayment 380 ≤ upperValue ((point split endpoint 4096 380+point split endpoint 4096 381)/2)
    have hp : upperPayment 380 = (402320357050:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 380+point split endpoint 4096 381)/2 = (585721127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585721127:ℝ)/168755200)*ClassicalSixthBranch.v ((585721127:ℝ)/168755200)/ClassicalSixthBranch.r = (153214770184577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_380
  · change upperPayment 381 ≤ upperValue ((point split endpoint 4096 381+point split endpoint 4096 382)/2)
    have hp : upperPayment 381 = (402258796085:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 381+point split endpoint 4096 382)/2 = (585746277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585746277:ℝ)/168755200)*ClassicalSixthBranch.v ((585746277:ℝ)/168755200)/ClassicalSixthBranch.r = (153189524039145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_381
  · change upperPayment 382 ≤ upperValue ((point split endpoint 4096 382+point split endpoint 4096 383)/2)
    have hp : upperPayment 382 = (402197214985:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 382+point split endpoint 4096 383)/2 = (585771427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585771427:ℝ)/168755200)*ClassicalSixthBranch.v ((585771427:ℝ)/168755200)/ClassicalSixthBranch.r = (153164279917785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_382
  · change upperPayment 383 ≤ upperValue ((point split endpoint 4096 383+point split endpoint 4096 384)/2)
    have hp : upperPayment 383 = (402135613748:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 383+point split endpoint 4096 384)/2 = (585796577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585796577:ℝ)/168755200)*ClassicalSixthBranch.v ((585796577:ℝ)/168755200)/ClassicalSixthBranch.r = (153139037820497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_383
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_023
