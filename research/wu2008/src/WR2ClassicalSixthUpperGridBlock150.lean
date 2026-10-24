import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints150
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_150 (j : Fin 16) : upperPayment (16*150+j.val) ≤
    upperValue ((point split endpoint 4096 (16*150+j.val)+point split endpoint 4096 (16*150+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2400 ≤ upperValue ((point split endpoint 4096 2400+point split endpoint 4096 2401)/2)
    have hp : upperPayment 2400 = (232411823333:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2400+point split endpoint 4096 2401)/2 = (636524127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636524127:ℝ)/168755200)*ClassicalSixthBranch.v ((636524127:ℝ)/168755200)/ClassicalSixthBranch.r = (106345023793617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2400
  · change upperPayment 2401 ≤ upperValue ((point split endpoint 4096 2401+point split endpoint 4096 2402)/2)
    have hp : upperPayment 2401 = (232302353946:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2401+point split endpoint 4096 2402)/2 = (636549277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636549277:ℝ)/168755200)*ClassicalSixthBranch.v ((636549277:ℝ)/168755200)/ClassicalSixthBranch.r = (106323866273625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2401
  · change upperPayment 2402 ≤ upperValue ((point split endpoint 4096 2402+point split endpoint 4096 2403)/2)
    have hp : upperPayment 2402 = (232192856086:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2402+point split endpoint 4096 2403)/2 = (636574427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636574427:ℝ)/168755200)*ClassicalSixthBranch.v ((636574427:ℝ)/168755200)/ClassicalSixthBranch.r = (106302710777705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2402
  · change upperPayment 2403 ≤ upperValue ((point split endpoint 4096 2403+point split endpoint 4096 2404)/2)
    have hp : upperPayment 2403 = (232083329746:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2403+point split endpoint 4096 2404)/2 = (636599577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636599577:ℝ)/168755200)*ClassicalSixthBranch.v ((636599577:ℝ)/168755200)/ClassicalSixthBranch.r = (106281557305857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2403
  · change upperPayment 2404 ≤ upperValue ((point split endpoint 4096 2404+point split endpoint 4096 2405)/2)
    have hp : upperPayment 2404 = (231973774922:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2404+point split endpoint 4096 2405)/2 = (636624727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636624727:ℝ)/168755200)*ClassicalSixthBranch.v ((636624727:ℝ)/168755200)/ClassicalSixthBranch.r = (106260405858081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2404
  · change upperPayment 2405 ≤ upperValue ((point split endpoint 4096 2405+point split endpoint 4096 2406)/2)
    have hp : upperPayment 2405 = (231864191607:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2405+point split endpoint 4096 2406)/2 = (636649877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636649877:ℝ)/168755200)*ClassicalSixthBranch.v ((636649877:ℝ)/168755200)/ClassicalSixthBranch.r = (106239256434377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2405
  · change upperPayment 2406 ≤ upperValue ((point split endpoint 4096 2406+point split endpoint 4096 2407)/2)
    have hp : upperPayment 2406 = (231754579794:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2406+point split endpoint 4096 2407)/2 = (636675027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636675027:ℝ)/168755200)*ClassicalSixthBranch.v ((636675027:ℝ)/168755200)/ClassicalSixthBranch.r = (106218109034745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2406
  · change upperPayment 2407 ≤ upperValue ((point split endpoint 4096 2407+point split endpoint 4096 2408)/2)
    have hp : upperPayment 2407 = (231644939479:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2407+point split endpoint 4096 2408)/2 = (636700177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636700177:ℝ)/168755200)*ClassicalSixthBranch.v ((636700177:ℝ)/168755200)/ClassicalSixthBranch.r = (106196963659185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2407
  · change upperPayment 2408 ≤ upperValue ((point split endpoint 4096 2408+point split endpoint 4096 2409)/2)
    have hp : upperPayment 2408 = (231535270654:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2408+point split endpoint 4096 2409)/2 = (636725327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636725327:ℝ)/168755200)*ClassicalSixthBranch.v ((636725327:ℝ)/168755200)/ClassicalSixthBranch.r = (106175820307697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2408
  · change upperPayment 2409 ≤ upperValue ((point split endpoint 4096 2409+point split endpoint 4096 2410)/2)
    have hp : upperPayment 2409 = (231425573313:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2409+point split endpoint 4096 2410)/2 = (636750477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636750477:ℝ)/168755200)*ClassicalSixthBranch.v ((636750477:ℝ)/168755200)/ClassicalSixthBranch.r = (106154678980281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2409
  · change upperPayment 2410 ≤ upperValue ((point split endpoint 4096 2410+point split endpoint 4096 2411)/2)
    have hp : upperPayment 2410 = (231315847451:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2410+point split endpoint 4096 2411)/2 = (636775627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636775627:ℝ)/168755200)*ClassicalSixthBranch.v ((636775627:ℝ)/168755200)/ClassicalSixthBranch.r = (106133539676937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2410
  · change upperPayment 2411 ≤ upperValue ((point split endpoint 4096 2411+point split endpoint 4096 2412)/2)
    have hp : upperPayment 2411 = (231206093061:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2411+point split endpoint 4096 2412)/2 = (636800777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636800777:ℝ)/168755200)*ClassicalSixthBranch.v ((636800777:ℝ)/168755200)/ClassicalSixthBranch.r = (106112402397665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2411
  · change upperPayment 2412 ≤ upperValue ((point split endpoint 4096 2412+point split endpoint 4096 2413)/2)
    have hp : upperPayment 2412 = (231096310138:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2412+point split endpoint 4096 2413)/2 = (636825927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636825927:ℝ)/168755200)*ClassicalSixthBranch.v ((636825927:ℝ)/168755200)/ClassicalSixthBranch.r = (106091267142465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2412
  · change upperPayment 2413 ≤ upperValue ((point split endpoint 4096 2413+point split endpoint 4096 2414)/2)
    have hp : upperPayment 2413 = (230986498675:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2413+point split endpoint 4096 2414)/2 = (636851077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636851077:ℝ)/168755200)*ClassicalSixthBranch.v ((636851077:ℝ)/168755200)/ClassicalSixthBranch.r = (106070133911337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2413
  · change upperPayment 2414 ≤ upperValue ((point split endpoint 4096 2414+point split endpoint 4096 2415)/2)
    have hp : upperPayment 2414 = (230876658665:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2414+point split endpoint 4096 2415)/2 = (636876227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636876227:ℝ)/168755200)*ClassicalSixthBranch.v ((636876227:ℝ)/168755200)/ClassicalSixthBranch.r = (106049002704281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2414
  · change upperPayment 2415 ≤ upperValue ((point split endpoint 4096 2415+point split endpoint 4096 2416)/2)
    have hp : upperPayment 2415 = (230766790104:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2415+point split endpoint 4096 2416)/2 = (636901377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636901377:ℝ)/168755200)*ClassicalSixthBranch.v ((636901377:ℝ)/168755200)/ClassicalSixthBranch.r = (106027873521297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2415
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_150
