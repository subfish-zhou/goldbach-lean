import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints148
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_148 (j : Fin 16) : upperPayment (16*148+j.val) ≤
    upperValue ((point split endpoint 4096 (16*148+j.val)+point split endpoint 4096 (16*148+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2368 ≤ upperValue ((point split endpoint 4096 2368+point split endpoint 4096 2369)/2)
    have hp : upperPayment 2368 = (235899846346:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2368+point split endpoint 4096 2369)/2 = (635719327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635719327:ℝ)/168755200)*ClassicalSixthBranch.v ((635719327:ℝ)/168755200)/ClassicalSixthBranch.r = (107023133143377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2368
  · change upperPayment 2369 ≤ upperValue ((point split endpoint 4096 2369+point split endpoint 4096 2370)/2)
    have hp : upperPayment 2369 = (235791284893:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2369+point split endpoint 4096 2370)/2 = (635744477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635744477:ℝ)/168755200)*ClassicalSixthBranch.v ((635744477:ℝ)/168755200)/ClassicalSixthBranch.r = (107001910853081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2369
  · change upperPayment 2370 ≤ upperValue ((point split endpoint 4096 2370+point split endpoint 4096 2371)/2)
    have hp : upperPayment 2370 = (235682695160:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2370+point split endpoint 4096 2371)/2 = (635769627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635769627:ℝ)/168755200)*ClassicalSixthBranch.v ((635769627:ℝ)/168755200)/ClassicalSixthBranch.r = (106980690586857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2370
  · change upperPayment 2371 ≤ upperValue ((point split endpoint 4096 2371+point split endpoint 4096 2372)/2)
    have hp : upperPayment 2371 = (235574077141:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2371+point split endpoint 4096 2372)/2 = (635794777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635794777:ℝ)/168755200)*ClassicalSixthBranch.v ((635794777:ℝ)/168755200)/ClassicalSixthBranch.r = (106959472344705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2371
  · change upperPayment 2372 ≤ upperValue ((point split endpoint 4096 2372+point split endpoint 4096 2373)/2)
    have hp : upperPayment 2372 = (235465430831:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2372+point split endpoint 4096 2373)/2 = (6173009:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((6173009:ℝ)/1638400)*ClassicalSixthBranch.v ((6173009:ℝ)/1638400)/ClassicalSixthBranch.r = (1038235496375:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2372
  · change upperPayment 2373 ≤ upperValue ((point split endpoint 4096 2373+point split endpoint 4096 2374)/2)
    have hp : upperPayment 2373 = (235356756223:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2373+point split endpoint 4096 2374)/2 = (635845077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635845077:ℝ)/168755200)*ClassicalSixthBranch.v ((635845077:ℝ)/168755200)/ClassicalSixthBranch.r = (106917041932617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2373
  · change upperPayment 2374 ≤ upperValue ((point split endpoint 4096 2374+point split endpoint 4096 2375)/2)
    have hp : upperPayment 2374 = (235248053312:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2374+point split endpoint 4096 2375)/2 = (635870227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635870227:ℝ)/168755200)*ClassicalSixthBranch.v ((635870227:ℝ)/168755200)/ClassicalSixthBranch.r = (106895829762681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2374
  · change upperPayment 2375 ≤ upperValue ((point split endpoint 4096 2375+point split endpoint 4096 2376)/2)
    have hp : upperPayment 2375 = (235139322091:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2375+point split endpoint 4096 2376)/2 = (635895377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635895377:ℝ)/168755200)*ClassicalSixthBranch.v ((635895377:ℝ)/168755200)/ClassicalSixthBranch.r = (106874619616817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2375
  · change upperPayment 2376 ≤ upperValue ((point split endpoint 4096 2376+point split endpoint 4096 2377)/2)
    have hp : upperPayment 2376 = (235030562555:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2376+point split endpoint 4096 2377)/2 = (635920527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635920527:ℝ)/168755200)*ClassicalSixthBranch.v ((635920527:ℝ)/168755200)/ClassicalSixthBranch.r = (106853411495025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2376
  · change upperPayment 2377 ≤ upperValue ((point split endpoint 4096 2377+point split endpoint 4096 2378)/2)
    have hp : upperPayment 2377 = (234921774697:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2377+point split endpoint 4096 2378)/2 = (635945677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635945677:ℝ)/168755200)*ClassicalSixthBranch.v ((635945677:ℝ)/168755200)/ClassicalSixthBranch.r = (106832205397305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2377
  · change upperPayment 2378 ≤ upperValue ((point split endpoint 4096 2378+point split endpoint 4096 2379)/2)
    have hp : upperPayment 2378 = (234812958511:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2378+point split endpoint 4096 2379)/2 = (635970827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635970827:ℝ)/168755200)*ClassicalSixthBranch.v ((635970827:ℝ)/168755200)/ClassicalSixthBranch.r = (106811001323657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2378
  · change upperPayment 2379 ≤ upperValue ((point split endpoint 4096 2379+point split endpoint 4096 2380)/2)
    have hp : upperPayment 2379 = (234704113992:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2379+point split endpoint 4096 2380)/2 = (635995977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635995977:ℝ)/168755200)*ClassicalSixthBranch.v ((635995977:ℝ)/168755200)/ClassicalSixthBranch.r = (106789799274081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2379
  · change upperPayment 2380 ≤ upperValue ((point split endpoint 4096 2380+point split endpoint 4096 2381)/2)
    have hp : upperPayment 2380 = (234595241134:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2380+point split endpoint 4096 2381)/2 = (636021127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636021127:ℝ)/168755200)*ClassicalSixthBranch.v ((636021127:ℝ)/168755200)/ClassicalSixthBranch.r = (106768599248577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2380
  · change upperPayment 2381 ≤ upperValue ((point split endpoint 4096 2381+point split endpoint 4096 2382)/2)
    have hp : upperPayment 2381 = (234486339929:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2381+point split endpoint 4096 2382)/2 = (636046277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636046277:ℝ)/168755200)*ClassicalSixthBranch.v ((636046277:ℝ)/168755200)/ClassicalSixthBranch.r = (106747401247145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2381
  · change upperPayment 2382 ≤ upperValue ((point split endpoint 4096 2382+point split endpoint 4096 2383)/2)
    have hp : upperPayment 2382 = (234377410373:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2382+point split endpoint 4096 2383)/2 = (636071427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636071427:ℝ)/168755200)*ClassicalSixthBranch.v ((636071427:ℝ)/168755200)/ClassicalSixthBranch.r = (106726205269785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2382
  · change upperPayment 2383 ≤ upperValue ((point split endpoint 4096 2383+point split endpoint 4096 2384)/2)
    have hp : upperPayment 2383 = (234268452459:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2383+point split endpoint 4096 2384)/2 = (636096577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636096577:ℝ)/168755200)*ClassicalSixthBranch.v ((636096577:ℝ)/168755200)/ClassicalSixthBranch.r = (106705011316497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2383
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_148
