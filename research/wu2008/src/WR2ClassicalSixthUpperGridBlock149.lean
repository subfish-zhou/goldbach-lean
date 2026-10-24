import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints149
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_149 (j : Fin 16) : upperPayment (16*149+j.val) ≤
    upperValue ((point split endpoint 4096 (16*149+j.val)+point split endpoint 4096 (16*149+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2384 ≤ upperValue ((point split endpoint 4096 2384+point split endpoint 4096 2385)/2)
    have hp : upperPayment 2384 = (234159466182:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2384+point split endpoint 4096 2385)/2 = (636121727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636121727:ℝ)/168755200)*ClassicalSixthBranch.v ((636121727:ℝ)/168755200)/ClassicalSixthBranch.r = (106683819387281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2384
  · change upperPayment 2385 ≤ upperValue ((point split endpoint 4096 2385+point split endpoint 4096 2386)/2)
    have hp : upperPayment 2385 = (234050451534:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2385+point split endpoint 4096 2386)/2 = (636146877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636146877:ℝ)/168755200)*ClassicalSixthBranch.v ((636146877:ℝ)/168755200)/ClassicalSixthBranch.r = (106662629482137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2385
  · change upperPayment 2386 ≤ upperValue ((point split endpoint 4096 2386+point split endpoint 4096 2387)/2)
    have hp : upperPayment 2386 = (233941408511:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2386+point split endpoint 4096 2387)/2 = (636172027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636172027:ℝ)/168755200)*ClassicalSixthBranch.v ((636172027:ℝ)/168755200)/ClassicalSixthBranch.r = (106641441601065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2386
  · change upperPayment 2387 ≤ upperValue ((point split endpoint 4096 2387+point split endpoint 4096 2388)/2)
    have hp : upperPayment 2387 = (233832337106:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2387+point split endpoint 4096 2388)/2 = (636197177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636197177:ℝ)/168755200)*ClassicalSixthBranch.v ((636197177:ℝ)/168755200)/ClassicalSixthBranch.r = (106620255744065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2387
  · change upperPayment 2388 ≤ upperValue ((point split endpoint 4096 2388+point split endpoint 4096 2389)/2)
    have hp : upperPayment 2388 = (233723237313:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2388+point split endpoint 4096 2389)/2 = (636222327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636222327:ℝ)/168755200)*ClassicalSixthBranch.v ((636222327:ℝ)/168755200)/ClassicalSixthBranch.r = (106599071911137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2388
  · change upperPayment 2389 ≤ upperValue ((point split endpoint 4096 2389+point split endpoint 4096 2390)/2)
    have hp : upperPayment 2389 = (233614109126:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2389+point split endpoint 4096 2390)/2 = (636247477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636247477:ℝ)/168755200)*ClassicalSixthBranch.v ((636247477:ℝ)/168755200)/ClassicalSixthBranch.r = (106577890102281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2389
  · change upperPayment 2390 ≤ upperValue ((point split endpoint 4096 2390+point split endpoint 4096 2391)/2)
    have hp : upperPayment 2390 = (233504952539:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2390+point split endpoint 4096 2391)/2 = (636272627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636272627:ℝ)/168755200)*ClassicalSixthBranch.v ((636272627:ℝ)/168755200)/ClassicalSixthBranch.r = (106556710317497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2390
  · change upperPayment 2391 ≤ upperValue ((point split endpoint 4096 2391+point split endpoint 4096 2392)/2)
    have hp : upperPayment 2391 = (233395767546:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2391+point split endpoint 4096 2392)/2 = (636297777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636297777:ℝ)/168755200)*ClassicalSixthBranch.v ((636297777:ℝ)/168755200)/ClassicalSixthBranch.r = (106535532556785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2391
  · change upperPayment 2392 ≤ upperValue ((point split endpoint 4096 2392+point split endpoint 4096 2393)/2)
    have hp : upperPayment 2392 = (233286554140:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2392+point split endpoint 4096 2393)/2 = (636322927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636322927:ℝ)/168755200)*ClassicalSixthBranch.v ((636322927:ℝ)/168755200)/ClassicalSixthBranch.r = (106514356820145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2392
  · change upperPayment 2393 ≤ upperValue ((point split endpoint 4096 2393+point split endpoint 4096 2394)/2)
    have hp : upperPayment 2393 = (233177312317:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2393+point split endpoint 4096 2394)/2 = (636348077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636348077:ℝ)/168755200)*ClassicalSixthBranch.v ((636348077:ℝ)/168755200)/ClassicalSixthBranch.r = (106493183107577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2393
  · change upperPayment 2394 ≤ upperValue ((point split endpoint 4096 2394+point split endpoint 4096 2395)/2)
    have hp : upperPayment 2394 = (233068042069:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2394+point split endpoint 4096 2395)/2 = (636373227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636373227:ℝ)/168755200)*ClassicalSixthBranch.v ((636373227:ℝ)/168755200)/ClassicalSixthBranch.r = (106472011419081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2394
  · change upperPayment 2395 ≤ upperValue ((point split endpoint 4096 2395+point split endpoint 4096 2396)/2)
    have hp : upperPayment 2395 = (232958743391:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2395+point split endpoint 4096 2396)/2 = (636398377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636398377:ℝ)/168755200)*ClassicalSixthBranch.v ((636398377:ℝ)/168755200)/ClassicalSixthBranch.r = (106450841754657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2395
  · change upperPayment 2396 ≤ upperValue ((point split endpoint 4096 2396+point split endpoint 4096 2397)/2)
    have hp : upperPayment 2396 = (232849416276:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2396+point split endpoint 4096 2397)/2 = (636423527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636423527:ℝ)/168755200)*ClassicalSixthBranch.v ((636423527:ℝ)/168755200)/ClassicalSixthBranch.r = (1033297806935:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2396
  · change upperPayment 2397 ≤ upperValue ((point split endpoint 4096 2397+point split endpoint 4096 2398)/2)
    have hp : upperPayment 2397 = (232740060720:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2397+point split endpoint 4096 2398)/2 = (636448677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636448677:ℝ)/168755200)*ClassicalSixthBranch.v ((636448677:ℝ)/168755200)/ClassicalSixthBranch.r = (106408508498025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2397
  · change upperPayment 2398 ≤ upperValue ((point split endpoint 4096 2398+point split endpoint 4096 2399)/2)
    have hp : upperPayment 2398 = (232630676714:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2398+point split endpoint 4096 2399)/2 = (636473827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636473827:ℝ)/168755200)*ClassicalSixthBranch.v ((636473827:ℝ)/168755200)/ClassicalSixthBranch.r = (106387344905817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2398
  · change upperPayment 2399 ≤ upperValue ((point split endpoint 4096 2399+point split endpoint 4096 2400)/2)
    have hp : upperPayment 2399 = (232521264254:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2399+point split endpoint 4096 2400)/2 = (636498977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636498977:ℝ)/168755200)*ClassicalSixthBranch.v ((636498977:ℝ)/168755200)/ClassicalSixthBranch.r = (106366183337681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2399
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_149
