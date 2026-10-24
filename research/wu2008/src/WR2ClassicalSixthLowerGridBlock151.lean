import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints151
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_151 (j : Fin 16) : lowerPayment (16*151+j.val) ≤
    lowerValue ((point 2 split 4096 (16*151+j.val)+point 2 split 4096 (16*151+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2416 ≤ lowerValue ((point 2 split 4096 2416+point 2 split 4096 2417)/2)
    have hp : lowerPayment 2416 = (269912433316:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2416+point 2 split 4096 2417)/2 = (478300523:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((478300523:ℝ)/168755200)/ClassicalSixthBranch.v ((478300523:ℝ)/168755200) = (627186683483:ℝ)/304567398296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2416
  · change lowerPayment 2417 ≤ lowerValue ((point 2 split 4096 2417+point 2 split 4096 2418)/2)
    have hp : lowerPayment 2417 = (270000650463:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2417+point 2 split 4096 2418)/2 = (95671757:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((95671757:ℝ)/33751040)/ClassicalSixthBranch.v ((95671757:ℝ)/33751040) = (627109369809:ℝ)/304519390408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2417
  · change lowerPayment 2418 ≤ lowerValue ((point 2 split 4096 2418+point 2 split 4096 2419)/2)
    have hp : lowerPayment 2418 = (270088863943:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2418+point 2 split 4096 2419)/2 = (478417047:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((478417047:ℝ)/168755200)/ClassicalSixthBranch.v ((478417047:ℝ)/168755200) = (125406411227:ℝ)/60894276504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2418
  · change lowerPayment 2419 ≤ lowerValue ((point 2 split 4096 2419+point 2 split 4096 2420)/2)
    have hp : lowerPayment 2419 = (270177073771:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2419+point 2 split 4096 2420)/2 = (478475309:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((478475309:ℝ)/168755200)/ClassicalSixthBranch.v ((478475309:ℝ)/168755200) = (626954742461:ℝ)/304423374632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2419
  · change lowerPayment 2420 ≤ lowerValue ((point 2 split 4096 2420+point 2 split 4096 2421)/2)
    have hp : lowerPayment 2420 = (270265279962:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2420+point 2 split 4096 2421)/2 = (4645957:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((4645957:ℝ)/1638400)/ClassicalSixthBranch.v ((4645957:ℝ)/1638400) = (6086188629:ℝ)/2955100648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2420
  · change lowerPayment 2421 ≤ lowerValue ((point 2 split 4096 2421+point 2 split 4096 2422)/2)
    have hp : lowerPayment 2421 = (270353482529:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2421+point 2 split 4096 2422)/2 = (478591833:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((478591833:ℝ)/168755200)/ClassicalSixthBranch.v ((478591833:ℝ)/168755200) = (626800115113:ℝ)/304327358856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2421
  · change lowerPayment 2422 ≤ lowerValue ((point 2 split 4096 2422+point 2 split 4096 2423)/2)
    have hp : lowerPayment 2422 = (270441681489:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2422+point 2 split 4096 2423)/2 = (95730019:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((95730019:ℝ)/33751040)/ClassicalSixthBranch.v ((95730019:ℝ)/33751040) = (626722801439:ℝ)/304279350968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2422
  · change lowerPayment 2423 ≤ lowerValue ((point 2 split 4096 2423+point 2 split 4096 2424)/2)
    have hp : lowerPayment 2423 = (270529876855:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2423+point 2 split 4096 2424)/2 = (478708357:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((478708357:ℝ)/168755200)/ClassicalSixthBranch.v ((478708357:ℝ)/168755200) = (125329097553:ℝ)/60846268616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2423
  · change lowerPayment 2424 ≤ lowerValue ((point 2 split 4096 2424+point 2 split 4096 2425)/2)
    have hp : lowerPayment 2424 = (270618068643:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2424+point 2 split 4096 2425)/2 = (478766619:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((478766619:ℝ)/168755200)/ClassicalSixthBranch.v ((478766619:ℝ)/168755200) = (626568174091:ℝ)/304183335192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2424
  · change lowerPayment 2425 ≤ lowerValue ((point 2 split 4096 2425+point 2 split 4096 2426)/2)
    have hp : lowerPayment 2425 = (270706256867:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2425+point 2 split 4096 2426)/2 = (478824881:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((478824881:ℝ)/168755200)/ClassicalSixthBranch.v ((478824881:ℝ)/168755200) = (626490860417:ℝ)/304135327304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2425
  · change lowerPayment 2426 ≤ lowerValue ((point 2 split 4096 2426+point 2 split 4096 2427)/2)
    have hp : lowerPayment 2426 = (270794441542:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2426+point 2 split 4096 2427)/2 = (478883143:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((478883143:ℝ)/168755200)/ClassicalSixthBranch.v ((478883143:ℝ)/168755200) = (626413546743:ℝ)/304087319416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2426
  · change lowerPayment 2427 ≤ lowerValue ((point 2 split 4096 2427+point 2 split 4096 2428)/2)
    have hp : lowerPayment 2427 = (270882622683:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2427+point 2 split 4096 2428)/2 = (95788281:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((95788281:ℝ)/33751040)/ClassicalSixthBranch.v ((95788281:ℝ)/33751040) = (626336233069:ℝ)/304039311528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2427
  · change lowerPayment 2428 ≤ lowerValue ((point 2 split 4096 2428+point 2 split 4096 2429)/2)
    have hp : lowerPayment 2428 = (270970800304:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2428+point 2 split 4096 2429)/2 = (478999667:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((478999667:ℝ)/168755200)/ClassicalSixthBranch.v ((478999667:ℝ)/168755200) = (125251783879:ℝ)/60798260728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2428
  · change lowerPayment 2429 ≤ lowerValue ((point 2 split 4096 2429+point 2 split 4096 2430)/2)
    have hp : lowerPayment 2429 = (271058974421:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2429+point 2 split 4096 2430)/2 = (479057929:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((479057929:ℝ)/168755200)/ClassicalSixthBranch.v ((479057929:ℝ)/168755200) = (626181605721:ℝ)/303943295752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2429
  · change lowerPayment 2430 ≤ lowerValue ((point 2 split 4096 2430+point 2 split 4096 2431)/2)
    have hp : lowerPayment 2430 = (271147145047:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2430+point 2 split 4096 2431)/2 = (479116191:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((479116191:ℝ)/168755200)/ClassicalSixthBranch.v ((479116191:ℝ)/168755200) = (626104292047:ℝ)/303895287864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2430
  · change lowerPayment 2431 ≤ lowerValue ((point 2 split 4096 2431+point 2 split 4096 2432)/2)
    have hp : lowerPayment 2431 = (271235312198:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2431+point 2 split 4096 2432)/2 = (479174453:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((479174453:ℝ)/168755200)/ClassicalSixthBranch.v ((479174453:ℝ)/168755200) = (626026978373:ℝ)/303847279976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2431
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_151
