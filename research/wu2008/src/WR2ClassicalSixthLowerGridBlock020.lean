import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints020
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_020 (j : Fin 16) : lowerPayment (16*20+j.val) ≤
    lowerValue ((point 2 split 4096 (16*20+j.val)+point 2 split 4096 (16*20+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 320 ≤ lowerValue ((point 2 split 4096 320+point 2 split 4096 321)/2)
    have hp : lowerPayment 320 = (48614970256:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 320+point 2 split 4096 321)/2 = (356183371:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((356183371:ℝ)/168755200)/ClassicalSixthBranch.v ((356183371:ℝ)/168755200) = (789236144187:ℝ)/405191931544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_320
  · change lowerPayment 321 ≤ lowerValue ((point 2 split 4096 321+point 2 split 4096 322)/2)
    have hp : lowerPayment 321 = (48756191459:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 321+point 2 split 4096 322)/2 = (356241633:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((356241633:ℝ)/168755200)/ClassicalSixthBranch.v ((356241633:ℝ)/168755200) = (789158830513:ℝ)/405143923656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_321
  · change lowerPayment 322 ≤ lowerValue ((point 2 split 4096 322+point 2 split 4096 323)/2)
    have hp : lowerPayment 322 = (48897353702:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 322+point 2 split 4096 323)/2 = (71259979:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((71259979:ℝ)/33751040)/ClassicalSixthBranch.v ((71259979:ℝ)/33751040) = (789081516839:ℝ)/405095915768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_322
  · change lowerPayment 323 ≤ lowerValue ((point 2 split 4096 323+point 2 split 4096 324)/2)
    have hp : lowerPayment 323 = (49038457040:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 323+point 2 split 4096 324)/2 = (356358157:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((356358157:ℝ)/168755200)/ClassicalSixthBranch.v ((356358157:ℝ)/168755200) = (157800840633:ℝ)/81009581576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_323
  · change lowerPayment 324 ≤ lowerValue ((point 2 split 4096 324+point 2 split 4096 325)/2)
    have hp : lowerPayment 324 = (49179501524:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 324+point 2 split 4096 325)/2 = (356416419:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((356416419:ℝ)/168755200)/ClassicalSixthBranch.v ((356416419:ℝ)/168755200) = (788926889491:ℝ)/404999899992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_324
  · change lowerPayment 325 ≤ lowerValue ((point 2 split 4096 325+point 2 split 4096 326)/2)
    have hp : lowerPayment 325 = (49320487206:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 325+point 2 split 4096 326)/2 = (356474681:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((356474681:ℝ)/168755200)/ClassicalSixthBranch.v ((356474681:ℝ)/168755200) = (788849575817:ℝ)/404951892104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_325
  · change lowerPayment 326 ≤ lowerValue ((point 2 split 4096 326+point 2 split 4096 327)/2)
    have hp : lowerPayment 326 = (49461414140:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 326+point 2 split 4096 327)/2 = (356532943:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((356532943:ℝ)/168755200)/ClassicalSixthBranch.v ((356532943:ℝ)/168755200) = (788772262143:ℝ)/404903884216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_326
  · change lowerPayment 327 ≤ lowerValue ((point 2 split 4096 327+point 2 split 4096 328)/2)
    have hp : lowerPayment 327 = (49602282378:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 327+point 2 split 4096 328)/2 = (71318241:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((71318241:ℝ)/33751040)/ClassicalSixthBranch.v ((71318241:ℝ)/33751040) = (788694948469:ℝ)/404855876328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_327
  · change lowerPayment 328 ≤ lowerValue ((point 2 split 4096 328+point 2 split 4096 329)/2)
    have hp : lowerPayment 328 = (49743091972:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 328+point 2 split 4096 329)/2 = (356649467:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((356649467:ℝ)/168755200)/ClassicalSixthBranch.v ((356649467:ℝ)/168755200) = (157723526959:ℝ)/80961573688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_328
  · change lowerPayment 329 ≤ lowerValue ((point 2 split 4096 329+point 2 split 4096 330)/2)
    have hp : lowerPayment 329 = (49883842975:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 329+point 2 split 4096 330)/2 = (356707729:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((356707729:ℝ)/168755200)/ClassicalSixthBranch.v ((356707729:ℝ)/168755200) = (788540321121:ℝ)/404759860552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_329
  · change lowerPayment 330 ≤ lowerValue ((point 2 split 4096 330+point 2 split 4096 331)/2)
    have hp : lowerPayment 330 = (50024535438:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 330+point 2 split 4096 331)/2 = (356765991:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((356765991:ℝ)/168755200)/ClassicalSixthBranch.v ((356765991:ℝ)/168755200) = (788463007447:ℝ)/404711852664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_330
  · change lowerPayment 331 ≤ lowerValue ((point 2 split 4096 331+point 2 split 4096 332)/2)
    have hp : lowerPayment 331 = (50165169414:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 331+point 2 split 4096 332)/2 = (356824253:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((356824253:ℝ)/168755200)/ClassicalSixthBranch.v ((356824253:ℝ)/168755200) = (788385693773:ℝ)/404663844776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_331
  · change lowerPayment 332 ≤ lowerValue ((point 2 split 4096 332+point 2 split 4096 333)/2)
    have hp : lowerPayment 332 = (50305744956:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 332+point 2 split 4096 333)/2 = (71376503:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((71376503:ℝ)/33751040)/ClassicalSixthBranch.v ((71376503:ℝ)/33751040) = (788308380099:ℝ)/404615836888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_332
  · change lowerPayment 333 ≤ lowerValue ((point 2 split 4096 333+point 2 split 4096 334)/2)
    have hp : lowerPayment 333 = (50446262114:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 333+point 2 split 4096 334)/2 = (356940777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((356940777:ℝ)/168755200)/ClassicalSixthBranch.v ((356940777:ℝ)/168755200) = (31529242657:ℝ)/16182713160 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_333
  · change lowerPayment 334 ≤ lowerValue ((point 2 split 4096 334+point 2 split 4096 335)/2)
    have hp : lowerPayment 334 = (50586720943:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 334+point 2 split 4096 335)/2 = (356999039:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((356999039:ℝ)/168755200)/ClassicalSixthBranch.v ((356999039:ℝ)/168755200) = (788153752751:ℝ)/404519821112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_334
  · change lowerPayment 335 ≤ lowerValue ((point 2 split 4096 335+point 2 split 4096 336)/2)
    have hp : lowerPayment 335 = (50727121492:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 335+point 2 split 4096 336)/2 = (357057301:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((357057301:ℝ)/168755200)/ClassicalSixthBranch.v ((357057301:ℝ)/168755200) = (788076439077:ℝ)/404471813224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_335
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_020
