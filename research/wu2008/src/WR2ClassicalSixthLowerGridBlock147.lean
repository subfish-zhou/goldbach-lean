import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints147
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_147 (j : Fin 16) : lowerPayment (16*147+j.val) ≤
    lowerValue ((point 2 split 4096 (16*147+j.val)+point 2 split 4096 (16*147+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2352 ≤ lowerValue ((point 2 split 4096 2352+point 2 split 4096 2353)/2)
    have hp : lowerPayment 2352 = (264258230576:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2352+point 2 split 4096 2353)/2 = (94914351:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((94914351:ℝ)/33751040)/ClassicalSixthBranch.v ((94914351:ℝ)/33751040) = (632134758619:ℝ)/307639903128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2352
  · change lowerPayment 2353 ≤ lowerValue ((point 2 split 4096 2353+point 2 split 4096 2354)/2)
    have hp : lowerPayment 2353 = (264346713262:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2353+point 2 split 4096 2354)/2 = (474630017:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((474630017:ℝ)/168755200)/ClassicalSixthBranch.v ((474630017:ℝ)/168755200) = (126411488989:ℝ)/61518379048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2353
  · change lowerPayment 2354 ≤ lowerValue ((point 2 split 4096 2354+point 2 split 4096 2355)/2)
    have hp : lowerPayment 2354 = (264435191330:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2354+point 2 split 4096 2355)/2 = (474688279:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((474688279:ℝ)/168755200)/ClassicalSixthBranch.v ((474688279:ℝ)/168755200) = (631980131271:ℝ)/307543887352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2354
  · change lowerPayment 2355 ≤ lowerValue ((point 2 split 4096 2355+point 2 split 4096 2356)/2)
    have hp : lowerPayment 2355 = (264523664794:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2355+point 2 split 4096 2356)/2 = (474746541:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((474746541:ℝ)/168755200)/ClassicalSixthBranch.v ((474746541:ℝ)/168755200) = (631902817597:ℝ)/307495879464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2355
  · change lowerPayment 2356 ≤ lowerValue ((point 2 split 4096 2356+point 2 split 4096 2357)/2)
    have hp : lowerPayment 2356 = (264612133669:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2356+point 2 split 4096 2357)/2 = (474804803:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((474804803:ℝ)/168755200)/ClassicalSixthBranch.v ((474804803:ℝ)/168755200) = (631825503923:ℝ)/307447871576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2356
  · change lowerPayment 2357 ≤ lowerValue ((point 2 split 4096 2357+point 2 split 4096 2358)/2)
    have hp : lowerPayment 2357 = (264700597971:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2357+point 2 split 4096 2358)/2 = (94972613:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((94972613:ℝ)/33751040)/ClassicalSixthBranch.v ((94972613:ℝ)/33751040) = (631748190249:ℝ)/307399863688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2357
  · change lowerPayment 2358 ≤ lowerValue ((point 2 split 4096 2358+point 2 split 4096 2359)/2)
    have hp : lowerPayment 2358 = (264789057715:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2358+point 2 split 4096 2359)/2 = (474921327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((474921327:ℝ)/168755200)/ClassicalSixthBranch.v ((474921327:ℝ)/168755200) = (25266835063:ℝ)/12294074232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2358
  · change lowerPayment 2359 ≤ lowerValue ((point 2 split 4096 2359+point 2 split 4096 2360)/2)
    have hp : lowerPayment 2359 = (264877512915:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2359+point 2 split 4096 2360)/2 = (474979589:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((474979589:ℝ)/168755200)/ClassicalSixthBranch.v ((474979589:ℝ)/168755200) = (631593562901:ℝ)/307303847912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2359
  · change lowerPayment 2360 ≤ lowerValue ((point 2 split 4096 2360+point 2 split 4096 2361)/2)
    have hp : lowerPayment 2360 = (264965963586:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2360+point 2 split 4096 2361)/2 = (475037851:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((475037851:ℝ)/168755200)/ClassicalSixthBranch.v ((475037851:ℝ)/168755200) = (631516249227:ℝ)/307255840024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2360
  · change lowerPayment 2361 ≤ lowerValue ((point 2 split 4096 2361+point 2 split 4096 2362)/2)
    have hp : lowerPayment 2361 = (265054409744:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2361+point 2 split 4096 2362)/2 = (475096113:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((475096113:ℝ)/168755200)/ClassicalSixthBranch.v ((475096113:ℝ)/168755200) = (631438935553:ℝ)/307207832136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2361
  · change lowerPayment 2362 ≤ lowerValue ((point 2 split 4096 2362+point 2 split 4096 2363)/2)
    have hp : lowerPayment 2362 = (265142851403:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2362+point 2 split 4096 2363)/2 = (19006175:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((19006175:ℝ)/6750208)/ClassicalSixthBranch.v ((19006175:ℝ)/6750208) = (631361621879:ℝ)/307159824248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2362
  · change lowerPayment 2363 ≤ lowerValue ((point 2 split 4096 2363+point 2 split 4096 2364)/2)
    have hp : lowerPayment 2363 = (265231288578:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2363+point 2 split 4096 2364)/2 = (475212637:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((475212637:ℝ)/168755200)/ClassicalSixthBranch.v ((475212637:ℝ)/168755200) = (126256861641:ℝ)/61422363272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2363
  · change lowerPayment 2364 ≤ lowerValue ((point 2 split 4096 2364+point 2 split 4096 2365)/2)
    have hp : lowerPayment 2364 = (265319721284:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2364+point 2 split 4096 2365)/2 = (475270899:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((475270899:ℝ)/168755200)/ClassicalSixthBranch.v ((475270899:ℝ)/168755200) = (631206994531:ℝ)/307063808472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2364
  · change lowerPayment 2365 ≤ lowerValue ((point 2 split 4096 2365+point 2 split 4096 2366)/2)
    have hp : lowerPayment 2365 = (265408149536:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2365+point 2 split 4096 2366)/2 = (475329161:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((475329161:ℝ)/168755200)/ClassicalSixthBranch.v ((475329161:ℝ)/168755200) = (631129680857:ℝ)/307015800584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2365
  · change lowerPayment 2366 ≤ lowerValue ((point 2 split 4096 2366+point 2 split 4096 2367)/2)
    have hp : lowerPayment 2366 = (265496573349:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2366+point 2 split 4096 2367)/2 = (475387423:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((475387423:ℝ)/168755200)/ClassicalSixthBranch.v ((475387423:ℝ)/168755200) = (631052367183:ℝ)/306967792696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2366
  · change lowerPayment 2367 ≤ lowerValue ((point 2 split 4096 2367+point 2 split 4096 2368)/2)
    have hp : lowerPayment 2367 = (265584992738:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2367+point 2 split 4096 2368)/2 = (95089137:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((95089137:ℝ)/33751040)/ClassicalSixthBranch.v ((95089137:ℝ)/33751040) = (630975053509:ℝ)/306919784808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2367
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_147
