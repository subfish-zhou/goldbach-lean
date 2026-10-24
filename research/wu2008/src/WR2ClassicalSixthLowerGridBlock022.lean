import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints022
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_022 (j : Fin 16) : lowerPayment (16*22+j.val) ≤
    lowerValue ((point 2 split 4096 (16*22+j.val)+point 2 split 4096 (16*22+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 352 ≤ lowerValue ((point 2 split 4096 352+point 2 split 4096 353)/2)
    have hp : lowerPayment 352 = (53105064398:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 352+point 2 split 4096 353)/2 = (71609551:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((71609551:ℝ)/33751040)/ClassicalSixthBranch.v ((71609551:ℝ)/33751040) = (786762106619:ℝ)/403655679128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_352
  · change lowerPayment 353 ≤ lowerValue ((point 2 split 4096 353+point 2 split 4096 354)/2)
    have hp : lowerPayment 353 = (53244424775:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 353+point 2 split 4096 354)/2 = (358106017:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((358106017:ℝ)/168755200)/ClassicalSixthBranch.v ((358106017:ℝ)/168755200) = (157336958589:ℝ)/80721534248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_353
  · change lowerPayment 354 ≤ lowerValue ((point 2 split 4096 354+point 2 split 4096 355)/2)
    have hp : lowerPayment 354 = (53383727853:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 354+point 2 split 4096 355)/2 = (358164279:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((358164279:ℝ)/168755200)/ClassicalSixthBranch.v ((358164279:ℝ)/168755200) = (786607479271:ℝ)/403559663352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_354
  · change lowerPayment 355 ≤ lowerValue ((point 2 split 4096 355+point 2 split 4096 356)/2)
    have hp : lowerPayment 355 = (53522973683:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 355+point 2 split 4096 356)/2 = (358222541:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((358222541:ℝ)/168755200)/ClassicalSixthBranch.v ((358222541:ℝ)/168755200) = (786530165597:ℝ)/403511655464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_355
  · change lowerPayment 356 ≤ lowerValue ((point 2 split 4096 356+point 2 split 4096 357)/2)
    have hp : lowerPayment 356 = (53662162315:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 356+point 2 split 4096 357)/2 = (358280803:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((358280803:ℝ)/168755200)/ClassicalSixthBranch.v ((358280803:ℝ)/168755200) = (786452851923:ℝ)/403463647576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_356
  · change lowerPayment 357 ≤ lowerValue ((point 2 split 4096 357+point 2 split 4096 358)/2)
    have hp : lowerPayment 357 = (53801293802:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 357+point 2 split 4096 358)/2 = (71667813:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((71667813:ℝ)/33751040)/ClassicalSixthBranch.v ((71667813:ℝ)/33751040) = (786375538249:ℝ)/403415639688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_357
  · change lowerPayment 358 ≤ lowerValue ((point 2 split 4096 358+point 2 split 4096 359)/2)
    have hp : lowerPayment 358 = (53940368193:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 358+point 2 split 4096 359)/2 = (358397327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((358397327:ℝ)/168755200)/ClassicalSixthBranch.v ((358397327:ℝ)/168755200) = (31451928983:ℝ)/16134705272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_358
  · change lowerPayment 359 ≤ lowerValue ((point 2 split 4096 359+point 2 split 4096 360)/2)
    have hp : lowerPayment 359 = (54079385540:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 359+point 2 split 4096 360)/2 = (358455589:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((358455589:ℝ)/168755200)/ClassicalSixthBranch.v ((358455589:ℝ)/168755200) = (786220910901:ℝ)/403319623912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_359
  · change lowerPayment 360 ≤ lowerValue ((point 2 split 4096 360+point 2 split 4096 361)/2)
    have hp : lowerPayment 360 = (54218345893:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 360+point 2 split 4096 361)/2 = (3480717:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((3480717:ℝ)/1638400)/ClassicalSixthBranch.v ((3480717:ℝ)/1638400) = (7632462109:ℝ)/3915258408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_360
  · change lowerPayment 361 ≤ lowerValue ((point 2 split 4096 361+point 2 split 4096 362)/2)
    have hp : lowerPayment 361 = (54357249303:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 361+point 2 split 4096 362)/2 = (358572113:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((358572113:ℝ)/168755200)/ClassicalSixthBranch.v ((358572113:ℝ)/168755200) = (786066283553:ℝ)/403223608136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_361
  · change lowerPayment 362 ≤ lowerValue ((point 2 split 4096 362+point 2 split 4096 363)/2)
    have hp : lowerPayment 362 = (54496095821:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 362+point 2 split 4096 363)/2 = (14345215:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((14345215:ℝ)/6750208)/ClassicalSixthBranch.v ((14345215:ℝ)/6750208) = (785988969879:ℝ)/403175600248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_362
  · change lowerPayment 363 ≤ lowerValue ((point 2 split 4096 363+point 2 split 4096 364)/2)
    have hp : lowerPayment 363 = (54634885498:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 363+point 2 split 4096 364)/2 = (358688637:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((358688637:ℝ)/168755200)/ClassicalSixthBranch.v ((358688637:ℝ)/168755200) = (157182331241:ℝ)/80625518472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_363
  · change lowerPayment 364 ≤ lowerValue ((point 2 split 4096 364+point 2 split 4096 365)/2)
    have hp : lowerPayment 364 = (54773618384:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 364+point 2 split 4096 365)/2 = (358746899:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((358746899:ℝ)/168755200)/ClassicalSixthBranch.v ((358746899:ℝ)/168755200) = (785834342531:ℝ)/403079584472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_364
  · change lowerPayment 365 ≤ lowerValue ((point 2 split 4096 365+point 2 split 4096 366)/2)
    have hp : lowerPayment 365 = (54912294529:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 365+point 2 split 4096 366)/2 = (358805161:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((358805161:ℝ)/168755200)/ClassicalSixthBranch.v ((358805161:ℝ)/168755200) = (785757028857:ℝ)/403031576584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_365
  · change lowerPayment 366 ≤ lowerValue ((point 2 split 4096 366+point 2 split 4096 367)/2)
    have hp : lowerPayment 366 = (55050913985:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 366+point 2 split 4096 367)/2 = (358863423:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((358863423:ℝ)/168755200)/ClassicalSixthBranch.v ((358863423:ℝ)/168755200) = (785679715183:ℝ)/402983568696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_366
  · change lowerPayment 367 ≤ lowerValue ((point 2 split 4096 367+point 2 split 4096 368)/2)
    have hp : lowerPayment 367 = (55189476802:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 367+point 2 split 4096 368)/2 = (71784337:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((71784337:ℝ)/33751040)/ClassicalSixthBranch.v ((71784337:ℝ)/33751040) = (785602401509:ℝ)/402935560808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_367
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_022
