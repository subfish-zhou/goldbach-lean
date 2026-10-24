import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints209
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_209 (j : Fin 16) : lowerPayment (16*209+j.val) ≤
    lowerValue ((point 2 split 4096 (16*209+j.val)+point 2 split 4096 (16*209+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3344 ≤ lowerValue ((point 2 split 4096 3344+point 2 split 4096 3345)/2)
    have hp : lowerPayment 3344 = (352107255092:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3344+point 2 split 4096 3345)/2 = (532367659:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((532367659:ℝ)/168755200)/ClassicalSixthBranch.v ((532367659:ℝ)/168755200) = (555439594011:ℝ)/260016078232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3344
  · change lowerPayment 3345 ≤ lowerValue ((point 2 split 4096 3345+point 2 split 4096 3346)/2)
    have hp : lowerPayment 3345 = (352198230258:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3345+point 2 split 4096 3346)/2 = (532425921:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((532425921:ℝ)/168755200)/ClassicalSixthBranch.v ((532425921:ℝ)/168755200) = (555362280337:ℝ)/259968070344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3345
  · change lowerPayment 3346 ≤ lowerValue ((point 2 split 4096 3346+point 2 split 4096 3347)/2)
    have hp : lowerPayment 3346 = (352289215070:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3346+point 2 split 4096 3347)/2 = (532484183:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((532484183:ℝ)/168755200)/ClassicalSixthBranch.v ((532484183:ℝ)/168755200) = (555284966663:ℝ)/259920062456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3346
  · change lowerPayment 3347 ≤ lowerValue ((point 2 split 4096 3347+point 2 split 4096 3348)/2)
    have hp : lowerPayment 3347 = (352380209545:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3347+point 2 split 4096 3348)/2 = (1034063:ℝ)/327680 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((1034063:ℝ)/327680)/ClassicalSixthBranch.v ((1034063:ℝ)/327680) = (5390365563:ℝ)/2523029656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3347
  · change lowerPayment 3348 ≤ lowerValue ((point 2 split 4096 3348+point 2 split 4096 3349)/2)
    have hp : lowerPayment 3348 = (352471213697:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3348+point 2 split 4096 3349)/2 = (532600707:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((532600707:ℝ)/168755200)/ClassicalSixthBranch.v ((532600707:ℝ)/168755200) = (111026067863:ℝ)/51964809336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3348
  · change lowerPayment 3349 ≤ lowerValue ((point 2 split 4096 3349+point 2 split 4096 3350)/2)
    have hp : lowerPayment 3349 = (352562227540:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3349+point 2 split 4096 3350)/2 = (532658969:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((532658969:ℝ)/168755200)/ClassicalSixthBranch.v ((532658969:ℝ)/168755200) = (555053025641:ℝ)/259776038792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3349
  · change lowerPayment 3350 ≤ lowerValue ((point 2 split 4096 3350+point 2 split 4096 3351)/2)
    have hp : lowerPayment 3350 = (352653251090:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3350+point 2 split 4096 3351)/2 = (532717231:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((532717231:ℝ)/168755200)/ClassicalSixthBranch.v ((532717231:ℝ)/168755200) = (554975711967:ℝ)/259728030904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3350
  · change lowerPayment 3351 ≤ lowerValue ((point 2 split 4096 3351+point 2 split 4096 3352)/2)
    have hp : lowerPayment 3351 = (352744284361:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3351+point 2 split 4096 3352)/2 = (532775493:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((532775493:ℝ)/168755200)/ClassicalSixthBranch.v ((532775493:ℝ)/168755200) = (554898398293:ℝ)/259680023016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3351
  · change lowerPayment 3352 ≤ lowerValue ((point 2 split 4096 3352+point 2 split 4096 3353)/2)
    have hp : lowerPayment 3352 = (352835327369:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3352+point 2 split 4096 3353)/2 = (106566751:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((106566751:ℝ)/33751040)/ClassicalSixthBranch.v ((106566751:ℝ)/33751040) = (554821084619:ℝ)/259632015128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3352
  · change lowerPayment 3353 ≤ lowerValue ((point 2 split 4096 3353+point 2 split 4096 3354)/2)
    have hp : lowerPayment 3353 = (352926380128:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3353+point 2 split 4096 3354)/2 = (532892017:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((532892017:ℝ)/168755200)/ClassicalSixthBranch.v ((532892017:ℝ)/168755200) = (110948754189:ℝ)/51916801448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3353
  · change lowerPayment 3354 ≤ lowerValue ((point 2 split 4096 3354+point 2 split 4096 3355)/2)
    have hp : lowerPayment 3354 = (353017442653:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3354+point 2 split 4096 3355)/2 = (532950279:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((532950279:ℝ)/168755200)/ClassicalSixthBranch.v ((532950279:ℝ)/168755200) = (554666457271:ℝ)/259535999352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3354
  · change lowerPayment 3355 ≤ lowerValue ((point 2 split 4096 3355+point 2 split 4096 3356)/2)
    have hp : lowerPayment 3355 = (353108514960:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3355+point 2 split 4096 3356)/2 = (533008541:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((533008541:ℝ)/168755200)/ClassicalSixthBranch.v ((533008541:ℝ)/168755200) = (554589143597:ℝ)/259487991464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3355
  · change lowerPayment 3356 ≤ lowerValue ((point 2 split 4096 3356+point 2 split 4096 3357)/2)
    have hp : lowerPayment 3356 = (353199597063:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3356+point 2 split 4096 3357)/2 = (533066803:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((533066803:ℝ)/168755200)/ClassicalSixthBranch.v ((533066803:ℝ)/168755200) = (554511829923:ℝ)/259439983576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3356
  · change lowerPayment 3357 ≤ lowerValue ((point 2 split 4096 3357+point 2 split 4096 3358)/2)
    have hp : lowerPayment 3357 = (353290688977:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3357+point 2 split 4096 3358)/2 = (106625013:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((106625013:ℝ)/33751040)/ClassicalSixthBranch.v ((106625013:ℝ)/33751040) = (554434516249:ℝ)/259391975688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3357
  · change lowerPayment 3358 ≤ lowerValue ((point 2 split 4096 3358+point 2 split 4096 3359)/2)
    have hp : lowerPayment 3358 = (353381790717:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3358+point 2 split 4096 3359)/2 = (533183327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((533183327:ℝ)/168755200)/ClassicalSixthBranch.v ((533183327:ℝ)/168755200) = (22174288103:ℝ)/10373758712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3358
  · change lowerPayment 3359 ≤ lowerValue ((point 2 split 4096 3359+point 2 split 4096 3360)/2)
    have hp : lowerPayment 3359 = (353472902298:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3359+point 2 split 4096 3360)/2 = (533241589:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((533241589:ℝ)/168755200)/ClassicalSixthBranch.v ((533241589:ℝ)/168755200) = (554279888901:ℝ)/259295959912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3359
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_209
