import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints017
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_017 (j : Fin 16) : lowerPayment (16*17+j.val) ≤
    lowerValue ((point 2 split 4096 (16*17+j.val)+point 2 split 4096 (16*17+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 272 ≤ lowerValue ((point 2 split 4096 272+point 2 split 4096 273)/2)
    have hp : lowerPayment 272 = (41765972656:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 272+point 2 split 4096 273)/2 = (70677359:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((70677359:ℝ)/33751040)/ClassicalSixthBranch.v ((70677359:ℝ)/33751040) = (792947200539:ℝ)/407496310168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_272
  · change lowerPayment 273 ≤ lowerValue ((point 2 split 4096 273+point 2 split 4096 274)/2)
    have hp : lowerPayment 273 = (41910086776:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 273+point 2 split 4096 274)/2 = (353445057:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((353445057:ℝ)/168755200)/ClassicalSixthBranch.v ((353445057:ℝ)/168755200) = (158573977373:ℝ)/81489660456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_273
  · change lowerPayment 274 ≤ lowerValue ((point 2 split 4096 274+point 2 split 4096 275)/2)
    have hp : lowerPayment 274 = (42054139351:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 274+point 2 split 4096 275)/2 = (353503319:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((353503319:ℝ)/168755200)/ClassicalSixthBranch.v ((353503319:ℝ)/168755200) = (792792573191:ℝ)/407400294392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_274
  · change lowerPayment 275 ≤ lowerValue ((point 2 split 4096 275+point 2 split 4096 276)/2)
    have hp : lowerPayment 275 = (42198130436:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 275+point 2 split 4096 276)/2 = (353561581:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((353561581:ℝ)/168755200)/ClassicalSixthBranch.v ((353561581:ℝ)/168755200) = (792715259517:ℝ)/407352286504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_275
  · change lowerPayment 276 ≤ lowerValue ((point 2 split 4096 276+point 2 split 4096 277)/2)
    have hp : lowerPayment 276 = (42342060085:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 276+point 2 split 4096 277)/2 = (353619843:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((353619843:ℝ)/168755200)/ClassicalSixthBranch.v ((353619843:ℝ)/168755200) = (792637945843:ℝ)/407304278616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_276
  · change lowerPayment 277 ≤ lowerValue ((point 2 split 4096 277+point 2 split 4096 278)/2)
    have hp : lowerPayment 277 = (42485928354:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 277+point 2 split 4096 278)/2 = (70735621:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((70735621:ℝ)/33751040)/ClassicalSixthBranch.v ((70735621:ℝ)/33751040) = (792560632169:ℝ)/407256270728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_277
  · change lowerPayment 278 ≤ lowerValue ((point 2 split 4096 278+point 2 split 4096 279)/2)
    have hp : lowerPayment 278 = (42629735298:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 278+point 2 split 4096 279)/2 = (353736367:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((353736367:ℝ)/168755200)/ClassicalSixthBranch.v ((353736367:ℝ)/168755200) = (158496663699:ℝ)/81441652568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_278
  · change lowerPayment 279 ≤ lowerValue ((point 2 split 4096 279+point 2 split 4096 280)/2)
    have hp : lowerPayment 279 = (42773480972:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 279+point 2 split 4096 280)/2 = (353794629:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((353794629:ℝ)/168755200)/ClassicalSixthBranch.v ((353794629:ℝ)/168755200) = (792406004821:ℝ)/407160254952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_279
  · change lowerPayment 280 ≤ lowerValue ((point 2 split 4096 280+point 2 split 4096 281)/2)
    have hp : lowerPayment 280 = (42917165430:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 280+point 2 split 4096 281)/2 = (353852891:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((353852891:ℝ)/168755200)/ClassicalSixthBranch.v ((353852891:ℝ)/168755200) = (792328691147:ℝ)/407112247064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_280
  · change lowerPayment 281 ≤ lowerValue ((point 2 split 4096 281+point 2 split 4096 282)/2)
    have hp : lowerPayment 281 = (43060788728:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 281+point 2 split 4096 282)/2 = (353911153:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((353911153:ℝ)/168755200)/ClassicalSixthBranch.v ((353911153:ℝ)/168755200) = (792251377473:ℝ)/407064239176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_281
  · change lowerPayment 282 ≤ lowerValue ((point 2 split 4096 282+point 2 split 4096 283)/2)
    have hp : lowerPayment 282 = (43204350920:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 282+point 2 split 4096 283)/2 = (70793883:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((70793883:ℝ)/33751040)/ClassicalSixthBranch.v ((70793883:ℝ)/33751040) = (792174063799:ℝ)/407016231288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_282
  · change lowerPayment 283 ≤ lowerValue ((point 2 split 4096 283+point 2 split 4096 284)/2)
    have hp : lowerPayment 283 = (43347852060:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 283+point 2 split 4096 284)/2 = (354027677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((354027677:ℝ)/168755200)/ClassicalSixthBranch.v ((354027677:ℝ)/168755200) = (31683870005:ℝ)/16278728936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_283
  · change lowerPayment 284 ≤ lowerValue ((point 2 split 4096 284+point 2 split 4096 285)/2)
    have hp : lowerPayment 284 = (43491292204:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 284+point 2 split 4096 285)/2 = (354085939:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((354085939:ℝ)/168755200)/ClassicalSixthBranch.v ((354085939:ℝ)/168755200) = (792019436451:ℝ)/406920215512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_284
  · change lowerPayment 285 ≤ lowerValue ((point 2 split 4096 285+point 2 split 4096 286)/2)
    have hp : lowerPayment 285 = (43634671406:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 285+point 2 split 4096 286)/2 = (354144201:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((354144201:ℝ)/168755200)/ClassicalSixthBranch.v ((354144201:ℝ)/168755200) = (791942122777:ℝ)/406872207624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_285
  · change lowerPayment 286 ≤ lowerValue ((point 2 split 4096 286+point 2 split 4096 287)/2)
    have hp : lowerPayment 286 = (43777989720:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 286+point 2 split 4096 287)/2 = (354202463:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((354202463:ℝ)/168755200)/ClassicalSixthBranch.v ((354202463:ℝ)/168755200) = (791864809103:ℝ)/406824199736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_286
  · change lowerPayment 287 ≤ lowerValue ((point 2 split 4096 287+point 2 split 4096 288)/2)
    have hp : lowerPayment 287 = (43921247201:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 287+point 2 split 4096 288)/2 = (14170429:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((14170429:ℝ)/6750208)/ClassicalSixthBranch.v ((14170429:ℝ)/6750208) = (791787495429:ℝ)/406776191848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_287
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_017
