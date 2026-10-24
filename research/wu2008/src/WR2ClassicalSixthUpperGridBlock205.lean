import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints205
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_205 (j : Fin 16) : upperPayment (16*205+j.val) ≤
    upperValue ((point split endpoint 4096 (16*205+j.val)+point split endpoint 4096 (16*205+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3280 ≤ upperValue ((point split endpoint 4096 3280+point split endpoint 4096 3281)/2)
    have hp : upperPayment 3280 = (124312973303:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3280+point split endpoint 4096 3281)/2 = (658656127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658656127:ℝ)/168755200)*ClassicalSixthBranch.v ((658656127:ℝ)/168755200)/ClassicalSixthBranch.r = (88509236287377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3280
  · change upperPayment 3281 ≤ upperValue ((point split endpoint 4096 3281+point split endpoint 4096 3282)/2)
    have hp : upperPayment 3281 = (124175792313:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3281+point split endpoint 4096 3282)/2 = (658681277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658681277:ℝ)/168755200)*ClassicalSixthBranch.v ((658681277:ℝ)/168755200)/ClassicalSixthBranch.r = (88489859950745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3281
  · change upperPayment 3282 ≤ upperValue ((point split endpoint 4096 3282+point split endpoint 4096 3283)/2)
    have hp : upperPayment 3282 = (124038576427:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3282+point split endpoint 4096 3283)/2 = (658706427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658706427:ℝ)/168755200)*ClassicalSixthBranch.v ((658706427:ℝ)/168755200)/ClassicalSixthBranch.r = (88470485638185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3282
  · change upperPayment 3283 ≤ upperValue ((point split endpoint 4096 3283+point split endpoint 4096 3284)/2)
    have hp : upperPayment 3283 = (123901325638:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3283+point split endpoint 4096 3284)/2 = (658731577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658731577:ℝ)/168755200)*ClassicalSixthBranch.v ((658731577:ℝ)/168755200)/ClassicalSixthBranch.r = (88451113349697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3283
  · change upperPayment 3284 ≤ upperValue ((point split endpoint 4096 3284+point split endpoint 4096 3285)/2)
    have hp : upperPayment 3284 = (123764039935:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3284+point split endpoint 4096 3285)/2 = (658756727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658756727:ℝ)/168755200)*ClassicalSixthBranch.v ((658756727:ℝ)/168755200)/ClassicalSixthBranch.r = (88431743085281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3284
  · change upperPayment 3285 ≤ upperValue ((point split endpoint 4096 3285+point split endpoint 4096 3286)/2)
    have hp : upperPayment 3285 = (123626719311:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3285+point split endpoint 4096 3286)/2 = (658781877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658781877:ℝ)/168755200)*ClassicalSixthBranch.v ((658781877:ℝ)/168755200)/ClassicalSixthBranch.r = (88412374844937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3285
  · change upperPayment 3286 ≤ upperValue ((point split endpoint 4096 3286+point split endpoint 4096 3287)/2)
    have hp : upperPayment 3286 = (123489363757:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3286+point split endpoint 4096 3287)/2 = (658807027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658807027:ℝ)/168755200)*ClassicalSixthBranch.v ((658807027:ℝ)/168755200)/ClassicalSixthBranch.r = (88393008628665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3286
  · change upperPayment 3287 ≤ upperValue ((point split endpoint 4096 3287+point split endpoint 4096 3288)/2)
    have hp : upperPayment 3287 = (123351973263:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3287+point split endpoint 4096 3288)/2 = (658832177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658832177:ℝ)/168755200)*ClassicalSixthBranch.v ((658832177:ℝ)/168755200)/ClassicalSixthBranch.r = (88373644436465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3287
  · change upperPayment 3288 ≤ upperValue ((point split endpoint 4096 3288+point split endpoint 4096 3289)/2)
    have hp : upperPayment 3288 = (123214547822:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3288+point split endpoint 4096 3289)/2 = (658857327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658857327:ℝ)/168755200)*ClassicalSixthBranch.v ((658857327:ℝ)/168755200)/ClassicalSixthBranch.r = (88354282268337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3288
  · change upperPayment 3289 ≤ upperValue ((point split endpoint 4096 3289+point split endpoint 4096 3290)/2)
    have hp : upperPayment 3289 = (123077087425:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3289+point split endpoint 4096 3290)/2 = (658882477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658882477:ℝ)/168755200)*ClassicalSixthBranch.v ((658882477:ℝ)/168755200)/ClassicalSixthBranch.r = (88334922124281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3289
  · change upperPayment 3290 ≤ upperValue ((point split endpoint 4096 3290+point split endpoint 4096 3291)/2)
    have hp : upperPayment 3290 = (122939592062:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3290+point split endpoint 4096 3291)/2 = (658907627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658907627:ℝ)/168755200)*ClassicalSixthBranch.v ((658907627:ℝ)/168755200)/ClassicalSixthBranch.r = (88315564004297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3290
  · change upperPayment 3291 ≤ upperValue ((point split endpoint 4096 3291+point split endpoint 4096 3292)/2)
    have hp : upperPayment 3291 = (122802061726:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3291+point split endpoint 4096 3292)/2 = (658932777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658932777:ℝ)/168755200)*ClassicalSixthBranch.v ((658932777:ℝ)/168755200)/ClassicalSixthBranch.r = (88296207908385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3291
  · change upperPayment 3292 ≤ upperValue ((point split endpoint 4096 3292+point split endpoint 4096 3293)/2)
    have hp : upperPayment 3292 = (122664496407:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3292+point split endpoint 4096 3293)/2 = (658957927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658957927:ℝ)/168755200)*ClassicalSixthBranch.v ((658957927:ℝ)/168755200)/ClassicalSixthBranch.r = (88276853836545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3292
  · change upperPayment 3293 ≤ upperValue ((point split endpoint 4096 3293+point split endpoint 4096 3294)/2)
    have hp : upperPayment 3293 = (122526896097:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3293+point split endpoint 4096 3294)/2 = (658983077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658983077:ℝ)/168755200)*ClassicalSixthBranch.v ((658983077:ℝ)/168755200)/ClassicalSixthBranch.r = (88257501788777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3293
  · change upperPayment 3294 ≤ upperValue ((point split endpoint 4096 3294+point split endpoint 4096 3295)/2)
    have hp : upperPayment 3294 = (122389260787:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3294+point split endpoint 4096 3295)/2 = (659008227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659008227:ℝ)/168755200)*ClassicalSixthBranch.v ((659008227:ℝ)/168755200)/ClassicalSixthBranch.r = (88238151765081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3294
  · change upperPayment 3295 ≤ upperValue ((point split endpoint 4096 3295+point split endpoint 4096 3296)/2)
    have hp : upperPayment 3295 = (122251590469:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3295+point split endpoint 4096 3296)/2 = (659033377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659033377:ℝ)/168755200)*ClassicalSixthBranch.v ((659033377:ℝ)/168755200)/ClassicalSixthBranch.r = (88218803765457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3295
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_205
