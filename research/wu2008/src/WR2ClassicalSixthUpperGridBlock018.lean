import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints018
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_018 (j : Fin 16) : upperPayment (16*18+j.val) ≤
    upperValue ((point split endpoint 4096 (16*18+j.val)+point split endpoint 4096 (16*18+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 288 ≤ upperValue ((point split endpoint 4096 288+point split endpoint 4096 289)/2)
    have hp : upperPayment 288 = (407898168958:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 288+point split endpoint 4096 289)/2 = (583407327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583407327:ℝ)/168755200)*ClassicalSixthBranch.v ((583407327:ℝ)/168755200)/ClassicalSixthBranch.r = (155546074544337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_288
  · change upperPayment 289 ≤ upperValue ((point split endpoint 4096 289+point split endpoint 4096 290)/2)
    have hp : upperPayment 289 = (407838449591:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 289+point split endpoint 4096 290)/2 = (583432477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583432477:ℝ)/168755200)*ClassicalSixthBranch.v ((583432477:ℝ)/168755200)/ClassicalSixthBranch.r = (155520642184281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_289
  · change upperPayment 290 ≤ upperValue ((point split endpoint 4096 290+point split endpoint 4096 291)/2)
    have hp : upperPayment 290 = (407778710321:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 290+point split endpoint 4096 291)/2 = (583457627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583457627:ℝ)/168755200)*ClassicalSixthBranch.v ((583457627:ℝ)/168755200)/ClassicalSixthBranch.r = (155495211848297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_290
  · change upperPayment 291 ≤ upperValue ((point split endpoint 4096 291+point split endpoint 4096 292)/2)
    have hp : upperPayment 291 = (407718951143:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 291+point split endpoint 4096 292)/2 = (583482777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583482777:ℝ)/168755200)*ClassicalSixthBranch.v ((583482777:ℝ)/168755200)/ClassicalSixthBranch.r = (155469783536385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_291
  · change upperPayment 292 ≤ upperValue ((point split endpoint 4096 292+point split endpoint 4096 293)/2)
    have hp : upperPayment 292 = (407659172057:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 292+point split endpoint 4096 293)/2 = (583507927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583507927:ℝ)/168755200)*ClassicalSixthBranch.v ((583507927:ℝ)/168755200)/ClassicalSixthBranch.r = (155444357248545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_292
  · change upperPayment 293 ≤ upperValue ((point split endpoint 4096 293+point split endpoint 4096 294)/2)
    have hp : upperPayment 293 = (407599373059:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 293+point split endpoint 4096 294)/2 = (583533077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583533077:ℝ)/168755200)*ClassicalSixthBranch.v ((583533077:ℝ)/168755200)/ClassicalSixthBranch.r = (155418932984777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_293
  · change upperPayment 294 ≤ upperValue ((point split endpoint 4096 294+point split endpoint 4096 295)/2)
    have hp : upperPayment 294 = (407539554146:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 294+point split endpoint 4096 295)/2 = (583558227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583558227:ℝ)/168755200)*ClassicalSixthBranch.v ((583558227:ℝ)/168755200)/ClassicalSixthBranch.r = (155393510745081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_294
  · change upperPayment 295 ≤ upperValue ((point split endpoint 4096 295+point split endpoint 4096 296)/2)
    have hp : upperPayment 295 = (407479715318:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 295+point split endpoint 4096 296)/2 = (583583377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583583377:ℝ)/168755200)*ClassicalSixthBranch.v ((583583377:ℝ)/168755200)/ClassicalSixthBranch.r = (155368090529457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_295
  · change upperPayment 296 ≤ upperValue ((point split endpoint 4096 296+point split endpoint 4096 297)/2)
    have hp : upperPayment 296 = (407419856570:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 296+point split endpoint 4096 297)/2 = (583608527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583608527:ℝ)/168755200)*ClassicalSixthBranch.v ((583608527:ℝ)/168755200)/ClassicalSixthBranch.r = (155342672337905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_296
  · change upperPayment 297 ≤ upperValue ((point split endpoint 4096 297+point split endpoint 4096 298)/2)
    have hp : upperPayment 297 = (407359977901:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 297+point split endpoint 4096 298)/2 = (583633677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583633677:ℝ)/168755200)*ClassicalSixthBranch.v ((583633677:ℝ)/168755200)/ClassicalSixthBranch.r = (155317256170425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_297
  · change upperPayment 298 ≤ upperValue ((point split endpoint 4096 298+point split endpoint 4096 299)/2)
    have hp : upperPayment 298 = (407300079308:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 298+point split endpoint 4096 299)/2 = (583658827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583658827:ℝ)/168755200)*ClassicalSixthBranch.v ((583658827:ℝ)/168755200)/ClassicalSixthBranch.r = (155291842027017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_298
  · change upperPayment 299 ≤ upperValue ((point split endpoint 4096 299+point split endpoint 4096 300)/2)
    have hp : upperPayment 299 = (407240160789:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 299+point split endpoint 4096 300)/2 = (583683977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583683977:ℝ)/168755200)*ClassicalSixthBranch.v ((583683977:ℝ)/168755200)/ClassicalSixthBranch.r = (155266429907681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_299
  · change upperPayment 300 ≤ upperValue ((point split endpoint 4096 300+point split endpoint 4096 301)/2)
    have hp : upperPayment 300 = (407180222341:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 300+point split endpoint 4096 301)/2 = (583709127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583709127:ℝ)/168755200)*ClassicalSixthBranch.v ((583709127:ℝ)/168755200)/ClassicalSixthBranch.r = (155241019812417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_300
  · change upperPayment 301 ≤ upperValue ((point split endpoint 4096 301+point split endpoint 4096 302)/2)
    have hp : upperPayment 301 = (407120263962:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 301+point split endpoint 4096 302)/2 = (583734277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583734277:ℝ)/168755200)*ClassicalSixthBranch.v ((583734277:ℝ)/168755200)/ClassicalSixthBranch.r = (155215611741225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_301
  · change upperPayment 302 ≤ upperValue ((point split endpoint 4096 302+point split endpoint 4096 303)/2)
    have hp : upperPayment 302 = (407060285649:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 302+point split endpoint 4096 303)/2 = (583759427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583759427:ℝ)/168755200)*ClassicalSixthBranch.v ((583759427:ℝ)/168755200)/ClassicalSixthBranch.r = (155190205694105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_302
  · change upperPayment 303 ≤ upperValue ((point split endpoint 4096 303+point split endpoint 4096 304)/2)
    have hp : upperPayment 303 = (407000287399:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 303+point split endpoint 4096 304)/2 = (583784577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583784577:ℝ)/168755200)*ClassicalSixthBranch.v ((583784577:ℝ)/168755200)/ClassicalSixthBranch.r = (155164801671057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_303
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_018
