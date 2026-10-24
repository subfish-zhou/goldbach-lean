import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints210
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_210 (j : Fin 16) : lowerPayment (16*210+j.val) ≤
    lowerValue ((point 2 split 4096 (16*210+j.val)+point 2 split 4096 (16*210+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3360 ≤ lowerValue ((point 2 split 4096 3360+point 2 split 4096 3361)/2)
    have hp : lowerPayment 3360 = (353564023735:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3360+point 2 split 4096 3361)/2 = (533299851:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((533299851:ℝ)/168755200)/ClassicalSixthBranch.v ((533299851:ℝ)/168755200) = (554202575227:ℝ)/259247952024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3360
  · change lowerPayment 3361 ≤ lowerValue ((point 2 split 4096 3361+point 2 split 4096 3362)/2)
    have hp : lowerPayment 3361 = (353655155043:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3361+point 2 split 4096 3362)/2 = (533358113:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((533358113:ℝ)/168755200)/ClassicalSixthBranch.v ((533358113:ℝ)/168755200) = (554125261553:ℝ)/259199944136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3361
  · change lowerPayment 3362 ≤ lowerValue ((point 2 split 4096 3362+point 2 split 4096 3363)/2)
    have hp : lowerPayment 3362 = (353746296236:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3362+point 2 split 4096 3363)/2 = (21336655:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((21336655:ℝ)/6750208)/ClassicalSixthBranch.v ((21336655:ℝ)/6750208) = (554047947879:ℝ)/259151936248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3362
  · change lowerPayment 3363 ≤ lowerValue ((point 2 split 4096 3363+point 2 split 4096 3364)/2)
    have hp : lowerPayment 3363 = (353837447331:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3363+point 2 split 4096 3364)/2 = (533474637:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((533474637:ℝ)/168755200)/ClassicalSixthBranch.v ((533474637:ℝ)/168755200) = (110794126841:ℝ)/51820785672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3363
  · change lowerPayment 3364 ≤ lowerValue ((point 2 split 4096 3364+point 2 split 4096 3365)/2)
    have hp : lowerPayment 3364 = (353928608341:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3364+point 2 split 4096 3365)/2 = (533532899:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((533532899:ℝ)/168755200)/ClassicalSixthBranch.v ((533532899:ℝ)/168755200) = (553893320531:ℝ)/259055920472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3364
  · change lowerPayment 3365 ≤ lowerValue ((point 2 split 4096 3365+point 2 split 4096 3366)/2)
    have hp : lowerPayment 3365 = (354019779282:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3365+point 2 split 4096 3366)/2 = (533591161:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((533591161:ℝ)/168755200)/ClassicalSixthBranch.v ((533591161:ℝ)/168755200) = (553816006857:ℝ)/259007912584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3365
  · change lowerPayment 3366 ≤ lowerValue ((point 2 split 4096 3366+point 2 split 4096 3367)/2)
    have hp : lowerPayment 3366 = (354110960169:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3366+point 2 split 4096 3367)/2 = (533649423:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((533649423:ℝ)/168755200)/ClassicalSixthBranch.v ((533649423:ℝ)/168755200) = (553738693183:ℝ)/258959904696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3366
  · change lowerPayment 3367 ≤ lowerValue ((point 2 split 4096 3367+point 2 split 4096 3368)/2)
    have hp : lowerPayment 3367 = (354202151017:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3367+point 2 split 4096 3368)/2 = (106741537:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((106741537:ℝ)/33751040)/ClassicalSixthBranch.v ((106741537:ℝ)/33751040) = (553661379509:ℝ)/258911896808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3367
  · change lowerPayment 3368 ≤ lowerValue ((point 2 split 4096 3368+point 2 split 4096 3369)/2)
    have hp : lowerPayment 3368 = (354293351840:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3368+point 2 split 4096 3369)/2 = (533765947:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((533765947:ℝ)/168755200)/ClassicalSixthBranch.v ((533765947:ℝ)/168755200) = (110716813167:ℝ)/51772777784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3368
  · change lowerPayment 3369 ≤ lowerValue ((point 2 split 4096 3369+point 2 split 4096 3370)/2)
    have hp : lowerPayment 3369 = (354384562654:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3369+point 2 split 4096 3370)/2 = (533824209:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((533824209:ℝ)/168755200)/ClassicalSixthBranch.v ((533824209:ℝ)/168755200) = (553506752161:ℝ)/258815881032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3369
  · change lowerPayment 3370 ≤ lowerValue ((point 2 split 4096 3370+point 2 split 4096 3371)/2)
    have hp : lowerPayment 3370 = (354475783473:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3370+point 2 split 4096 3371)/2 = (533882471:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((533882471:ℝ)/168755200)/ClassicalSixthBranch.v ((533882471:ℝ)/168755200) = (553429438487:ℝ)/258767873144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3370
  · change lowerPayment 3371 ≤ lowerValue ((point 2 split 4096 3371+point 2 split 4096 3372)/2)
    have hp : lowerPayment 3371 = (354567014314:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3371+point 2 split 4096 3372)/2 = (533940733:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((533940733:ℝ)/168755200)/ClassicalSixthBranch.v ((533940733:ℝ)/168755200) = (553352124813:ℝ)/258719865256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3371
  · change lowerPayment 3372 ≤ lowerValue ((point 2 split 4096 3372+point 2 split 4096 3373)/2)
    have hp : lowerPayment 3372 = (354658255189:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3372+point 2 split 4096 3373)/2 = (106799799:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((106799799:ℝ)/33751040)/ClassicalSixthBranch.v ((106799799:ℝ)/33751040) = (553274811139:ℝ)/258671857368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3372
  · change lowerPayment 3373 ≤ lowerValue ((point 2 split 4096 3373+point 2 split 4096 3374)/2)
    have hp : lowerPayment 3373 = (354749506116:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3373+point 2 split 4096 3374)/2 = (534057257:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((534057257:ℝ)/168755200)/ClassicalSixthBranch.v ((534057257:ℝ)/168755200) = (110639499493:ℝ)/51724769896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3373
  · change lowerPayment 3374 ≤ lowerValue ((point 2 split 4096 3374+point 2 split 4096 3375)/2)
    have hp : lowerPayment 3374 = (354840767108:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3374+point 2 split 4096 3375)/2 = (534115519:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((534115519:ℝ)/168755200)/ClassicalSixthBranch.v ((534115519:ℝ)/168755200) = (553120183791:ℝ)/258575841592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3374
  · change lowerPayment 3375 ≤ lowerValue ((point 2 split 4096 3375+point 2 split 4096 3376)/2)
    have hp : lowerPayment 3375 = (354932038180:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3375+point 2 split 4096 3376)/2 = (534173781:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((534173781:ℝ)/168755200)/ClassicalSixthBranch.v ((534173781:ℝ)/168755200) = (553042870117:ℝ)/258527833704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3375
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_210
