import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints205
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_205 (j : Fin 16) : lowerPayment (16*205+j.val) ≤
    lowerValue ((point 2 split 4096 (16*205+j.val)+point 2 split 4096 (16*205+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3280 ≤ lowerValue ((point 2 split 4096 3280+point 2 split 4096 3281)/2)
    have hp : lowerPayment 3280 = (346304230575:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3280+point 2 split 4096 3281)/2 = (528638891:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((528638891:ℝ)/168755200)/ClassicalSixthBranch.v ((528638891:ℝ)/168755200) = (560387669147:ℝ)/263088583064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3280
  · change lowerPayment 3281 ≤ lowerValue ((point 2 split 4096 3281+point 2 split 4096 3282)/2)
    have hp : lowerPayment 3281 = (346394619191:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3281+point 2 split 4096 3282)/2 = (528697153:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((528697153:ℝ)/168755200)/ClassicalSixthBranch.v ((528697153:ℝ)/168755200) = (560310355473:ℝ)/263040575176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3281
  · change lowerPayment 3282 ≤ lowerValue ((point 2 split 4096 3282+point 2 split 4096 3283)/2)
    have hp : lowerPayment 3282 = (346485016507:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3282+point 2 split 4096 3283)/2 = (105751083:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((105751083:ℝ)/33751040)/ClassicalSixthBranch.v ((105751083:ℝ)/33751040) = (560233041799:ℝ)/262992567288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3282
  · change lowerPayment 3283 ≤ lowerValue ((point 2 split 4096 3283+point 2 split 4096 3284)/2)
    have hp : lowerPayment 3283 = (346575422537:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3283+point 2 split 4096 3284)/2 = (528813677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((528813677:ℝ)/168755200)/ClassicalSixthBranch.v ((528813677:ℝ)/168755200) = (22406229125:ℝ)/10517782376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3283
  · change lowerPayment 3284 ≤ lowerValue ((point 2 split 4096 3284+point 2 split 4096 3285)/2)
    have hp : lowerPayment 3284 = (346665837296:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3284+point 2 split 4096 3285)/2 = (528871939:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((528871939:ℝ)/168755200)/ClassicalSixthBranch.v ((528871939:ℝ)/168755200) = (560078414451:ℝ)/262896551512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3284
  · change lowerPayment 3285 ≤ lowerValue ((point 2 split 4096 3285+point 2 split 4096 3286)/2)
    have hp : lowerPayment 3285 = (346756260799:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3285+point 2 split 4096 3286)/2 = (528930201:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((528930201:ℝ)/168755200)/ClassicalSixthBranch.v ((528930201:ℝ)/168755200) = (560001100777:ℝ)/262848543624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3285
  · change lowerPayment 3286 ≤ lowerValue ((point 2 split 4096 3286+point 2 split 4096 3287)/2)
    have hp : lowerPayment 3286 = (346846693060:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3286+point 2 split 4096 3287)/2 = (528988463:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((528988463:ℝ)/168755200)/ClassicalSixthBranch.v ((528988463:ℝ)/168755200) = (559923787103:ℝ)/262800535736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3286
  · change lowerPayment 3287 ≤ lowerValue ((point 2 split 4096 3287+point 2 split 4096 3288)/2)
    have hp : lowerPayment 3287 = (346937134094:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3287+point 2 split 4096 3288)/2 = (21161869:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((21161869:ℝ)/6750208)/ClassicalSixthBranch.v ((21161869:ℝ)/6750208) = (559846473429:ℝ)/262752527848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3287
  · change lowerPayment 3288 ≤ lowerValue ((point 2 split 4096 3288+point 2 split 4096 3289)/2)
    have hp : lowerPayment 3288 = (347027583917:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3288+point 2 split 4096 3289)/2 = (529104987:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((529104987:ℝ)/168755200)/ClassicalSixthBranch.v ((529104987:ℝ)/168755200) = (111953831951:ℝ)/52540903992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3288
  · change lowerPayment 3289 ≤ lowerValue ((point 2 split 4096 3289+point 2 split 4096 3290)/2)
    have hp : lowerPayment 3289 = (347118042542:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3289+point 2 split 4096 3290)/2 = (529163249:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((529163249:ℝ)/168755200)/ClassicalSixthBranch.v ((529163249:ℝ)/168755200) = (559691846081:ℝ)/262656512072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3289
  · change lowerPayment 3290 ≤ lowerValue ((point 2 split 4096 3290+point 2 split 4096 3291)/2)
    have hp : lowerPayment 3290 = (347208509984:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3290+point 2 split 4096 3291)/2 = (529221511:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((529221511:ℝ)/168755200)/ClassicalSixthBranch.v ((529221511:ℝ)/168755200) = (559614532407:ℝ)/262608504184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3290
  · change lowerPayment 3291 ≤ lowerValue ((point 2 split 4096 3291+point 2 split 4096 3292)/2)
    have hp : lowerPayment 3291 = (347298986259:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3291+point 2 split 4096 3292)/2 = (529279773:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((529279773:ℝ)/168755200)/ClassicalSixthBranch.v ((529279773:ℝ)/168755200) = (559537218733:ℝ)/262560496296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3291
  · change lowerPayment 3292 ≤ lowerValue ((point 2 split 4096 3292+point 2 split 4096 3293)/2)
    have hp : lowerPayment 3292 = (347389471380:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3292+point 2 split 4096 3293)/2 = (105867607:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((105867607:ℝ)/33751040)/ClassicalSixthBranch.v ((105867607:ℝ)/33751040) = (559459905059:ℝ)/262512488408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3292
  · change lowerPayment 3293 ≤ lowerValue ((point 2 split 4096 3293+point 2 split 4096 3294)/2)
    have hp : lowerPayment 3293 = (347479965363:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3293+point 2 split 4096 3294)/2 = (529396297:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((529396297:ℝ)/168755200)/ClassicalSixthBranch.v ((529396297:ℝ)/168755200) = (111876518277:ℝ)/52492896104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3293
  · change lowerPayment 3294 ≤ lowerValue ((point 2 split 4096 3294+point 2 split 4096 3295)/2)
    have hp : lowerPayment 3294 = (347570468223:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3294+point 2 split 4096 3295)/2 = (529454559:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((529454559:ℝ)/168755200)/ClassicalSixthBranch.v ((529454559:ℝ)/168755200) = (559305277711:ℝ)/262416472632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3294
  · change lowerPayment 3295 ≤ lowerValue ((point 2 split 4096 3295+point 2 split 4096 3296)/2)
    have hp : lowerPayment 3295 = (347660979973:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3295+point 2 split 4096 3296)/2 = (529512821:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((529512821:ℝ)/168755200)/ClassicalSixthBranch.v ((529512821:ℝ)/168755200) = (559227964037:ℝ)/262368464744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3295
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_205
