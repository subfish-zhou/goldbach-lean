import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints207
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_207 (j : Fin 16) : lowerPayment (16*207+j.val) ≤
    lowerValue ((point 2 split 4096 (16*207+j.val)+point 2 split 4096 (16*207+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3312 ≤ lowerValue ((point 2 split 4096 3312+point 2 split 4096 3313)/2)
    have hp : lowerPayment 3312 = (349201054359:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3312+point 2 split 4096 3313)/2 = (21220131:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((21220131:ℝ)/6750208)/ClassicalSixthBranch.v ((21220131:ℝ)/6750208) = (557913631579:ℝ)/261552330648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3312
  · change lowerPayment 3313 ≤ lowerValue ((point 2 split 4096 3313+point 2 split 4096 3314)/2)
    have hp : lowerPayment 3313 = (349291728672:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3313+point 2 split 4096 3314)/2 = (530561537:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((530561537:ℝ)/168755200)/ClassicalSixthBranch.v ((530561537:ℝ)/168755200) = (111567263581:ℝ)/52300864552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3313
  · change lowerPayment 3314 ≤ lowerValue ((point 2 split 4096 3314+point 2 split 4096 3315)/2)
    have hp : lowerPayment 3314 = (349382412157:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3314+point 2 split 4096 3315)/2 = (530619799:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((530619799:ℝ)/168755200)/ClassicalSixthBranch.v ((530619799:ℝ)/168755200) = (557759004231:ℝ)/261456314872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3314
  · change lowerPayment 3315 ≤ lowerValue ((point 2 split 4096 3315+point 2 split 4096 3316)/2)
    have hp : lowerPayment 3315 = (349473104829:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3315+point 2 split 4096 3316)/2 = (530678061:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((530678061:ℝ)/168755200)/ClassicalSixthBranch.v ((530678061:ℝ)/168755200) = (557681690557:ℝ)/261408306984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3315
  · change lowerPayment 3316 ≤ lowerValue ((point 2 split 4096 3316+point 2 split 4096 3317)/2)
    have hp : lowerPayment 3316 = (349563806702:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3316+point 2 split 4096 3317)/2 = (530736323:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((530736323:ℝ)/168755200)/ClassicalSixthBranch.v ((530736323:ℝ)/168755200) = (557604376883:ℝ)/261360299096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3316
  · change lowerPayment 3317 ≤ lowerValue ((point 2 split 4096 3317+point 2 split 4096 3318)/2)
    have hp : lowerPayment 3317 = (349654517791:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3317+point 2 split 4096 3318)/2 = (106158917:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((106158917:ℝ)/33751040)/ClassicalSixthBranch.v ((106158917:ℝ)/33751040) = (557527063209:ℝ)/261312291208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3317
  · change lowerPayment 3318 ≤ lowerValue ((point 2 split 4096 3318+point 2 split 4096 3319)/2)
    have hp : lowerPayment 3318 = (349745238111:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3318+point 2 split 4096 3319)/2 = (530852847:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((530852847:ℝ)/168755200)/ClassicalSixthBranch.v ((530852847:ℝ)/168755200) = (111489949907:ℝ)/52252856664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3318
  · change lowerPayment 3319 ≤ lowerValue ((point 2 split 4096 3319+point 2 split 4096 3320)/2)
    have hp : lowerPayment 3319 = (349835967677:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3319+point 2 split 4096 3320)/2 = (530911109:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((530911109:ℝ)/168755200)/ClassicalSixthBranch.v ((530911109:ℝ)/168755200) = (557372435861:ℝ)/261216275432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3319
  · change lowerPayment 3320 ≤ lowerValue ((point 2 split 4096 3320+point 2 split 4096 3321)/2)
    have hp : lowerPayment 3320 = (349926706504:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3320+point 2 split 4096 3321)/2 = (530969371:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((530969371:ℝ)/168755200)/ClassicalSixthBranch.v ((530969371:ℝ)/168755200) = (557295122187:ℝ)/261168267544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3320
  · change lowerPayment 3321 ≤ lowerValue ((point 2 split 4096 3321+point 2 split 4096 3322)/2)
    have hp : lowerPayment 3321 = (350017454606:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3321+point 2 split 4096 3322)/2 = (531027633:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((531027633:ℝ)/168755200)/ClassicalSixthBranch.v ((531027633:ℝ)/168755200) = (557217808513:ℝ)/261120259656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3321
  · change lowerPayment 3322 ≤ lowerValue ((point 2 split 4096 3322+point 2 split 4096 3323)/2)
    have hp : lowerPayment 3322 = (350108211998:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3322+point 2 split 4096 3323)/2 = (106217179:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((106217179:ℝ)/33751040)/ClassicalSixthBranch.v ((106217179:ℝ)/33751040) = (557140494839:ℝ)/261072251768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3322
  · change lowerPayment 3323 ≤ lowerValue ((point 2 split 4096 3323+point 2 split 4096 3324)/2)
    have hp : lowerPayment 3323 = (350198978695:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3323+point 2 split 4096 3324)/2 = (531144157:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((531144157:ℝ)/168755200)/ClassicalSixthBranch.v ((531144157:ℝ)/168755200) = (111412636233:ℝ)/52204848776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3323
  · change lowerPayment 3324 ≤ lowerValue ((point 2 split 4096 3324+point 2 split 4096 3325)/2)
    have hp : lowerPayment 3324 = (350289754712:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3324+point 2 split 4096 3325)/2 = (531202419:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((531202419:ℝ)/168755200)/ClassicalSixthBranch.v ((531202419:ℝ)/168755200) = (556985867491:ℝ)/260976235992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3324
  · change lowerPayment 3325 ≤ lowerValue ((point 2 split 4096 3325+point 2 split 4096 3326)/2)
    have hp : lowerPayment 3325 = (350380540063:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3325+point 2 split 4096 3326)/2 = (531260681:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((531260681:ℝ)/168755200)/ClassicalSixthBranch.v ((531260681:ℝ)/168755200) = (556908553817:ℝ)/260928228104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3325
  · change lowerPayment 3326 ≤ lowerValue ((point 2 split 4096 3326+point 2 split 4096 3327)/2)
    have hp : lowerPayment 3326 = (350471334764:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3326+point 2 split 4096 3327)/2 = (531318943:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((531318943:ℝ)/168755200)/ClassicalSixthBranch.v ((531318943:ℝ)/168755200) = (556831240143:ℝ)/260880220216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3326
  · change lowerPayment 3327 ≤ lowerValue ((point 2 split 4096 3327+point 2 split 4096 3328)/2)
    have hp : lowerPayment 3327 = (350562138830:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3327+point 2 split 4096 3328)/2 = (106275441:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((106275441:ℝ)/33751040)/ClassicalSixthBranch.v ((106275441:ℝ)/33751040) = (556753926469:ℝ)/260832212328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3327
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_207
