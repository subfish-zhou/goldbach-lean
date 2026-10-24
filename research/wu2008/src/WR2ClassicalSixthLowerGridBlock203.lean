import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints203
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_203 (j : Fin 16) : lowerPayment (16*203+j.val) ≤
    lowerValue ((point 2 split 4096 (16*203+j.val)+point 2 split 4096 (16*203+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3248 ≤ lowerValue ((point 2 split 4096 3248+point 2 split 4096 3249)/2)
    have hp : lowerPayment 3248 = (343416300423:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3248+point 2 split 4096 3249)/2 = (526774507:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((526774507:ℝ)/168755200)/ClassicalSixthBranch.v ((526774507:ℝ)/168755200) = (112572341343:ℝ)/52924967096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3248
  · change lowerPayment 3249 ≤ lowerValue ((point 2 split 4096 3249+point 2 split 4096 3250)/2)
    have hp : lowerPayment 3249 = (343506418399:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3249+point 2 split 4096 3250)/2 = (526832769:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((526832769:ℝ)/168755200)/ClassicalSixthBranch.v ((526832769:ℝ)/168755200) = (562784393041:ℝ)/264576827592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3249
  · change lowerPayment 3250 ≤ lowerValue ((point 2 split 4096 3250+point 2 split 4096 3251)/2)
    have hp : lowerPayment 3250 = (343596544605:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3250+point 2 split 4096 3251)/2 = (526891031:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((526891031:ℝ)/168755200)/ClassicalSixthBranch.v ((526891031:ℝ)/168755200) = (562707079367:ℝ)/264528819704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3250
  · change lowerPayment 3251 ≤ lowerValue ((point 2 split 4096 3251+point 2 split 4096 3252)/2)
    have hp : lowerPayment 3251 = (343686679055:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3251+point 2 split 4096 3252)/2 = (526949293:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((526949293:ℝ)/168755200)/ClassicalSixthBranch.v ((526949293:ℝ)/168755200) = (562629765693:ℝ)/264480811816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3251
  · change lowerPayment 3252 ≤ lowerValue ((point 2 split 4096 3252+point 2 split 4096 3253)/2)
    have hp : lowerPayment 3252 = (343776821766:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3252+point 2 split 4096 3253)/2 = (105401511:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((105401511:ℝ)/33751040)/ClassicalSixthBranch.v ((105401511:ℝ)/33751040) = (562552452019:ℝ)/264432803928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3252
  · change lowerPayment 3253 ≤ lowerValue ((point 2 split 4096 3253+point 2 split 4096 3254)/2)
    have hp : lowerPayment 3253 = (343866972751:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3253+point 2 split 4096 3254)/2 = (527065817:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((527065817:ℝ)/168755200)/ClassicalSixthBranch.v ((527065817:ℝ)/168755200) = (112495027669:ℝ)/52876959208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3253
  · change lowerPayment 3254 ≤ lowerValue ((point 2 split 4096 3254+point 2 split 4096 3255)/2)
    have hp : lowerPayment 3254 = (343957132025:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3254+point 2 split 4096 3255)/2 = (527124079:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((527124079:ℝ)/168755200)/ClassicalSixthBranch.v ((527124079:ℝ)/168755200) = (562397824671:ℝ)/264336788152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3254
  · change lowerPayment 3255 ≤ lowerValue ((point 2 split 4096 3255+point 2 split 4096 3256)/2)
    have hp : lowerPayment 3255 = (344047299603:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3255+point 2 split 4096 3256)/2 = (527182341:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((527182341:ℝ)/168755200)/ClassicalSixthBranch.v ((527182341:ℝ)/168755200) = (562320510997:ℝ)/264288780264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3255
  · change lowerPayment 3256 ≤ lowerValue ((point 2 split 4096 3256+point 2 split 4096 3257)/2)
    have hp : lowerPayment 3256 = (344137475499:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3256+point 2 split 4096 3257)/2 = (527240603:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((527240603:ℝ)/168755200)/ClassicalSixthBranch.v ((527240603:ℝ)/168755200) = (562243197323:ℝ)/264240772376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3256
  · change lowerPayment 3257 ≤ lowerValue ((point 2 split 4096 3257+point 2 split 4096 3258)/2)
    have hp : lowerPayment 3257 = (344227659728:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3257+point 2 split 4096 3258)/2 = (105459773:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((105459773:ℝ)/33751040)/ClassicalSixthBranch.v ((105459773:ℝ)/33751040) = (562165883649:ℝ)/264192764488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3257
  · change lowerPayment 3258 ≤ lowerValue ((point 2 split 4096 3258+point 2 split 4096 3259)/2)
    have hp : lowerPayment 3258 = (344317852305:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3258+point 2 split 4096 3259)/2 = (527357127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((527357127:ℝ)/168755200)/ClassicalSixthBranch.v ((527357127:ℝ)/168755200) = (22483542799:ℝ)/10565790264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3258
  · change lowerPayment 3259 ≤ lowerValue ((point 2 split 4096 3259+point 2 split 4096 3260)/2)
    have hp : lowerPayment 3259 = (344408053243:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3259+point 2 split 4096 3260)/2 = (527415389:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((527415389:ℝ)/168755200)/ClassicalSixthBranch.v ((527415389:ℝ)/168755200) = (562011256301:ℝ)/264096748712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3259
  · change lowerPayment 3260 ≤ lowerValue ((point 2 split 4096 3260+point 2 split 4096 3261)/2)
    have hp : lowerPayment 3260 = (344498262559:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3260+point 2 split 4096 3261)/2 = (527473651:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((527473651:ℝ)/168755200)/ClassicalSixthBranch.v ((527473651:ℝ)/168755200) = (561933942627:ℝ)/264048740824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3260
  · change lowerPayment 3261 ≤ lowerValue ((point 2 split 4096 3261+point 2 split 4096 3262)/2)
    have hp : lowerPayment 3261 = (344588480266:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3261+point 2 split 4096 3262)/2 = (527531913:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((527531913:ℝ)/168755200)/ClassicalSixthBranch.v ((527531913:ℝ)/168755200) = (561856628953:ℝ)/264000732936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3261
  · change lowerPayment 3262 ≤ lowerValue ((point 2 split 4096 3262+point 2 split 4096 3263)/2)
    have hp : lowerPayment 3262 = (344678706379:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3262+point 2 split 4096 3263)/2 = (21103607:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((21103607:ℝ)/6750208)/ClassicalSixthBranch.v ((21103607:ℝ)/6750208) = (561779315279:ℝ)/263952725048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3262
  · change lowerPayment 3263 ≤ lowerValue ((point 2 split 4096 3263+point 2 split 4096 3264)/2)
    have hp : lowerPayment 3263 = (344768940913:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3263+point 2 split 4096 3264)/2 = (527648437:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((527648437:ℝ)/168755200)/ClassicalSixthBranch.v ((527648437:ℝ)/168755200) = (112340400321:ℝ)/52780943432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3263
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_203
