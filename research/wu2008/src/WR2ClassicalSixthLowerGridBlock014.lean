import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints014
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_014 (j : Fin 16) : lowerPayment (16*14+j.val) ≤
    lowerValue ((point 2 split 4096 (16*14+j.val)+point 2 split 4096 (16*14+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 224 ≤ lowerValue ((point 2 split 4096 224+point 2 split 4096 225)/2)
    have hp : lowerPayment 224 = (34775023780:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 224+point 2 split 4096 225)/2 = (350590219:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((350590219:ℝ)/168755200)/ClassicalSixthBranch.v ((350590219:ℝ)/168755200) = (796658256891:ℝ)/409800688792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_224
  · change lowerPayment 225 ≤ lowerValue ((point 2 split 4096 225+point 2 split 4096 226)/2)
    have hp : lowerPayment 225 = (34922157956:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 225+point 2 split 4096 226)/2 = (350648481:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((350648481:ℝ)/168755200)/ClassicalSixthBranch.v ((350648481:ℝ)/168755200) = (796580943217:ℝ)/409752680904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_225
  · change lowerPayment 226 ≤ lowerValue ((point 2 split 4096 226+point 2 split 4096 227)/2)
    have hp : lowerPayment 226 = (35069227876:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 226+point 2 split 4096 227)/2 = (350706743:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((350706743:ℝ)/168755200)/ClassicalSixthBranch.v ((350706743:ℝ)/168755200) = (796503629543:ℝ)/409704673016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_226
  · change lowerPayment 227 ≤ lowerValue ((point 2 split 4096 227+point 2 split 4096 228)/2)
    have hp : lowerPayment 227 = (35216233600:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 227+point 2 split 4096 228)/2 = (70153001:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((70153001:ℝ)/33751040)/ClassicalSixthBranch.v ((70153001:ℝ)/33751040) = (796426315869:ℝ)/409656665128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_227
  · change lowerPayment 228 ≤ lowerValue ((point 2 split 4096 228+point 2 split 4096 229)/2)
    have hp : lowerPayment 228 = (35363175183:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 228+point 2 split 4096 229)/2 = (350823267:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((350823267:ℝ)/168755200)/ClassicalSixthBranch.v ((350823267:ℝ)/168755200) = (159269800439:ℝ)/81921731448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_228
  · change lowerPayment 229 ≤ lowerValue ((point 2 split 4096 229+point 2 split 4096 230)/2)
    have hp : lowerPayment 229 = (35510052685:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 229+point 2 split 4096 230)/2 = (350881529:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((350881529:ℝ)/168755200)/ClassicalSixthBranch.v ((350881529:ℝ)/168755200) = (796271688521:ℝ)/409560649352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_229
  · change lowerPayment 230 ≤ lowerValue ((point 2 split 4096 230+point 2 split 4096 231)/2)
    have hp : lowerPayment 230 = (35656866163:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 230+point 2 split 4096 231)/2 = (350939791:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((350939791:ℝ)/168755200)/ClassicalSixthBranch.v ((350939791:ℝ)/168755200) = (796194374847:ℝ)/409512641464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_230
  · change lowerPayment 231 ≤ lowerValue ((point 2 split 4096 231+point 2 split 4096 232)/2)
    have hp : lowerPayment 231 = (35803615674:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 231+point 2 split 4096 232)/2 = (350998053:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((350998053:ℝ)/168755200)/ClassicalSixthBranch.v ((350998053:ℝ)/168755200) = (796117061173:ℝ)/409464633576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_231
  · change lowerPayment 232 ≤ lowerValue ((point 2 split 4096 232+point 2 split 4096 233)/2)
    have hp : lowerPayment 232 = (35950301275:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 232+point 2 split 4096 233)/2 = (70211263:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((70211263:ℝ)/33751040)/ClassicalSixthBranch.v ((70211263:ℝ)/33751040) = (796039747499:ℝ)/409416625688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_232
  · change lowerPayment 233 ≤ lowerValue ((point 2 split 4096 233+point 2 split 4096 234)/2)
    have hp : lowerPayment 233 = (36096923025:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 233+point 2 split 4096 234)/2 = (351114577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((351114577:ℝ)/168755200)/ClassicalSixthBranch.v ((351114577:ℝ)/168755200) = (31838497353:ℝ)/16374744712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_233
  · change lowerPayment 234 ≤ lowerValue ((point 2 split 4096 234+point 2 split 4096 235)/2)
    have hp : lowerPayment 234 = (36243480980:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 234+point 2 split 4096 235)/2 = (351172839:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((351172839:ℝ)/168755200)/ClassicalSixthBranch.v ((351172839:ℝ)/168755200) = (795885120151:ℝ)/409320609912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_234
  · change lowerPayment 235 ≤ lowerValue ((point 2 split 4096 235+point 2 split 4096 236)/2)
    have hp : lowerPayment 235 = (36389975198:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 235+point 2 split 4096 236)/2 = (351231101:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((351231101:ℝ)/168755200)/ClassicalSixthBranch.v ((351231101:ℝ)/168755200) = (795807806477:ℝ)/409272602024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_235
  · change lowerPayment 236 ≤ lowerValue ((point 2 split 4096 236+point 2 split 4096 237)/2)
    have hp : lowerPayment 236 = (36536405736:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 236+point 2 split 4096 237)/2 = (351289363:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((351289363:ℝ)/168755200)/ClassicalSixthBranch.v ((351289363:ℝ)/168755200) = (795730492803:ℝ)/409224594136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_236
  · change lowerPayment 237 ≤ lowerValue ((point 2 split 4096 237+point 2 split 4096 238)/2)
    have hp : lowerPayment 237 = (36682772651:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 237+point 2 split 4096 238)/2 = (14053905:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((14053905:ℝ)/6750208)/ClassicalSixthBranch.v ((14053905:ℝ)/6750208) = (795653179129:ℝ)/409176586248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_237
  · change lowerPayment 238 ≤ lowerValue ((point 2 split 4096 238+point 2 split 4096 239)/2)
    have hp : lowerPayment 238 = (36829076001:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 238+point 2 split 4096 239)/2 = (351405887:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((351405887:ℝ)/168755200)/ClassicalSixthBranch.v ((351405887:ℝ)/168755200) = (159115173091:ℝ)/81825715672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_238
  · change lowerPayment 239 ≤ lowerValue ((point 2 split 4096 239+point 2 split 4096 240)/2)
    have hp : lowerPayment 239 = (36975315842:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 239+point 2 split 4096 240)/2 = (351464149:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((351464149:ℝ)/168755200)/ClassicalSixthBranch.v ((351464149:ℝ)/168755200) = (795498551781:ℝ)/409080570472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_239
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_014
