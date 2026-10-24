import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints202
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_202 (j : Fin 16) : lowerPayment (16*202+j.val) ≤
    lowerValue ((point 2 split 4096 (16*202+j.val)+point 2 split 4096 (16*202+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3232 ≤ lowerValue ((point 2 split 4096 3232+point 2 split 4096 3233)/2)
    have hp : lowerPayment 3232 = (341975520254:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3232+point 2 split 4096 3233)/2 = (105168463:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((105168463:ℝ)/33751040)/ClassicalSixthBranch.v ((105168463:ℝ)/33751040) = (564098725499:ℝ)/265392961688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3232
  · change lowerPayment 3233 ≤ lowerValue ((point 2 split 4096 3233+point 2 split 4096 3234)/2)
    have hp : lowerPayment 3233 = (342065508526:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3233+point 2 split 4096 3234)/2 = (525900577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((525900577:ℝ)/168755200)/ClassicalSixthBranch.v ((525900577:ℝ)/168755200) = (22560856473:ℝ)/10613798152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3233
  · change lowerPayment 3234 ≤ lowerValue ((point 2 split 4096 3234+point 2 split 4096 3235)/2)
    have hp : lowerPayment 3234 = (342155504796:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3234+point 2 split 4096 3235)/2 = (525958839:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((525958839:ℝ)/168755200)/ClassicalSixthBranch.v ((525958839:ℝ)/168755200) = (563944098151:ℝ)/265296945912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3234
  · change lowerPayment 3235 ≤ lowerValue ((point 2 split 4096 3235+point 2 split 4096 3236)/2)
    have hp : lowerPayment 3235 = (342245509077:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3235+point 2 split 4096 3236)/2 = (526017101:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((526017101:ℝ)/168755200)/ClassicalSixthBranch.v ((526017101:ℝ)/168755200) = (563866784477:ℝ)/265248938024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3235
  · change lowerPayment 3236 ≤ lowerValue ((point 2 split 4096 3236+point 2 split 4096 3237)/2)
    have hp : lowerPayment 3236 = (342335521384:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3236+point 2 split 4096 3237)/2 = (526075363:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((526075363:ℝ)/168755200)/ClassicalSixthBranch.v ((526075363:ℝ)/168755200) = (563789470803:ℝ)/265200930136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3236
  · change lowerPayment 3237 ≤ lowerValue ((point 2 split 4096 3237+point 2 split 4096 3238)/2)
    have hp : lowerPayment 3237 = (342425541733:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3237+point 2 split 4096 3238)/2 = (21045345:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((21045345:ℝ)/6750208)/ClassicalSixthBranch.v ((21045345:ℝ)/6750208) = (563712157129:ℝ)/265152922248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3237
  · change lowerPayment 3238 ≤ lowerValue ((point 2 split 4096 3238+point 2 split 4096 3239)/2)
    have hp : lowerPayment 3238 = (342515570136:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3238+point 2 split 4096 3239)/2 = (526191887:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((526191887:ℝ)/168755200)/ClassicalSixthBranch.v ((526191887:ℝ)/168755200) = (112726968691:ℝ)/53020982872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3238
  · change lowerPayment 3239 ≤ lowerValue ((point 2 split 4096 3239+point 2 split 4096 3240)/2)
    have hp : lowerPayment 3239 = (342605606609:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3239+point 2 split 4096 3240)/2 = (526250149:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((526250149:ℝ)/168755200)/ClassicalSixthBranch.v ((526250149:ℝ)/168755200) = (563557529781:ℝ)/265056906472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3239
  · change lowerPayment 3240 ≤ lowerValue ((point 2 split 4096 3240+point 2 split 4096 3241)/2)
    have hp : lowerPayment 3240 = (342695651167:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3240+point 2 split 4096 3241)/2 = (526308411:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((526308411:ℝ)/168755200)/ClassicalSixthBranch.v ((526308411:ℝ)/168755200) = (563480216107:ℝ)/265008898584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3240
  · change lowerPayment 3241 ≤ lowerValue ((point 2 split 4096 3241+point 2 split 4096 3242)/2)
    have hp : lowerPayment 3241 = (342785703824:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3241+point 2 split 4096 3242)/2 = (526366673:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((526366673:ℝ)/168755200)/ClassicalSixthBranch.v ((526366673:ℝ)/168755200) = (563402902433:ℝ)/264960890696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3241
  · change lowerPayment 3242 ≤ lowerValue ((point 2 split 4096 3242+point 2 split 4096 3243)/2)
    have hp : lowerPayment 3242 = (342875764595:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3242+point 2 split 4096 3243)/2 = (105284987:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((105284987:ℝ)/33751040)/ClassicalSixthBranch.v ((105284987:ℝ)/33751040) = (563325588759:ℝ)/264912882808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3242
  · change lowerPayment 3243 ≤ lowerValue ((point 2 split 4096 3243+point 2 split 4096 3244)/2)
    have hp : lowerPayment 3243 = (342965833494:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3243+point 2 split 4096 3244)/2 = (526483197:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((526483197:ℝ)/168755200)/ClassicalSixthBranch.v ((526483197:ℝ)/168755200) = (112649655017:ℝ)/52972974984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3243
  · change lowerPayment 3244 ≤ lowerValue ((point 2 split 4096 3244+point 2 split 4096 3245)/2)
    have hp : lowerPayment 3244 = (343055910535:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3244+point 2 split 4096 3245)/2 = (5112053:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((5112053:ℝ)/1638400)/ClassicalSixthBranch.v ((5112053:ℝ)/1638400) = (5467679237:ℝ)/2571037544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3244
  · change lowerPayment 3245 ≤ lowerValue ((point 2 split 4096 3245+point 2 split 4096 3246)/2)
    have hp : lowerPayment 3245 = (343145995735:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3245+point 2 split 4096 3246)/2 = (526599721:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((526599721:ℝ)/168755200)/ClassicalSixthBranch.v ((526599721:ℝ)/168755200) = (563093647737:ℝ)/264768859144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3245
  · change lowerPayment 3246 ≤ lowerValue ((point 2 split 4096 3246+point 2 split 4096 3247)/2)
    have hp : lowerPayment 3246 = (343236089106:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3246+point 2 split 4096 3247)/2 = (526657983:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((526657983:ℝ)/168755200)/ClassicalSixthBranch.v ((526657983:ℝ)/168755200) = (563016334063:ℝ)/264720851256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3246
  · change lowerPayment 3247 ≤ lowerValue ((point 2 split 4096 3247+point 2 split 4096 3248)/2)
    have hp : lowerPayment 3247 = (343326190664:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3247+point 2 split 4096 3248)/2 = (105343249:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((105343249:ℝ)/33751040)/ClassicalSixthBranch.v ((105343249:ℝ)/33751040) = (562939020389:ℝ)/264672843368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3247
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_202
