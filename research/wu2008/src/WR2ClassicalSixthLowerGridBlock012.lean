import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints012
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_012 (j : Fin 16) : lowerPayment (16*12+j.val) ≤
    lowerValue ((point 2 split 4096 (16*12+j.val)+point 2 split 4096 (16*12+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 192 ≤ lowerValue ((point 2 split 4096 192+point 2 split 4096 193)/2)
    have hp : lowerPayment 192 = (30032454898:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 192+point 2 split 4096 193)/2 = (69745167:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((69745167:ℝ)/33751040)/ClassicalSixthBranch.v ((69745167:ℝ)/33751040) = (799132294459:ℝ)/411336941208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_192
  · change lowerPayment 193 ≤ lowerValue ((point 2 split 4096 193+point 2 split 4096 194)/2)
    have hp : lowerPayment 193 = (30181676074:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 193+point 2 split 4096 194)/2 = (348784097:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((348784097:ℝ)/168755200)/ClassicalSixthBranch.v ((348784097:ℝ)/168755200) = (159810996157:ℝ)/82257786664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_193
  · change lowerPayment 194 ≤ lowerValue ((point 2 split 4096 194+point 2 split 4096 195)/2)
    have hp : lowerPayment 194 = (30330831116:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 194+point 2 split 4096 195)/2 = (348842359:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((348842359:ℝ)/168755200)/ClassicalSixthBranch.v ((348842359:ℝ)/168755200) = (798977667111:ℝ)/411240925432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_194
  · change lowerPayment 195 ≤ lowerValue ((point 2 split 4096 195+point 2 split 4096 196)/2)
    have hp : lowerPayment 195 = (30479920084:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 195+point 2 split 4096 196)/2 = (348900621:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((348900621:ℝ)/168755200)/ClassicalSixthBranch.v ((348900621:ℝ)/168755200) = (798900353437:ℝ)/411192917544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_195
  · change lowerPayment 196 ≤ lowerValue ((point 2 split 4096 196+point 2 split 4096 197)/2)
    have hp : lowerPayment 196 = (30628943038:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 196+point 2 split 4096 197)/2 = (348958883:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((348958883:ℝ)/168755200)/ClassicalSixthBranch.v ((348958883:ℝ)/168755200) = (798823039763:ℝ)/411144909656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_196
  · change lowerPayment 197 ≤ lowerValue ((point 2 split 4096 197+point 2 split 4096 198)/2)
    have hp : lowerPayment 197 = (30777900036:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 197+point 2 split 4096 198)/2 = (69803429:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((69803429:ℝ)/33751040)/ClassicalSixthBranch.v ((69803429:ℝ)/33751040) = (798745726089:ℝ)/411096901768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_197
  · change lowerPayment 198 ≤ lowerValue ((point 2 split 4096 198+point 2 split 4096 199)/2)
    have hp : lowerPayment 198 = (30926791139:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 198+point 2 split 4096 199)/2 = (349075407:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((349075407:ℝ)/168755200)/ClassicalSixthBranch.v ((349075407:ℝ)/168755200) = (159733682483:ℝ)/82209778776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_198
  · change lowerPayment 199 ≤ lowerValue ((point 2 split 4096 199+point 2 split 4096 200)/2)
    have hp : lowerPayment 199 = (31075616405:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 199+point 2 split 4096 200)/2 = (349133669:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((349133669:ℝ)/168755200)/ClassicalSixthBranch.v ((349133669:ℝ)/168755200) = (798591098741:ℝ)/411000885992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_199
  · change lowerPayment 200 ≤ lowerValue ((point 2 split 4096 200+point 2 split 4096 201)/2)
    have hp : lowerPayment 200 = (31224375895:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 200+point 2 split 4096 201)/2 = (349191931:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((349191931:ℝ)/168755200)/ClassicalSixthBranch.v ((349191931:ℝ)/168755200) = (798513785067:ℝ)/410952878104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_200
  · change lowerPayment 201 ≤ lowerValue ((point 2 split 4096 201+point 2 split 4096 202)/2)
    have hp : lowerPayment 201 = (31373069667:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 201+point 2 split 4096 202)/2 = (349250193:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((349250193:ℝ)/168755200)/ClassicalSixthBranch.v ((349250193:ℝ)/168755200) = (798436471393:ℝ)/410904870216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_201
  · change lowerPayment 202 ≤ lowerValue ((point 2 split 4096 202+point 2 split 4096 203)/2)
    have hp : lowerPayment 202 = (31521697780:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 202+point 2 split 4096 203)/2 = (69861691:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((69861691:ℝ)/33751040)/ClassicalSixthBranch.v ((69861691:ℝ)/33751040) = (798359157719:ℝ)/410856862328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_202
  · change lowerPayment 203 ≤ lowerValue ((point 2 split 4096 203+point 2 split 4096 204)/2)
    have hp : lowerPayment 203 = (31670260294:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 203+point 2 split 4096 204)/2 = (349366717:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((349366717:ℝ)/168755200)/ClassicalSixthBranch.v ((349366717:ℝ)/168755200) = (159656368809:ℝ)/82161770888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_203
  · change lowerPayment 204 ≤ lowerValue ((point 2 split 4096 204+point 2 split 4096 205)/2)
    have hp : lowerPayment 204 = (31818757268:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 204+point 2 split 4096 205)/2 = (349424979:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((349424979:ℝ)/168755200)/ClassicalSixthBranch.v ((349424979:ℝ)/168755200) = (798204530371:ℝ)/410760846552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_204
  · change lowerPayment 205 ≤ lowerValue ((point 2 split 4096 205+point 2 split 4096 206)/2)
    have hp : lowerPayment 205 = (31967188761:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 205+point 2 split 4096 206)/2 = (349483241:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((349483241:ℝ)/168755200)/ClassicalSixthBranch.v ((349483241:ℝ)/168755200) = (798127216697:ℝ)/410712838664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_205
  · change lowerPayment 206 ≤ lowerValue ((point 2 split 4096 206+point 2 split 4096 207)/2)
    have hp : lowerPayment 206 = (32115554832:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 206+point 2 split 4096 207)/2 = (349541503:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((349541503:ℝ)/168755200)/ClassicalSixthBranch.v ((349541503:ℝ)/168755200) = (798049903023:ℝ)/410664830776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_206
  · change lowerPayment 207 ≤ lowerValue ((point 2 split 4096 207+point 2 split 4096 208)/2)
    have hp : lowerPayment 207 = (32263855539:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 207+point 2 split 4096 208)/2 = (69919953:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((69919953:ℝ)/33751040)/ClassicalSixthBranch.v ((69919953:ℝ)/33751040) = (797972589349:ℝ)/410616822888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_207
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_012
