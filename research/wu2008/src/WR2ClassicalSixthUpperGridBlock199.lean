import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints199
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_199 (j : Fin 16) : upperPayment (16*199+j.val) ≤
    upperValue ((point split endpoint 4096 (16*199+j.val)+point split endpoint 4096 (16*199+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3184 ≤ upperValue ((point split endpoint 4096 3184+point split endpoint 4096 3185)/2)
    have hp : upperPayment 3184 = (137321182134:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3184+point split endpoint 4096 3185)/2 = (656241727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656241727:ℝ)/168755200)*ClassicalSixthBranch.v ((656241727:ℝ)/168755200)/ClassicalSixthBranch.r = (90378788683281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3184
  · change upperPayment 3185 ≤ upperValue ((point split endpoint 4096 3185+point split endpoint 4096 3186)/2)
    have hp : upperPayment 3185 = (137187311223:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3185+point split endpoint 4096 3186)/2 = (656266877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656266877:ℝ)/168755200)*ClassicalSixthBranch.v ((656266877:ℝ)/168755200)/ClassicalSixthBranch.r = (90359218035737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3185
  · change upperPayment 3186 ≤ upperValue ((point split endpoint 4096 3186+point split endpoint 4096 3187)/2)
    have hp : upperPayment 3186 = (137053406233:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3186+point split endpoint 4096 3187)/2 = (656292027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656292027:ℝ)/168755200)*ClassicalSixthBranch.v ((656292027:ℝ)/168755200)/ClassicalSixthBranch.r = (90339649412265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3186
  · change upperPayment 3187 ≤ upperValue ((point split endpoint 4096 3187+point split endpoint 4096 3188)/2)
    have hp : upperPayment 3187 = (136919467157:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3187+point split endpoint 4096 3188)/2 = (656317177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656317177:ℝ)/168755200)*ClassicalSixthBranch.v ((656317177:ℝ)/168755200)/ClassicalSixthBranch.r = (90320082812865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3187
  · change upperPayment 3188 ≤ upperValue ((point split endpoint 4096 3188+point split endpoint 4096 3189)/2)
    have hp : upperPayment 3188 = (136785493986:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3188+point split endpoint 4096 3189)/2 = (656342327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656342327:ℝ)/168755200)*ClassicalSixthBranch.v ((656342327:ℝ)/168755200)/ClassicalSixthBranch.r = (90300518237537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3188
  · change upperPayment 3189 ≤ upperValue ((point split endpoint 4096 3189+point split endpoint 4096 3190)/2)
    have hp : upperPayment 3189 = (136651486712:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3189+point split endpoint 4096 3190)/2 = (656367477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656367477:ℝ)/168755200)*ClassicalSixthBranch.v ((656367477:ℝ)/168755200)/ClassicalSixthBranch.r = (90280955686281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3189
  · change upperPayment 3190 ≤ upperValue ((point split endpoint 4096 3190+point split endpoint 4096 3191)/2)
    have hp : upperPayment 3190 = (136517445326:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3190+point split endpoint 4096 3191)/2 = (656392627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656392627:ℝ)/168755200)*ClassicalSixthBranch.v ((656392627:ℝ)/168755200)/ClassicalSixthBranch.r = (90261395159097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3190
  · change upperPayment 3191 ≤ upperValue ((point split endpoint 4096 3191+point split endpoint 4096 3192)/2)
    have hp : upperPayment 3191 = (136383369819:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3191+point split endpoint 4096 3192)/2 = (656417777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656417777:ℝ)/168755200)*ClassicalSixthBranch.v ((656417777:ℝ)/168755200)/ClassicalSixthBranch.r = (90241836655985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3191
  · change upperPayment 3192 ≤ upperValue ((point split endpoint 4096 3192+point split endpoint 4096 3193)/2)
    have hp : upperPayment 3192 = (136249260184:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3192+point split endpoint 4096 3193)/2 = (656442927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656442927:ℝ)/168755200)*ClassicalSixthBranch.v ((656442927:ℝ)/168755200)/ClassicalSixthBranch.r = (90222280176945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3192
  · change upperPayment 3193 ≤ upperValue ((point split endpoint 4096 3193+point split endpoint 4096 3194)/2)
    have hp : upperPayment 3193 = (136115116413:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3193+point split endpoint 4096 3194)/2 = (656468077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656468077:ℝ)/168755200)*ClassicalSixthBranch.v ((656468077:ℝ)/168755200)/ClassicalSixthBranch.r = (90202725721977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3193
  · change upperPayment 3194 ≤ upperValue ((point split endpoint 4096 3194+point split endpoint 4096 3195)/2)
    have hp : upperPayment 3194 = (135980938496:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3194+point split endpoint 4096 3195)/2 = (656493227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656493227:ℝ)/168755200)*ClassicalSixthBranch.v ((656493227:ℝ)/168755200)/ClassicalSixthBranch.r = (90183173291081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3194
  · change upperPayment 3195 ≤ upperValue ((point split endpoint 4096 3195+point split endpoint 4096 3196)/2)
    have hp : upperPayment 3195 = (135846726425:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3195+point split endpoint 4096 3196)/2 = (656518377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656518377:ℝ)/168755200)*ClassicalSixthBranch.v ((656518377:ℝ)/168755200)/ClassicalSixthBranch.r = (90163622884257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3195
  · change upperPayment 3196 ≤ upperValue ((point split endpoint 4096 3196+point split endpoint 4096 3197)/2)
    have hp : upperPayment 3196 = (135712480193:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3196+point split endpoint 4096 3197)/2 = (6374209:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((6374209:ℝ)/1638400)*ClassicalSixthBranch.v ((6374209:ℝ)/1638400)/ClassicalSixthBranch.r = (875185189335:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3196
  · change upperPayment 3197 ≤ upperValue ((point split endpoint 4096 3197+point split endpoint 4096 3198)/2)
    have hp : upperPayment 3197 = (135578199790:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3197+point split endpoint 4096 3198)/2 = (656568677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656568677:ℝ)/168755200)*ClassicalSixthBranch.v ((656568677:ℝ)/168755200)/ClassicalSixthBranch.r = (90124528142825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3197
  · change upperPayment 3198 ≤ upperValue ((point split endpoint 4096 3198+point split endpoint 4096 3199)/2)
    have hp : upperPayment 3198 = (135443885209:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3198+point split endpoint 4096 3199)/2 = (656593827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656593827:ℝ)/168755200)*ClassicalSixthBranch.v ((656593827:ℝ)/168755200)/ClassicalSixthBranch.r = (90104983808217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3198
  · change upperPayment 3199 ≤ upperValue ((point split endpoint 4096 3199+point split endpoint 4096 3200)/2)
    have hp : upperPayment 3199 = (135309536440:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3199+point split endpoint 4096 3200)/2 = (656618977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656618977:ℝ)/168755200)*ClassicalSixthBranch.v ((656618977:ℝ)/168755200)/ClassicalSixthBranch.r = (90085441497681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3199
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_199
