import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints012
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_012 (j : Fin 16) : upperPayment (16*12+j.val) ≤
    upperValue ((point split endpoint 4096 (16*12+j.val)+point split endpoint 4096 (16*12+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 192 ≤ upperValue ((point split endpoint 4096 192+point split endpoint 4096 193)/2)
    have hp : upperPayment 192 = (413538921904:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 192+point split endpoint 4096 193)/2 = (580992927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580992927:ℝ)/168755200)*ClassicalSixthBranch.v ((580992927:ℝ)/168755200)/ClassicalSixthBranch.r = (157997005188945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_192
  · change upperPayment 193 ≤ upperValue ((point split endpoint 4096 193+point split endpoint 4096 194)/2)
    have hp : upperPayment 193 = (413481102127:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 193+point split endpoint 4096 194)/2 = (581018077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581018077:ℝ)/168755200)*ClassicalSixthBranch.v ((581018077:ℝ)/168755200)/ClassicalSixthBranch.r = (157971378517977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_193
  · change upperPayment 194 ≤ upperValue ((point split endpoint 4096 194+point split endpoint 4096 195)/2)
    have hp : upperPayment 194 = (413423262676:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 194+point split endpoint 4096 195)/2 = (581043227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581043227:ℝ)/168755200)*ClassicalSixthBranch.v ((581043227:ℝ)/168755200)/ClassicalSixthBranch.r = (157945753871081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_194
  · change upperPayment 195 ≤ upperValue ((point split endpoint 4096 195+point split endpoint 4096 196)/2)
    have hp : upperPayment 195 = (413365403547:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 195+point split endpoint 4096 196)/2 = (581068377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581068377:ℝ)/168755200)*ClassicalSixthBranch.v ((581068377:ℝ)/168755200)/ClassicalSixthBranch.r = (157920131248257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_195
  · change upperPayment 196 ≤ upperValue ((point split endpoint 4096 196+point split endpoint 4096 197)/2)
    have hp : upperPayment 196 = (413307524739:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 196+point split endpoint 4096 197)/2 = (581093527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581093527:ℝ)/168755200)*ClassicalSixthBranch.v ((581093527:ℝ)/168755200)/ClassicalSixthBranch.r = (157894510649505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_196
  · change upperPayment 197 ≤ upperValue ((point split endpoint 4096 197+point split endpoint 4096 198)/2)
    have hp : upperPayment 197 = (413249626249:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 197+point split endpoint 4096 198)/2 = (581118677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581118677:ℝ)/168755200)*ClassicalSixthBranch.v ((581118677:ℝ)/168755200)/ClassicalSixthBranch.r = (157868892074825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_197
  · change upperPayment 198 ≤ upperValue ((point split endpoint 4096 198+point split endpoint 4096 199)/2)
    have hp : upperPayment 198 = (413191708074:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 198+point split endpoint 4096 199)/2 = (581143827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581143827:ℝ)/168755200)*ClassicalSixthBranch.v ((581143827:ℝ)/168755200)/ClassicalSixthBranch.r = (157843275524217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_198
  · change upperPayment 199 ≤ upperValue ((point split endpoint 4096 199+point split endpoint 4096 200)/2)
    have hp : upperPayment 199 = (413133770214:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 199+point split endpoint 4096 200)/2 = (581168977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581168977:ℝ)/168755200)*ClassicalSixthBranch.v ((581168977:ℝ)/168755200)/ClassicalSixthBranch.r = (157817660997681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_199
  · change upperPayment 200 ≤ upperValue ((point split endpoint 4096 200+point split endpoint 4096 201)/2)
    have hp : upperPayment 200 = (413075812664:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 200+point split endpoint 4096 201)/2 = (581194127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581194127:ℝ)/168755200)*ClassicalSixthBranch.v ((581194127:ℝ)/168755200)/ClassicalSixthBranch.r = (157792048495217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_200
  · change upperPayment 201 ≤ upperValue ((point split endpoint 4096 201+point split endpoint 4096 202)/2)
    have hp : upperPayment 201 = (413017835424:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 201+point split endpoint 4096 202)/2 = (581219277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581219277:ℝ)/168755200)*ClassicalSixthBranch.v ((581219277:ℝ)/168755200)/ClassicalSixthBranch.r = (157766438016825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_201
  · change upperPayment 202 ≤ upperValue ((point split endpoint 4096 202+point split endpoint 4096 203)/2)
    have hp : upperPayment 202 = (412959838490:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 202+point split endpoint 4096 203)/2 = (581244427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581244427:ℝ)/168755200)*ClassicalSixthBranch.v ((581244427:ℝ)/168755200)/ClassicalSixthBranch.r = (157740829562505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_202
  · change upperPayment 203 ≤ upperValue ((point split endpoint 4096 203+point split endpoint 4096 204)/2)
    have hp : upperPayment 203 = (412901821860:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 203+point split endpoint 4096 204)/2 = (581269577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581269577:ℝ)/168755200)*ClassicalSixthBranch.v ((581269577:ℝ)/168755200)/ClassicalSixthBranch.r = (157715223132257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_203
  · change upperPayment 204 ≤ upperValue ((point split endpoint 4096 204+point split endpoint 4096 205)/2)
    have hp : upperPayment 204 = (412843785531:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 204+point split endpoint 4096 205)/2 = (581294727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581294727:ℝ)/168755200)*ClassicalSixthBranch.v ((581294727:ℝ)/168755200)/ClassicalSixthBranch.r = (157689618726081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_204
  · change upperPayment 205 ≤ upperValue ((point split endpoint 4096 205+point split endpoint 4096 206)/2)
    have hp : upperPayment 205 = (412785729503:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 205+point split endpoint 4096 206)/2 = (581319877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581319877:ℝ)/168755200)*ClassicalSixthBranch.v ((581319877:ℝ)/168755200)/ClassicalSixthBranch.r = (157664016343977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_205
  · change upperPayment 206 ≤ upperValue ((point split endpoint 4096 206+point split endpoint 4096 207)/2)
    have hp : upperPayment 206 = (412727653771:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 206+point split endpoint 4096 207)/2 = (581345027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581345027:ℝ)/168755200)*ClassicalSixthBranch.v ((581345027:ℝ)/168755200)/ClassicalSixthBranch.r = (157638415985945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_206
  · change upperPayment 207 ≤ upperValue ((point split endpoint 4096 207+point split endpoint 4096 208)/2)
    have hp : upperPayment 207 = (412669558334:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 207+point split endpoint 4096 208)/2 = (581370177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581370177:ℝ)/168755200)*ClassicalSixthBranch.v ((581370177:ℝ)/168755200)/ClassicalSixthBranch.r = (157612817651985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_207
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_012
