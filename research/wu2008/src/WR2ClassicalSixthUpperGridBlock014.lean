import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints014
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_014 (j : Fin 16) : upperPayment (16*14+j.val) ≤
    upperValue ((point split endpoint 4096 (16*14+j.val)+point split endpoint 4096 (16*14+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 224 ≤ upperValue ((point split endpoint 4096 224+point split endpoint 4096 225)/2)
    have hp : upperPayment 224 = (411678918731:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 224+point split endpoint 4096 225)/2 = (581797727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581797727:ℝ)/168755200)*ClassicalSixthBranch.v ((581797727:ℝ)/168755200)/ClassicalSixthBranch.r = (157177955657681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_224
  · change upperPayment 225 ≤ upperValue ((point split endpoint 4096 225+point split endpoint 4096 226)/2)
    have hp : upperPayment 225 = (411620468197:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 225+point split endpoint 4096 226)/2 = (581822877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581822877:ℝ)/168755200)*ClassicalSixthBranch.v ((581822877:ℝ)/168755200)/ClassicalSixthBranch.r = (157152393757017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_225
  · change upperPayment 226 ≤ upperValue ((point split endpoint 4096 226+point split endpoint 4096 227)/2)
    have hp : upperPayment 226 = (411561997914:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 226+point split endpoint 4096 227)/2 = (581848027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581848027:ℝ)/168755200)*ClassicalSixthBranch.v ((581848027:ℝ)/168755200)/ClassicalSixthBranch.r = (157126833880425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_226
  · change upperPayment 227 ≤ upperValue ((point split endpoint 4096 227+point split endpoint 4096 228)/2)
    have hp : upperPayment 227 = (411503507878:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 227+point split endpoint 4096 228)/2 = (581873177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581873177:ℝ)/168755200)*ClassicalSixthBranch.v ((581873177:ℝ)/168755200)/ClassicalSixthBranch.r = (157101276027905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_227
  · change upperPayment 228 ≤ upperValue ((point split endpoint 4096 228+point split endpoint 4096 229)/2)
    have hp : upperPayment 228 = (411444998087:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 228+point split endpoint 4096 229)/2 = (581898327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581898327:ℝ)/168755200)*ClassicalSixthBranch.v ((581898327:ℝ)/168755200)/ClassicalSixthBranch.r = (157075720199457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_228
  · change upperPayment 229 ≤ upperValue ((point split endpoint 4096 229+point split endpoint 4096 230)/2)
    have hp : upperPayment 229 = (411386468539:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 229+point split endpoint 4096 230)/2 = (581923477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581923477:ℝ)/168755200)*ClassicalSixthBranch.v ((581923477:ℝ)/168755200)/ClassicalSixthBranch.r = (157050166395081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_229
  · change upperPayment 230 ≤ upperValue ((point split endpoint 4096 230+point split endpoint 4096 231)/2)
    have hp : upperPayment 230 = (411327919232:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 230+point split endpoint 4096 231)/2 = (581948627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581948627:ℝ)/168755200)*ClassicalSixthBranch.v ((581948627:ℝ)/168755200)/ClassicalSixthBranch.r = (157024614614777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_230
  · change upperPayment 231 ≤ upperValue ((point split endpoint 4096 231+point split endpoint 4096 232)/2)
    have hp : upperPayment 231 = (411269350163:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 231+point split endpoint 4096 232)/2 = (581973777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581973777:ℝ)/168755200)*ClassicalSixthBranch.v ((581973777:ℝ)/168755200)/ClassicalSixthBranch.r = (156999064858545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_231
  · change upperPayment 232 ≤ upperValue ((point split endpoint 4096 232+point split endpoint 4096 233)/2)
    have hp : upperPayment 232 = (411210761329:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 232+point split endpoint 4096 233)/2 = (581998927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581998927:ℝ)/168755200)*ClassicalSixthBranch.v ((581998927:ℝ)/168755200)/ClassicalSixthBranch.r = (156973517126385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_232
  · change upperPayment 233 ≤ upperValue ((point split endpoint 4096 233+point split endpoint 4096 234)/2)
    have hp : upperPayment 233 = (411152152729:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 233+point split endpoint 4096 234)/2 = (582024077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582024077:ℝ)/168755200)*ClassicalSixthBranch.v ((582024077:ℝ)/168755200)/ClassicalSixthBranch.r = (1523766712799:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_233
  · change upperPayment 234 ≤ upperValue ((point split endpoint 4096 234+point split endpoint 4096 235)/2)
    have hp : upperPayment 234 = (411093524360:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 234+point split endpoint 4096 235)/2 = (582049227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582049227:ℝ)/168755200)*ClassicalSixthBranch.v ((582049227:ℝ)/168755200)/ClassicalSixthBranch.r = (156922427734281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_234
  · change upperPayment 235 ≤ upperValue ((point split endpoint 4096 235+point split endpoint 4096 236)/2)
    have hp : upperPayment 235 = (411034876219:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 235+point split endpoint 4096 236)/2 = (582074377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582074377:ℝ)/168755200)*ClassicalSixthBranch.v ((582074377:ℝ)/168755200)/ClassicalSixthBranch.r = (156896886074337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_235
  · change upperPayment 236 ≤ upperValue ((point split endpoint 4096 236+point split endpoint 4096 237)/2)
    have hp : upperPayment 236 = (410976208305:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 236+point split endpoint 4096 237)/2 = (582099527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582099527:ℝ)/168755200)*ClassicalSixthBranch.v ((582099527:ℝ)/168755200)/ClassicalSixthBranch.r = (156871346438465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_236
  · change upperPayment 237 ≤ upperValue ((point split endpoint 4096 237+point split endpoint 4096 238)/2)
    have hp : upperPayment 237 = (410917520614:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 237+point split endpoint 4096 238)/2 = (582124677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582124677:ℝ)/168755200)*ClassicalSixthBranch.v ((582124677:ℝ)/168755200)/ClassicalSixthBranch.r = (156845808826665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_237
  · change upperPayment 238 ≤ upperValue ((point split endpoint 4096 238+point split endpoint 4096 239)/2)
    have hp : upperPayment 238 = (410858813145:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 238+point split endpoint 4096 239)/2 = (582149827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582149827:ℝ)/168755200)*ClassicalSixthBranch.v ((582149827:ℝ)/168755200)/ClassicalSixthBranch.r = (156820273238937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_238
  · change upperPayment 239 ≤ upperValue ((point split endpoint 4096 239+point split endpoint 4096 240)/2)
    have hp : upperPayment 239 = (410800085895:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 239+point split endpoint 4096 240)/2 = (582174977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582174977:ℝ)/168755200)*ClassicalSixthBranch.v ((582174977:ℝ)/168755200)/ClassicalSixthBranch.r = (156794739675281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_239
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_014
