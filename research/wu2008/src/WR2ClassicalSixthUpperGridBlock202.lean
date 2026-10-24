import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints202
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_202 (j : Fin 16) : upperPayment (16*202+j.val) ≤
    upperValue ((point split endpoint 4096 (16*202+j.val)+point split endpoint 4096 (16*202+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3232 ≤ upperValue ((point split endpoint 4096 3232+point split endpoint 4096 3233)/2)
    have hp : upperPayment 3232 = (130856792992:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3232+point split endpoint 4096 3233)/2 = (657448927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657448927:ℝ)/168755200)*ClassicalSixthBranch.v ((657448927:ℝ)/168755200)/ClassicalSixthBranch.r = (89441680754385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3232
  · change upperPayment 3233 ≤ upperValue ((point split endpoint 4096 3233+point split endpoint 4096 3234)/2)
    have hp : upperPayment 3233 = (130721276846:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3233+point split endpoint 4096 3234)/2 = (657474077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657474077:ℝ)/168755200)*ClassicalSixthBranch.v ((657474077:ℝ)/168755200)/ClassicalSixthBranch.r = (89422207262297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3233
  · change upperPayment 3234 ≤ upperValue ((point split endpoint 4096 3234+point split endpoint 4096 3235)/2)
    have hp : upperPayment 3234 = (130585726216:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3234+point split endpoint 4096 3235)/2 = (657499227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657499227:ℝ)/168755200)*ClassicalSixthBranch.v ((657499227:ℝ)/168755200)/ClassicalSixthBranch.r = (89402735794281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3234
  · change upperPayment 3235 ≤ upperValue ((point split endpoint 4096 3235+point split endpoint 4096 3236)/2)
    have hp : upperPayment 3235 = (130450141095:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3235+point split endpoint 4096 3236)/2 = (657524377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657524377:ℝ)/168755200)*ClassicalSixthBranch.v ((657524377:ℝ)/168755200)/ClassicalSixthBranch.r = (89383266350337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3235
  · change upperPayment 3236 ≤ upperValue ((point split endpoint 4096 3236+point split endpoint 4096 3237)/2)
    have hp : upperPayment 3236 = (130314521474:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3236+point split endpoint 4096 3237)/2 = (657549527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657549527:ℝ)/168755200)*ClassicalSixthBranch.v ((657549527:ℝ)/168755200)/ClassicalSixthBranch.r = (89363798930465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3236
  · change upperPayment 3237 ≤ upperValue ((point split endpoint 4096 3237+point split endpoint 4096 3238)/2)
    have hp : upperPayment 3237 = (130178867344:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3237+point split endpoint 4096 3238)/2 = (657574677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657574677:ℝ)/168755200)*ClassicalSixthBranch.v ((657574677:ℝ)/168755200)/ClassicalSixthBranch.r = (89344333534665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3237
  · change upperPayment 3238 ≤ upperValue ((point split endpoint 4096 3238+point split endpoint 4096 3239)/2)
    have hp : upperPayment 3238 = (130043178698:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3238+point split endpoint 4096 3239)/2 = (657599827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657599827:ℝ)/168755200)*ClassicalSixthBranch.v ((657599827:ℝ)/168755200)/ClassicalSixthBranch.r = (89324870162937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3238
  · change upperPayment 3239 ≤ upperValue ((point split endpoint 4096 3239+point split endpoint 4096 3240)/2)
    have hp : upperPayment 3239 = (129907455526:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3239+point split endpoint 4096 3240)/2 = (657624977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657624977:ℝ)/168755200)*ClassicalSixthBranch.v ((657624977:ℝ)/168755200)/ClassicalSixthBranch.r = (89305408815281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3239
  · change upperPayment 3240 ≤ upperValue ((point split endpoint 4096 3240+point split endpoint 4096 3241)/2)
    have hp : upperPayment 3240 = (129771697820:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3240+point split endpoint 4096 3241)/2 = (657650127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657650127:ℝ)/168755200)*ClassicalSixthBranch.v ((657650127:ℝ)/168755200)/ClassicalSixthBranch.r = (89285949491697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3240
  · change upperPayment 3241 ≤ upperValue ((point split endpoint 4096 3241+point split endpoint 4096 3242)/2)
    have hp : upperPayment 3241 = (129635905572:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3241+point split endpoint 4096 3242)/2 = (657675277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657675277:ℝ)/168755200)*ClassicalSixthBranch.v ((657675277:ℝ)/168755200)/ClassicalSixthBranch.r = (89266492192185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3241
  · change upperPayment 3242 ≤ upperValue ((point split endpoint 4096 3242+point split endpoint 4096 3243)/2)
    have hp : upperPayment 3242 = (129500078772:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3242+point split endpoint 4096 3243)/2 = (657700427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657700427:ℝ)/168755200)*ClassicalSixthBranch.v ((657700427:ℝ)/168755200)/ClassicalSixthBranch.r = (89247036916745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3242
  · change upperPayment 3243 ≤ upperValue ((point split endpoint 4096 3243+point split endpoint 4096 3244)/2)
    have hp : upperPayment 3243 = (129364217413:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3243+point split endpoint 4096 3244)/2 = (657725577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657725577:ℝ)/168755200)*ClassicalSixthBranch.v ((657725577:ℝ)/168755200)/ClassicalSixthBranch.r = (89227583665377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3243
  · change upperPayment 3244 ≤ upperValue ((point split endpoint 4096 3244+point split endpoint 4096 3245)/2)
    have hp : upperPayment 3244 = (129228321485:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3244+point split endpoint 4096 3245)/2 = (657750727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657750727:ℝ)/168755200)*ClassicalSixthBranch.v ((657750727:ℝ)/168755200)/ClassicalSixthBranch.r = (89208132438081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3244
  · change upperPayment 3245 ≤ upperValue ((point split endpoint 4096 3245+point split endpoint 4096 3246)/2)
    have hp : upperPayment 3245 = (129092390981:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3245+point split endpoint 4096 3246)/2 = (657775877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657775877:ℝ)/168755200)*ClassicalSixthBranch.v ((657775877:ℝ)/168755200)/ClassicalSixthBranch.r = (89188683234857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3245
  · change upperPayment 3246 ≤ upperValue ((point split endpoint 4096 3246+point split endpoint 4096 3247)/2)
    have hp : upperPayment 3246 = (128956425891:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3246+point split endpoint 4096 3247)/2 = (657801027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657801027:ℝ)/168755200)*ClassicalSixthBranch.v ((657801027:ℝ)/168755200)/ClassicalSixthBranch.r = (89169236055705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3246
  · change upperPayment 3247 ≤ upperValue ((point split endpoint 4096 3247+point split endpoint 4096 3248)/2)
    have hp : upperPayment 3247 = (128820426208:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3247+point split endpoint 4096 3248)/2 = (657826177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657826177:ℝ)/168755200)*ClassicalSixthBranch.v ((657826177:ℝ)/168755200)/ClassicalSixthBranch.r = (89149790900625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3247
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_202
