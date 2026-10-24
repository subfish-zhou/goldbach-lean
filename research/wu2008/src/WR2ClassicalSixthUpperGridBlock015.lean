import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints015
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_015 (j : Fin 16) : upperPayment (16*15+j.val) ≤
    upperValue ((point split endpoint 4096 (16*15+j.val)+point split endpoint 4096 (16*15+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 240 ≤ upperValue ((point split endpoint 4096 240+point split endpoint 4096 241)/2)
    have hp : upperPayment 240 = (410741338861:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 240+point split endpoint 4096 241)/2 = (582200127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582200127:ℝ)/168755200)*ClassicalSixthBranch.v ((582200127:ℝ)/168755200)/ClassicalSixthBranch.r = (156769208135697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_240
  · change upperPayment 241 ≤ upperValue ((point split endpoint 4096 241+point split endpoint 4096 242)/2)
    have hp : upperPayment 241 = (410682572042:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 241+point split endpoint 4096 242)/2 = (582225277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582225277:ℝ)/168755200)*ClassicalSixthBranch.v ((582225277:ℝ)/168755200)/ClassicalSixthBranch.r = (156743678620185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_241
  · change upperPayment 242 ≤ upperValue ((point split endpoint 4096 242+point split endpoint 4096 243)/2)
    have hp : upperPayment 242 = (410623785435:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 242+point split endpoint 4096 243)/2 = (582250427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582250427:ℝ)/168755200)*ClassicalSixthBranch.v ((582250427:ℝ)/168755200)/ClassicalSixthBranch.r = (156718151128745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_242
  · change upperPayment 243 ≤ upperValue ((point split endpoint 4096 243+point split endpoint 4096 244)/2)
    have hp : upperPayment 243 = (410564979037:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 243+point split endpoint 4096 244)/2 = (582275577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582275577:ℝ)/168755200)*ClassicalSixthBranch.v ((582275577:ℝ)/168755200)/ClassicalSixthBranch.r = (156692625661377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_243
  · change upperPayment 244 ≤ upperValue ((point split endpoint 4096 244+point split endpoint 4096 245)/2)
    have hp : upperPayment 244 = (410506152846:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 244+point split endpoint 4096 245)/2 = (582300727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582300727:ℝ)/168755200)*ClassicalSixthBranch.v ((582300727:ℝ)/168755200)/ClassicalSixthBranch.r = (156667102218081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_244
  · change upperPayment 245 ≤ upperValue ((point split endpoint 4096 245+point split endpoint 4096 246)/2)
    have hp : upperPayment 245 = (410447306860:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 245+point split endpoint 4096 246)/2 = (582325877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582325877:ℝ)/168755200)*ClassicalSixthBranch.v ((582325877:ℝ)/168755200)/ClassicalSixthBranch.r = (156641580798857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_245
  · change upperPayment 246 ≤ upperValue ((point split endpoint 4096 246+point split endpoint 4096 247)/2)
    have hp : upperPayment 246 = (410388441076:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 246+point split endpoint 4096 247)/2 = (582351027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582351027:ℝ)/168755200)*ClassicalSixthBranch.v ((582351027:ℝ)/168755200)/ClassicalSixthBranch.r = (156616061403705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_246
  · change upperPayment 247 ≤ upperValue ((point split endpoint 4096 247+point split endpoint 4096 248)/2)
    have hp : upperPayment 247 = (410329555493:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 247+point split endpoint 4096 248)/2 = (582376177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582376177:ℝ)/168755200)*ClassicalSixthBranch.v ((582376177:ℝ)/168755200)/ClassicalSixthBranch.r = (156590544032625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_247
  · change upperPayment 248 ≤ upperValue ((point split endpoint 4096 248+point split endpoint 4096 249)/2)
    have hp : upperPayment 248 = (410270650106:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 248+point split endpoint 4096 249)/2 = (582401327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582401327:ℝ)/168755200)*ClassicalSixthBranch.v ((582401327:ℝ)/168755200)/ClassicalSixthBranch.r = (156565028685617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_248
  · change upperPayment 249 ≤ upperValue ((point split endpoint 4096 249+point split endpoint 4096 250)/2)
    have hp : upperPayment 249 = (410211724915:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 249+point split endpoint 4096 250)/2 = (582426477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582426477:ℝ)/168755200)*ClassicalSixthBranch.v ((582426477:ℝ)/168755200)/ClassicalSixthBranch.r = (156539515362681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_249
  · change upperPayment 250 ≤ upperValue ((point split endpoint 4096 250+point split endpoint 4096 251)/2)
    have hp : upperPayment 250 = (410152779917:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 250+point split endpoint 4096 251)/2 = (582451627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582451627:ℝ)/168755200)*ClassicalSixthBranch.v ((582451627:ℝ)/168755200)/ClassicalSixthBranch.r = (156514004063817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_250
  · change upperPayment 251 ≤ upperValue ((point split endpoint 4096 251+point split endpoint 4096 252)/2)
    have hp : upperPayment 251 = (410093815108:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 251+point split endpoint 4096 252)/2 = (582476777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582476777:ℝ)/168755200)*ClassicalSixthBranch.v ((582476777:ℝ)/168755200)/ClassicalSixthBranch.r = (156488494789025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_251
  · change upperPayment 252 ≤ upperValue ((point split endpoint 4096 252+point split endpoint 4096 253)/2)
    have hp : upperPayment 252 = (410034830488:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 252+point split endpoint 4096 253)/2 = (582501927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582501927:ℝ)/168755200)*ClassicalSixthBranch.v ((582501927:ℝ)/168755200)/ClassicalSixthBranch.r = (156462987538305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_252
  · change upperPayment 253 ≤ upperValue ((point split endpoint 4096 253+point split endpoint 4096 254)/2)
    have hp : upperPayment 253 = (409975826054:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 253+point split endpoint 4096 254)/2 = (582527077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582527077:ℝ)/168755200)*ClassicalSixthBranch.v ((582527077:ℝ)/168755200)/ClassicalSixthBranch.r = (156437482311657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_253
  · change upperPayment 254 ≤ upperValue ((point split endpoint 4096 254+point split endpoint 4096 255)/2)
    have hp : upperPayment 254 = (409916801802:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 254+point split endpoint 4096 255)/2 = (582552227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582552227:ℝ)/168755200)*ClassicalSixthBranch.v ((582552227:ℝ)/168755200)/ClassicalSixthBranch.r = (156411979109081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_254
  · change upperPayment 255 ≤ upperValue ((point split endpoint 4096 255+point split endpoint 4096 256)/2)
    have hp : upperPayment 255 = (409857757731:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 255+point split endpoint 4096 256)/2 = (582577377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((582577377:ℝ)/168755200)*ClassicalSixthBranch.v ((582577377:ℝ)/168755200)/ClassicalSixthBranch.r = (156386477930577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_255
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_015
