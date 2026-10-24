import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints151
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_151 (j : Fin 16) : upperPayment (16*151+j.val) ≤
    upperValue ((point split endpoint 4096 (16*151+j.val)+point split endpoint 4096 (16*151+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2416 ≤ upperValue ((point split endpoint 4096 2416+point split endpoint 4096 2417)/2)
    have hp : upperPayment 2416 = (230656892984:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2416+point split endpoint 4096 2417)/2 = (636926527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636926527:ℝ)/168755200)*ClassicalSixthBranch.v ((636926527:ℝ)/168755200)/ClassicalSixthBranch.r = (106006746362385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2416
  · change upperPayment 2417 ≤ upperValue ((point split endpoint 4096 2417+point split endpoint 4096 2418)/2)
    have hp : upperPayment 2417 = (230546967301:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2417+point split endpoint 4096 2418)/2 = (636951677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636951677:ℝ)/168755200)*ClassicalSixthBranch.v ((636951677:ℝ)/168755200)/ClassicalSixthBranch.r = (105985621227545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2417
  · change upperPayment 2418 ≤ upperValue ((point split endpoint 4096 2418+point split endpoint 4096 2419)/2)
    have hp : upperPayment 2418 = (230437013046:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2418+point split endpoint 4096 2419)/2 = (636976827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((636976827:ℝ)/168755200)*ClassicalSixthBranch.v ((636976827:ℝ)/168755200)/ClassicalSixthBranch.r = (105964498116777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2418
  · change upperPayment 2419 ≤ upperValue ((point split endpoint 4096 2419+point split endpoint 4096 2420)/2)
    have hp : upperPayment 2419 = (230327030215:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2419+point split endpoint 4096 2420)/2 = (637001977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637001977:ℝ)/168755200)*ClassicalSixthBranch.v ((637001977:ℝ)/168755200)/ClassicalSixthBranch.r = (105943377030081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2419
  · change upperPayment 2420 ≤ upperValue ((point split endpoint 4096 2420+point split endpoint 4096 2421)/2)
    have hp : upperPayment 2420 = (230217018802:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2420+point split endpoint 4096 2421)/2 = (637027127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637027127:ℝ)/168755200)*ClassicalSixthBranch.v ((637027127:ℝ)/168755200)/ClassicalSixthBranch.r = (105922257967457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2420
  · change upperPayment 2421 ≤ upperValue ((point split endpoint 4096 2421+point split endpoint 4096 2422)/2)
    have hp : upperPayment 2421 = (230106978800:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2421+point split endpoint 4096 2422)/2 = (637052277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637052277:ℝ)/168755200)*ClassicalSixthBranch.v ((637052277:ℝ)/168755200)/ClassicalSixthBranch.r = (105901140928905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2421
  · change upperPayment 2422 ≤ upperValue ((point split endpoint 4096 2422+point split endpoint 4096 2423)/2)
    have hp : upperPayment 2422 = (229996910202:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2422+point split endpoint 4096 2423)/2 = (637077427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637077427:ℝ)/168755200)*ClassicalSixthBranch.v ((637077427:ℝ)/168755200)/ClassicalSixthBranch.r = (105880025914425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2422
  · change upperPayment 2423 ≤ upperValue ((point split endpoint 4096 2423+point split endpoint 4096 2424)/2)
    have hp : upperPayment 2423 = (229886813004:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2423+point split endpoint 4096 2424)/2 = (637102577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637102577:ℝ)/168755200)*ClassicalSixthBranch.v ((637102577:ℝ)/168755200)/ClassicalSixthBranch.r = (105858912924017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2423
  · change upperPayment 2424 ≤ upperValue ((point split endpoint 4096 2424+point split endpoint 4096 2425)/2)
    have hp : upperPayment 2424 = (229776687199:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2424+point split endpoint 4096 2425)/2 = (637127727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637127727:ℝ)/168755200)*ClassicalSixthBranch.v ((637127727:ℝ)/168755200)/ClassicalSixthBranch.r = (105837801957681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2424
  · change upperPayment 2425 ≤ upperValue ((point split endpoint 4096 2425+point split endpoint 4096 2426)/2)
    have hp : upperPayment 2425 = (229666532780:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2425+point split endpoint 4096 2426)/2 = (637152877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637152877:ℝ)/168755200)*ClassicalSixthBranch.v ((637152877:ℝ)/168755200)/ClassicalSixthBranch.r = (105816693015417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2425
  · change upperPayment 2426 ≤ upperValue ((point split endpoint 4096 2426+point split endpoint 4096 2427)/2)
    have hp : upperPayment 2426 = (229556349741:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2426+point split endpoint 4096 2427)/2 = (637178027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637178027:ℝ)/168755200)*ClassicalSixthBranch.v ((637178027:ℝ)/168755200)/ClassicalSixthBranch.r = (105795586097225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2426
  · change upperPayment 2427 ≤ upperValue ((point split endpoint 4096 2427+point split endpoint 4096 2428)/2)
    have hp : upperPayment 2427 = (229446138078:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2427+point split endpoint 4096 2428)/2 = (637203177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637203177:ℝ)/168755200)*ClassicalSixthBranch.v ((637203177:ℝ)/168755200)/ClassicalSixthBranch.r = (105774481203105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2427
  · change upperPayment 2428 ≤ upperValue ((point split endpoint 4096 2428+point split endpoint 4096 2429)/2)
    have hp : upperPayment 2428 = (229335897782:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2428+point split endpoint 4096 2429)/2 = (637228327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637228327:ℝ)/168755200)*ClassicalSixthBranch.v ((637228327:ℝ)/168755200)/ClassicalSixthBranch.r = (105753378333057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2428
  · change upperPayment 2429 ≤ upperValue ((point split endpoint 4096 2429+point split endpoint 4096 2430)/2)
    have hp : upperPayment 2429 = (229225628848:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2429+point split endpoint 4096 2430)/2 = (637253477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637253477:ℝ)/168755200)*ClassicalSixthBranch.v ((637253477:ℝ)/168755200)/ClassicalSixthBranch.r = (105732277487081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2429
  · change upperPayment 2430 ≤ upperValue ((point split endpoint 4096 2430+point split endpoint 4096 2431)/2)
    have hp : upperPayment 2430 = (229115331271:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2430+point split endpoint 4096 2431)/2 = (637278627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637278627:ℝ)/168755200)*ClassicalSixthBranch.v ((637278627:ℝ)/168755200)/ClassicalSixthBranch.r = (105711178665177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2430
  · change upperPayment 2431 ≤ upperValue ((point split endpoint 4096 2431+point split endpoint 4096 2432)/2)
    have hp : upperPayment 2431 = (229005005043:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2431+point split endpoint 4096 2432)/2 = (637303777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637303777:ℝ)/168755200)*ClassicalSixthBranch.v ((637303777:ℝ)/168755200)/ClassicalSixthBranch.r = (105690081867345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2431
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_151
