import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints026
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_026 (j : Fin 16) : upperPayment (16*26+j.val) ≤
    upperValue ((point split endpoint 4096 (16*26+j.val)+point split endpoint 4096 (16*26+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 416 ≤ upperValue ((point split endpoint 4096 416+point split endpoint 4096 417)/2)
    have hp : upperPayment 416 = (400091459015:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 416+point split endpoint 4096 417)/2 = (586626527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586626527:ℝ)/168755200)*ClassicalSixthBranch.v ((586626527:ℝ)/168755200)/ClassicalSixthBranch.r = (152307184114385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_416
  · change upperPayment 417 ≤ upperValue ((point split endpoint 4096 417+point split endpoint 4096 418)/2)
    have hp : upperPayment 417 = (400029171574:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 417+point split endpoint 4096 418)/2 = (586651677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586651677:ℝ)/168755200)*ClassicalSixthBranch.v ((586651677:ℝ)/168755200)/ClassicalSixthBranch.r = (152282010835545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_417
  · change upperPayment 418 ≤ upperValue ((point split endpoint 4096 418+point split endpoint 4096 419)/2)
    have hp : upperPayment 418 = (399966863904:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 418+point split endpoint 4096 419)/2 = (586676827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586676827:ℝ)/168755200)*ClassicalSixthBranch.v ((586676827:ℝ)/168755200)/ClassicalSixthBranch.r = (152256839580777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_418
  · change upperPayment 419 ≤ upperValue ((point split endpoint 4096 419+point split endpoint 4096 420)/2)
    have hp : upperPayment 419 = (399904536004:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 419+point split endpoint 4096 420)/2 = (586701977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586701977:ℝ)/168755200)*ClassicalSixthBranch.v ((586701977:ℝ)/168755200)/ClassicalSixthBranch.r = (152231670350081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_419
  · change upperPayment 420 ≤ upperValue ((point split endpoint 4096 420+point split endpoint 4096 421)/2)
    have hp : upperPayment 420 = (399842187871:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 420+point split endpoint 4096 421)/2 = (586727127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586727127:ℝ)/168755200)*ClassicalSixthBranch.v ((586727127:ℝ)/168755200)/ClassicalSixthBranch.r = (152206503143457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_420
  · change upperPayment 421 ≤ upperValue ((point split endpoint 4096 421+point split endpoint 4096 422)/2)
    have hp : upperPayment 421 = (399779819503:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 421+point split endpoint 4096 422)/2 = (586752277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586752277:ℝ)/168755200)*ClassicalSixthBranch.v ((586752277:ℝ)/168755200)/ClassicalSixthBranch.r = (152181337960905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_421
  · change upperPayment 422 ≤ upperValue ((point split endpoint 4096 422+point split endpoint 4096 423)/2)
    have hp : upperPayment 422 = (399717430896:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 422+point split endpoint 4096 423)/2 = (586777427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586777427:ℝ)/168755200)*ClassicalSixthBranch.v ((586777427:ℝ)/168755200)/ClassicalSixthBranch.r = (152156174802425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_422
  · change upperPayment 423 ≤ upperValue ((point split endpoint 4096 423+point split endpoint 4096 424)/2)
    have hp : upperPayment 423 = (399655022048:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 423+point split endpoint 4096 424)/2 = (586802577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586802577:ℝ)/168755200)*ClassicalSixthBranch.v ((586802577:ℝ)/168755200)/ClassicalSixthBranch.r = (152131013668017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_423
  · change upperPayment 424 ≤ upperValue ((point split endpoint 4096 424+point split endpoint 4096 425)/2)
    have hp : upperPayment 424 = (399592592956:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 424+point split endpoint 4096 425)/2 = (586827727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586827727:ℝ)/168755200)*ClassicalSixthBranch.v ((586827727:ℝ)/168755200)/ClassicalSixthBranch.r = (152105854557681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_424
  · change upperPayment 425 ≤ upperValue ((point split endpoint 4096 425+point split endpoint 4096 426)/2)
    have hp : upperPayment 425 = (399530143619:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 425+point split endpoint 4096 426)/2 = (586852877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586852877:ℝ)/168755200)*ClassicalSixthBranch.v ((586852877:ℝ)/168755200)/ClassicalSixthBranch.r = (152080697471417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_425
  · change upperPayment 426 ≤ upperValue ((point split endpoint 4096 426+point split endpoint 4096 427)/2)
    have hp : upperPayment 426 = (399467674032:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 426+point split endpoint 4096 427)/2 = (586878027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586878027:ℝ)/168755200)*ClassicalSixthBranch.v ((586878027:ℝ)/168755200)/ClassicalSixthBranch.r = (152055542409225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_426
  · change upperPayment 427 ≤ upperValue ((point split endpoint 4096 427+point split endpoint 4096 428)/2)
    have hp : upperPayment 427 = (399405184194:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 427+point split endpoint 4096 428)/2 = (586903177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586903177:ℝ)/168755200)*ClassicalSixthBranch.v ((586903177:ℝ)/168755200)/ClassicalSixthBranch.r = (152030389371105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_427
  · change upperPayment 428 ≤ upperValue ((point split endpoint 4096 428+point split endpoint 4096 429)/2)
    have hp : upperPayment 428 = (399342674102:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 428+point split endpoint 4096 429)/2 = (586928327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586928327:ℝ)/168755200)*ClassicalSixthBranch.v ((586928327:ℝ)/168755200)/ClassicalSixthBranch.r = (152005238357057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_428
  · change upperPayment 429 ≤ upperValue ((point split endpoint 4096 429+point split endpoint 4096 430)/2)
    have hp : upperPayment 429 = (399280143754:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 429+point split endpoint 4096 430)/2 = (586953477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586953477:ℝ)/168755200)*ClassicalSixthBranch.v ((586953477:ℝ)/168755200)/ClassicalSixthBranch.r = (151980089367081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_429
  · change upperPayment 430 ≤ upperValue ((point split endpoint 4096 430+point split endpoint 4096 431)/2)
    have hp : upperPayment 430 = (399217593146:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 430+point split endpoint 4096 431)/2 = (586978627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586978627:ℝ)/168755200)*ClassicalSixthBranch.v ((586978627:ℝ)/168755200)/ClassicalSixthBranch.r = (151954942401177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_430
  · change upperPayment 431 ≤ upperValue ((point split endpoint 4096 431+point split endpoint 4096 432)/2)
    have hp : upperPayment 431 = (399155022276:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 431+point split endpoint 4096 432)/2 = (587003777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587003777:ℝ)/168755200)*ClassicalSixthBranch.v ((587003777:ℝ)/168755200)/ClassicalSixthBranch.r = (151929797459345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_431
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_026
