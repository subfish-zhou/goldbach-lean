import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints088
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_088 (j : Fin 16) : upperPayment (16*88+j.val) ≤
    upperValue ((point split endpoint 4096 (16*88+j.val)+point split endpoint 4096 (16*88+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1408 ≤ upperValue ((point split endpoint 4096 1408+point split endpoint 4096 1409)/2)
    have hp : upperPayment 1408 = (327882434737:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1408+point split endpoint 4096 1409)/2 = (611575327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611575327:ℝ)/168755200)*ClassicalSixthBranch.v ((611575327:ℝ)/168755200)/ClassicalSixthBranch.r = (128330195759697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1408
  · change upperPayment 1409 ≤ upperValue ((point split endpoint 4096 1409+point split endpoint 4096 1410)/2)
    have hp : upperPayment 1409 = (327798577612:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1409+point split endpoint 4096 1410)/2 = (611600477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611600477:ℝ)/168755200)*ClassicalSixthBranch.v ((611600477:ℝ)/168755200)/ClassicalSixthBranch.r = (128307030360281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1409
  · change upperPayment 1410 ≤ upperValue ((point split endpoint 4096 1410+point split endpoint 4096 1411)/2)
    have hp : upperPayment 1410 = (327714696985:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1410+point split endpoint 4096 1411)/2 = (611625627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611625627:ℝ)/168755200)*ClassicalSixthBranch.v ((611625627:ℝ)/168755200)/ClassicalSixthBranch.r = (128283866984937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1410
  · change upperPayment 1411 ≤ upperValue ((point split endpoint 4096 1411+point split endpoint 4096 1412)/2)
    have hp : upperPayment 1411 = (327630792851:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1411+point split endpoint 4096 1412)/2 = (611650777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611650777:ℝ)/168755200)*ClassicalSixthBranch.v ((611650777:ℝ)/168755200)/ClassicalSixthBranch.r = (128260705633665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1411
  · change upperPayment 1412 ≤ upperValue ((point split endpoint 4096 1412+point split endpoint 4096 1413)/2)
    have hp : upperPayment 1412 = (327546865207:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1412+point split endpoint 4096 1413)/2 = (611675927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611675927:ℝ)/168755200)*ClassicalSixthBranch.v ((611675927:ℝ)/168755200)/ClassicalSixthBranch.r = (128237546306465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1412
  · change upperPayment 1413 ≤ upperValue ((point split endpoint 4096 1413+point split endpoint 4096 1414)/2)
    have hp : upperPayment 1413 = (327462914048:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1413+point split endpoint 4096 1414)/2 = (611701077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611701077:ℝ)/168755200)*ClassicalSixthBranch.v ((611701077:ℝ)/168755200)/ClassicalSixthBranch.r = (128214389003337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1413
  · change upperPayment 1414 ≤ upperValue ((point split endpoint 4096 1414+point split endpoint 4096 1415)/2)
    have hp : upperPayment 1414 = (327378939370:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1414+point split endpoint 4096 1415)/2 = (611726227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611726227:ℝ)/168755200)*ClassicalSixthBranch.v ((611726227:ℝ)/168755200)/ClassicalSixthBranch.r = (128191233724281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1414
  · change upperPayment 1415 ≤ upperValue ((point split endpoint 4096 1415+point split endpoint 4096 1416)/2)
    have hp : upperPayment 1415 = (327294941170:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1415+point split endpoint 4096 1416)/2 = (611751377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611751377:ℝ)/168755200)*ClassicalSixthBranch.v ((611751377:ℝ)/168755200)/ClassicalSixthBranch.r = (128168080469297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1415
  · change upperPayment 1416 ≤ upperValue ((point split endpoint 4096 1416+point split endpoint 4096 1417)/2)
    have hp : upperPayment 1416 = (327210919443:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1416+point split endpoint 4096 1417)/2 = (611776527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611776527:ℝ)/168755200)*ClassicalSixthBranch.v ((611776527:ℝ)/168755200)/ClassicalSixthBranch.r = (128144929238385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1416
  · change upperPayment 1417 ≤ upperValue ((point split endpoint 4096 1417+point split endpoint 4096 1418)/2)
    have hp : upperPayment 1417 = (327126874185:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1417+point split endpoint 4096 1418)/2 = (611801677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611801677:ℝ)/168755200)*ClassicalSixthBranch.v ((611801677:ℝ)/168755200)/ClassicalSixthBranch.r = (128121780031545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1417
  · change upperPayment 1418 ≤ upperValue ((point split endpoint 4096 1418+point split endpoint 4096 1419)/2)
    have hp : upperPayment 1418 = (327042805393:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1418+point split endpoint 4096 1419)/2 = (611826827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611826827:ℝ)/168755200)*ClassicalSixthBranch.v ((611826827:ℝ)/168755200)/ClassicalSixthBranch.r = (128098632848777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1418
  · change upperPayment 1419 ≤ upperValue ((point split endpoint 4096 1419+point split endpoint 4096 1420)/2)
    have hp : upperPayment 1419 = (326958713061:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1419+point split endpoint 4096 1420)/2 = (611851977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611851977:ℝ)/168755200)*ClassicalSixthBranch.v ((611851977:ℝ)/168755200)/ClassicalSixthBranch.r = (128075487690081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1419
  · change upperPayment 1420 ≤ upperValue ((point split endpoint 4096 1420+point split endpoint 4096 1421)/2)
    have hp : upperPayment 1420 = (326874597187:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1420+point split endpoint 4096 1421)/2 = (611877127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611877127:ℝ)/168755200)*ClassicalSixthBranch.v ((611877127:ℝ)/168755200)/ClassicalSixthBranch.r = (128052344555457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1420
  · change upperPayment 1421 ≤ upperValue ((point split endpoint 4096 1421+point split endpoint 4096 1422)/2)
    have hp : upperPayment 1421 = (326790457765:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1421+point split endpoint 4096 1422)/2 = (611902277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611902277:ℝ)/168755200)*ClassicalSixthBranch.v ((611902277:ℝ)/168755200)/ClassicalSixthBranch.r = (128029203444905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1421
  · change upperPayment 1422 ≤ upperValue ((point split endpoint 4096 1422+point split endpoint 4096 1423)/2)
    have hp : upperPayment 1422 = (326706294792:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1422+point split endpoint 4096 1423)/2 = (611927427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611927427:ℝ)/168755200)*ClassicalSixthBranch.v ((611927427:ℝ)/168755200)/ClassicalSixthBranch.r = (128006064358425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1422
  · change upperPayment 1423 ≤ upperValue ((point split endpoint 4096 1423+point split endpoint 4096 1424)/2)
    have hp : upperPayment 1423 = (326622108264:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1423+point split endpoint 4096 1424)/2 = (611952577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611952577:ℝ)/168755200)*ClassicalSixthBranch.v ((611952577:ℝ)/168755200)/ClassicalSixthBranch.r = (127982927296017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1423
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_088
