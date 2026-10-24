import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints027
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_027 (j : Fin 16) : upperPayment (16*27+j.val) ≤
    upperValue ((point split endpoint 4096 (16*27+j.val)+point split endpoint 4096 (16*27+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 432 ≤ upperValue ((point split endpoint 4096 432+point split endpoint 4096 433)/2)
    have hp : upperPayment 432 = (399092431142:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 432+point split endpoint 4096 433)/2 = (587028927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587028927:ℝ)/168755200)*ClassicalSixthBranch.v ((587028927:ℝ)/168755200)/ClassicalSixthBranch.r = (151904654541585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_432
  · change upperPayment 433 ≤ upperValue ((point split endpoint 4096 433+point split endpoint 4096 434)/2)
    have hp : upperPayment 433 = (399029819740:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 433+point split endpoint 4096 434)/2 = (587054077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587054077:ℝ)/168755200)*ClassicalSixthBranch.v ((587054077:ℝ)/168755200)/ClassicalSixthBranch.r = (151879513647897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_433
  · change upperPayment 434 ≤ upperValue ((point split endpoint 4096 434+point split endpoint 4096 435)/2)
    have hp : upperPayment 434 = (398967188069:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 434+point split endpoint 4096 435)/2 = (587079227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587079227:ℝ)/168755200)*ClassicalSixthBranch.v ((587079227:ℝ)/168755200)/ClassicalSixthBranch.r = (151854374778281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_434
  · change upperPayment 435 ≤ upperValue ((point split endpoint 4096 435+point split endpoint 4096 436)/2)
    have hp : upperPayment 435 = (398904536125:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 435+point split endpoint 4096 436)/2 = (587104377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587104377:ℝ)/168755200)*ClassicalSixthBranch.v ((587104377:ℝ)/168755200)/ClassicalSixthBranch.r = (151829237932737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_435
  · change upperPayment 436 ≤ upperValue ((point split endpoint 4096 436+point split endpoint 4096 437)/2)
    have hp : upperPayment 436 = (398841863907:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 436+point split endpoint 4096 437)/2 = (587129527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587129527:ℝ)/168755200)*ClassicalSixthBranch.v ((587129527:ℝ)/168755200)/ClassicalSixthBranch.r = (151804103111265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_436
  · change upperPayment 437 ≤ upperValue ((point split endpoint 4096 437+point split endpoint 4096 438)/2)
    have hp : upperPayment 437 = (398779171410:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 437+point split endpoint 4096 438)/2 = (587154677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587154677:ℝ)/168755200)*ClassicalSixthBranch.v ((587154677:ℝ)/168755200)/ClassicalSixthBranch.r = (151778970313865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_437
  · change upperPayment 438 ≤ upperValue ((point split endpoint 4096 438+point split endpoint 4096 439)/2)
    have hp : upperPayment 438 = (398716458633:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 438+point split endpoint 4096 439)/2 = (587179827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587179827:ℝ)/168755200)*ClassicalSixthBranch.v ((587179827:ℝ)/168755200)/ClassicalSixthBranch.r = (151753839540537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_438
  · change upperPayment 439 ≤ upperValue ((point split endpoint 4096 439+point split endpoint 4096 440)/2)
    have hp : upperPayment 439 = (398653725574:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 439+point split endpoint 4096 440)/2 = (587204977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587204977:ℝ)/168755200)*ClassicalSixthBranch.v ((587204977:ℝ)/168755200)/ClassicalSixthBranch.r = (1473094279527:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_439
  · change upperPayment 440 ≤ upperValue ((point split endpoint 4096 440+point split endpoint 4096 441)/2)
    have hp : upperPayment 440 = (398590972228:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 440+point split endpoint 4096 441)/2 = (587230127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587230127:ℝ)/168755200)*ClassicalSixthBranch.v ((587230127:ℝ)/168755200)/ClassicalSixthBranch.r = (151703584066097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_440
  · change upperPayment 441 ≤ upperValue ((point split endpoint 4096 441+point split endpoint 4096 442)/2)
    have hp : upperPayment 441 = (398528198595:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 441+point split endpoint 4096 442)/2 = (587255277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587255277:ℝ)/168755200)*ClassicalSixthBranch.v ((587255277:ℝ)/168755200)/ClassicalSixthBranch.r = (151678459364985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_441
  · change upperPayment 442 ≤ upperValue ((point split endpoint 4096 442+point split endpoint 4096 443)/2)
    have hp : upperPayment 442 = (398465404670:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 442+point split endpoint 4096 443)/2 = (587280427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587280427:ℝ)/168755200)*ClassicalSixthBranch.v ((587280427:ℝ)/168755200)/ClassicalSixthBranch.r = (151653336687945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_442
  · change upperPayment 443 ≤ upperValue ((point split endpoint 4096 443+point split endpoint 4096 444)/2)
    have hp : upperPayment 443 = (398402590453:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 443+point split endpoint 4096 444)/2 = (587305577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587305577:ℝ)/168755200)*ClassicalSixthBranch.v ((587305577:ℝ)/168755200)/ClassicalSixthBranch.r = (151628216034977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_443
  · change upperPayment 444 ≤ upperValue ((point split endpoint 4096 444+point split endpoint 4096 445)/2)
    have hp : upperPayment 444 = (398339755939:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 444+point split endpoint 4096 445)/2 = (587330727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587330727:ℝ)/168755200)*ClassicalSixthBranch.v ((587330727:ℝ)/168755200)/ClassicalSixthBranch.r = (151603097406081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_444
  · change upperPayment 445 ≤ upperValue ((point split endpoint 4096 445+point split endpoint 4096 446)/2)
    have hp : upperPayment 445 = (398276901126:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 445+point split endpoint 4096 446)/2 = (587355877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587355877:ℝ)/168755200)*ClassicalSixthBranch.v ((587355877:ℝ)/168755200)/ClassicalSixthBranch.r = (151577980801257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_445
  · change upperPayment 446 ≤ upperValue ((point split endpoint 4096 446+point split endpoint 4096 447)/2)
    have hp : upperPayment 446 = (398214026011:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 446+point split endpoint 4096 447)/2 = (587381027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587381027:ℝ)/168755200)*ClassicalSixthBranch.v ((587381027:ℝ)/168755200)/ClassicalSixthBranch.r = (151552866220505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_446
  · change upperPayment 447 ≤ upperValue ((point split endpoint 4096 447+point split endpoint 4096 448)/2)
    have hp : upperPayment 447 = (398151130593:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 447+point split endpoint 4096 448)/2 = (587406177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((587406177:ℝ)/168755200)*ClassicalSixthBranch.v ((587406177:ℝ)/168755200)/ClassicalSixthBranch.r = (151527753663825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_447
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_027
