import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints154
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_154 (j : Fin 16) : upperPayment (16*154+j.val) ≤
    upperValue ((point split endpoint 4096 (16*154+j.val)+point split endpoint 4096 (16*154+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2464 ≤ upperValue ((point split endpoint 4096 2464+point split endpoint 4096 2465)/2)
    have hp : upperPayment 2464 = (225348126365:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2464+point split endpoint 4096 2465)/2 = (638133727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638133727:ℝ)/168755200)*ClassicalSixthBranch.v ((638133727:ℝ)/168755200)/ClassicalSixthBranch.r = (104995023043281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2464
  · change upperPayment 2465 ≤ upperValue ((point split endpoint 4096 2465+point split endpoint 4096 2466)/2)
    have hp : upperPayment 2465 = (225236822354:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2465+point split endpoint 4096 2466)/2 = (638158877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638158877:ℝ)/168755200)*ClassicalSixthBranch.v ((638158877:ℝ)/168755200)/ClassicalSixthBranch.r = (104973995063897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2465
  · change upperPayment 2466 ≤ upperValue ((point split endpoint 4096 2466+point split endpoint 4096 2467)/2)
    have hp : upperPayment 2466 = (225125489475:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2466+point split endpoint 4096 2467)/2 = (638184027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638184027:ℝ)/168755200)*ClassicalSixthBranch.v ((638184027:ℝ)/168755200)/ClassicalSixthBranch.r = (104952969108585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2466
  · change upperPayment 2467 ≤ upperValue ((point split endpoint 4096 2467+point split endpoint 4096 2468)/2)
    have hp : upperPayment 2467 = (225014127723:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2467+point split endpoint 4096 2468)/2 = (638209177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638209177:ℝ)/168755200)*ClassicalSixthBranch.v ((638209177:ℝ)/168755200)/ClassicalSixthBranch.r = (104931945177345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2467
  · change upperPayment 2468 ≤ upperValue ((point split endpoint 4096 2468+point split endpoint 4096 2469)/2)
    have hp : upperPayment 2468 = (224902737092:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2468+point split endpoint 4096 2469)/2 = (638234327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638234327:ℝ)/168755200)*ClassicalSixthBranch.v ((638234327:ℝ)/168755200)/ClassicalSixthBranch.r = (104910923270177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2468
  · change upperPayment 2469 ≤ upperValue ((point split endpoint 4096 2469+point split endpoint 4096 2470)/2)
    have hp : upperPayment 2469 = (224791317574:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2469+point split endpoint 4096 2470)/2 = (638259477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638259477:ℝ)/168755200)*ClassicalSixthBranch.v ((638259477:ℝ)/168755200)/ClassicalSixthBranch.r = (104889903387081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2469
  · change upperPayment 2470 ≤ upperValue ((point split endpoint 4096 2470+point split endpoint 4096 2471)/2)
    have hp : upperPayment 2470 = (224679869165:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2470+point split endpoint 4096 2471)/2 = (638284627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638284627:ℝ)/168755200)*ClassicalSixthBranch.v ((638284627:ℝ)/168755200)/ClassicalSixthBranch.r = (104868885528057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2470
  · change upperPayment 2471 ≤ upperValue ((point split endpoint 4096 2471+point split endpoint 4096 2472)/2)
    have hp : upperPayment 2471 = (224568391858:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2471+point split endpoint 4096 2472)/2 = (638309777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638309777:ℝ)/168755200)*ClassicalSixthBranch.v ((638309777:ℝ)/168755200)/ClassicalSixthBranch.r = (104847869693105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2471
  · change upperPayment 2472 ≤ upperValue ((point split endpoint 4096 2472+point split endpoint 4096 2473)/2)
    have hp : upperPayment 2472 = (224456885646:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2472+point split endpoint 4096 2473)/2 = (638334927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638334927:ℝ)/168755200)*ClassicalSixthBranch.v ((638334927:ℝ)/168755200)/ClassicalSixthBranch.r = (104826855882225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2472
  · change upperPayment 2473 ≤ upperValue ((point split endpoint 4096 2473+point split endpoint 4096 2474)/2)
    have hp : upperPayment 2473 = (224345350523:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2473+point split endpoint 4096 2474)/2 = (638360077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638360077:ℝ)/168755200)*ClassicalSixthBranch.v ((638360077:ℝ)/168755200)/ClassicalSixthBranch.r = (104805844095417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2473
  · change upperPayment 2474 ≤ upperValue ((point split endpoint 4096 2474+point split endpoint 4096 2475)/2)
    have hp : upperPayment 2474 = (224233786483:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2474+point split endpoint 4096 2475)/2 = (638385227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638385227:ℝ)/168755200)*ClassicalSixthBranch.v ((638385227:ℝ)/168755200)/ClassicalSixthBranch.r = (104784834332681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2474
  · change upperPayment 2475 ≤ upperValue ((point split endpoint 4096 2475+point split endpoint 4096 2476)/2)
    have hp : upperPayment 2475 = (224122193520:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2475+point split endpoint 4096 2476)/2 = (6198159:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((6198159:ℝ)/1638400)*ClassicalSixthBranch.v ((6198159:ℝ)/1638400)/ClassicalSixthBranch.r = (1017124530039:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2475
  · change upperPayment 2476 ≤ upperValue ((point split endpoint 4096 2476+point split endpoint 4096 2477)/2)
    have hp : upperPayment 2476 = (224010571627:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2476+point split endpoint 4096 2477)/2 = (638435527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638435527:ℝ)/168755200)*ClassicalSixthBranch.v ((638435527:ℝ)/168755200)/ClassicalSixthBranch.r = (104742820879425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2476
  · change upperPayment 2477 ≤ upperValue ((point split endpoint 4096 2477+point split endpoint 4096 2478)/2)
    have hp : upperPayment 2477 = (223898920799:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2477+point split endpoint 4096 2478)/2 = (638460677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638460677:ℝ)/168755200)*ClassicalSixthBranch.v ((638460677:ℝ)/168755200)/ClassicalSixthBranch.r = (104721817188905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2477
  · change upperPayment 2478 ≤ upperValue ((point split endpoint 4096 2478+point split endpoint 4096 2479)/2)
    have hp : upperPayment 2478 = (223787241029:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2478+point split endpoint 4096 2479)/2 = (638485827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638485827:ℝ)/168755200)*ClassicalSixthBranch.v ((638485827:ℝ)/168755200)/ClassicalSixthBranch.r = (104700815522457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2478
  · change upperPayment 2479 ≤ upperValue ((point split endpoint 4096 2479+point split endpoint 4096 2480)/2)
    have hp : upperPayment 2479 = (223675532310:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2479+point split endpoint 4096 2480)/2 = (638510977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638510977:ℝ)/168755200)*ClassicalSixthBranch.v ((638510977:ℝ)/168755200)/ClassicalSixthBranch.r = (104679815880081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2479
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_154
