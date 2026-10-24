import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints255
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_255 (j : Fin 16) : upperPayment (16*255+j.val) ≤
    upperValue ((point split endpoint 4096 (16*255+j.val)+point split endpoint 4096 (16*255+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 4080 ≤ upperValue ((point split endpoint 4096 4080+point split endpoint 4096 4081)/2)
    have hp : upperPayment 4080 = (2612064873:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4080+point split endpoint 4096 4081)/2 = (678776127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678776127:ℝ)/168755200)*ClassicalSixthBranch.v ((678776127:ℝ)/168755200)/ClassicalSixthBranch.r = (73655060392977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4080
  · change upperPayment 4081 ≤ upperValue ((point split endpoint 4096 4081+point split endpoint 4096 4082)/2)
    have hp : upperPayment 4081 = (2443857747:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4081+point split endpoint 4096 4082)/2 = (678801277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678801277:ℝ)/168755200)*ClassicalSixthBranch.v ((678801277:ℝ)/168755200)/ClassicalSixthBranch.r = (73637303313945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4081
  · change upperPayment 4082 ≤ upperValue ((point split endpoint 4096 4082+point split endpoint 4096 4083)/2)
    have hp : upperPayment 4082 = (2275607477:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4082+point split endpoint 4096 4083)/2 = (678826427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678826427:ℝ)/168755200)*ClassicalSixthBranch.v ((678826427:ℝ)/168755200)/ClassicalSixthBranch.r = (73619548258985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4082
  · change upperPayment 4083 ≤ upperValue ((point split endpoint 4096 4083+point split endpoint 4096 4084)/2)
    have hp : upperPayment 4083 = (2107314052:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4083+point split endpoint 4096 4084)/2 = (678851577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678851577:ℝ)/168755200)*ClassicalSixthBranch.v ((678851577:ℝ)/168755200)/ClassicalSixthBranch.r = (73601795228097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4083
  · change upperPayment 4084 ≤ upperValue ((point split endpoint 4096 4084+point split endpoint 4096 4085)/2)
    have hp : upperPayment 4084 = (1938977459:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4084+point split endpoint 4096 4085)/2 = (678876727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678876727:ℝ)/168755200)*ClassicalSixthBranch.v ((678876727:ℝ)/168755200)/ClassicalSixthBranch.r = (73584044221281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4084
  · change upperPayment 4085 ≤ upperValue ((point split endpoint 4096 4085+point split endpoint 4096 4086)/2)
    have hp : upperPayment 4085 = (1770597686:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4085+point split endpoint 4096 4086)/2 = (678901877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678901877:ℝ)/168755200)*ClassicalSixthBranch.v ((678901877:ℝ)/168755200)/ClassicalSixthBranch.r = (73566295238537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4085
  · change upperPayment 4086 ≤ upperValue ((point split endpoint 4096 4086+point split endpoint 4096 4087)/2)
    have hp : upperPayment 4086 = (1602174720:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4086+point split endpoint 4096 4087)/2 = (678927027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678927027:ℝ)/168755200)*ClassicalSixthBranch.v ((678927027:ℝ)/168755200)/ClassicalSixthBranch.r = (73548548279865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4086
  · change upperPayment 4087 ≤ upperValue ((point split endpoint 4096 4087+point split endpoint 4096 4088)/2)
    have hp : upperPayment 4087 = (1433708551:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4087+point split endpoint 4096 4088)/2 = (678952177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678952177:ℝ)/168755200)*ClassicalSixthBranch.v ((678952177:ℝ)/168755200)/ClassicalSixthBranch.r = (73530803345265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4087
  · change upperPayment 4088 ≤ upperValue ((point split endpoint 4096 4088+point split endpoint 4096 4089)/2)
    have hp : upperPayment 4088 = (1265199164:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4088+point split endpoint 4096 4089)/2 = (678977327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((678977327:ℝ)/168755200)*ClassicalSixthBranch.v ((678977327:ℝ)/168755200)/ClassicalSixthBranch.r = (73513060434737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4088
  · change upperPayment 4089 ≤ upperValue ((point split endpoint 4096 4089+point split endpoint 4096 4090)/2)
    have hp : upperPayment 4089 = (1096646548:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4089+point split endpoint 4096 4090)/2 = (679002477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((679002477:ℝ)/168755200)*ClassicalSixthBranch.v ((679002477:ℝ)/168755200)/ClassicalSixthBranch.r = (73495319548281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4089
  · change upperPayment 4090 ≤ upperValue ((point split endpoint 4096 4090+point split endpoint 4096 4091)/2)
    have hp : upperPayment 4090 = (928050692:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4090+point split endpoint 4096 4091)/2 = (679027627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((679027627:ℝ)/168755200)*ClassicalSixthBranch.v ((679027627:ℝ)/168755200)/ClassicalSixthBranch.r = (73477580685897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4090
  · change upperPayment 4091 ≤ upperValue ((point split endpoint 4096 4091+point split endpoint 4096 4092)/2)
    have hp : upperPayment 4091 = (759411582:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4091+point split endpoint 4096 4092)/2 = (679052777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((679052777:ℝ)/168755200)*ClassicalSixthBranch.v ((679052777:ℝ)/168755200)/ClassicalSixthBranch.r = (73459843847585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4091
  · change upperPayment 4092 ≤ upperValue ((point split endpoint 4096 4092+point split endpoint 4096 4093)/2)
    have hp : upperPayment 4092 = (590729206:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4092+point split endpoint 4096 4093)/2 = (679077927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((679077927:ℝ)/168755200)*ClassicalSixthBranch.v ((679077927:ℝ)/168755200)/ClassicalSixthBranch.r = (73442109033345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4092
  · change upperPayment 4093 ≤ upperValue ((point split endpoint 4096 4093+point split endpoint 4096 4094)/2)
    have hp : upperPayment 4093 = (422003553:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4093+point split endpoint 4096 4094)/2 = (679103077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((679103077:ℝ)/168755200)*ClassicalSixthBranch.v ((679103077:ℝ)/168755200)/ClassicalSixthBranch.r = (73424376243177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4093
  · change upperPayment 4094 ≤ upperValue ((point split endpoint 4096 4094+point split endpoint 4096 4095)/2)
    have hp : upperPayment 4094 = (253234610:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4094+point split endpoint 4096 4095)/2 = (679128227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((679128227:ℝ)/168755200)*ClassicalSixthBranch.v ((679128227:ℝ)/168755200)/ClassicalSixthBranch.r = (73406645477081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4094
  · change upperPayment 4095 ≤ upperValue ((point split endpoint 4096 4095+point split endpoint 4096 4096)/2)
    have hp : upperPayment 4095 = (84422364:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4095+point split endpoint 4096 4096)/2 = (679153377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((679153377:ℝ)/168755200)*ClassicalSixthBranch.v ((679153377:ℝ)/168755200)/ClassicalSixthBranch.r = (73388916735057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4095
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_255
