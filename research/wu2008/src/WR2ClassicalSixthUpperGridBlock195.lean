import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints195
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_195 (j : Fin 16) : upperPayment (16*195+j.val) ≤
    upperValue ((point split endpoint 4096 (16*195+j.val)+point split endpoint 4096 (16*195+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3120 ≤ upperValue ((point split endpoint 4096 3120+point split endpoint 4096 3121)/2)
    have hp : upperPayment 3120 = (145818416886:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3120+point split endpoint 4096 3121)/2 = (654632127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654632127:ℝ)/168755200)*ClassicalSixthBranch.v ((654632127:ℝ)/168755200)/ClassicalSixthBranch.r = (91635520195857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3120
  · change upperPayment 3121 ≤ upperValue ((point split endpoint 4096 3121+point split endpoint 4096 3122)/2)
    have hp : upperPayment 3121 = (145686709781:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3121+point split endpoint 4096 3122)/2 = (654657277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654657277:ℝ)/168755200)*ClassicalSixthBranch.v ((654657277:ℝ)/168755200)/ClassicalSixthBranch.r = (91615820007705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3121
  · change upperPayment 3122 ≤ upperValue ((point split endpoint 4096 3122+point split endpoint 4096 3123)/2)
    have hp : upperPayment 3122 = (145554969124:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3122+point split endpoint 4096 3123)/2 = (654682427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654682427:ℝ)/168755200)*ClassicalSixthBranch.v ((654682427:ℝ)/168755200)/ClassicalSixthBranch.r = (91596121843625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3122
  · change upperPayment 3123 ≤ upperValue ((point split endpoint 4096 3123+point split endpoint 4096 3124)/2)
    have hp : upperPayment 3123 = (145423194908:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3123+point split endpoint 4096 3124)/2 = (654707577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654707577:ℝ)/168755200)*ClassicalSixthBranch.v ((654707577:ℝ)/168755200)/ClassicalSixthBranch.r = (91576425703617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3123
  · change upperPayment 3124 ≤ upperValue ((point split endpoint 4096 3124+point split endpoint 4096 3125)/2)
    have hp : upperPayment 3124 = (145291387125:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3124+point split endpoint 4096 3125)/2 = (654732727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654732727:ℝ)/168755200)*ClassicalSixthBranch.v ((654732727:ℝ)/168755200)/ClassicalSixthBranch.r = (91556731587681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3124
  · change upperPayment 3125 ≤ upperValue ((point split endpoint 4096 3125+point split endpoint 4096 3126)/2)
    have hp : upperPayment 3125 = (145159545766:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3125+point split endpoint 4096 3126)/2 = (654757877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654757877:ℝ)/168755200)*ClassicalSixthBranch.v ((654757877:ℝ)/168755200)/ClassicalSixthBranch.r = (91537039495817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3125
  · change upperPayment 3126 ≤ upperValue ((point split endpoint 4096 3126+point split endpoint 4096 3127)/2)
    have hp : upperPayment 3126 = (145027670824:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3126+point split endpoint 4096 3127)/2 = (654783027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654783027:ℝ)/168755200)*ClassicalSixthBranch.v ((654783027:ℝ)/168755200)/ClassicalSixthBranch.r = (91517349428025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3126
  · change upperPayment 3127 ≤ upperValue ((point split endpoint 4096 3127+point split endpoint 4096 3128)/2)
    have hp : upperPayment 3127 = (144895762289:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3127+point split endpoint 4096 3128)/2 = (654808177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654808177:ℝ)/168755200)*ClassicalSixthBranch.v ((654808177:ℝ)/168755200)/ClassicalSixthBranch.r = (91497661384305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3127
  · change upperPayment 3128 ≤ upperValue ((point split endpoint 4096 3128+point split endpoint 4096 3129)/2)
    have hp : upperPayment 3128 = (144763820155:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3128+point split endpoint 4096 3129)/2 = (654833327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654833327:ℝ)/168755200)*ClassicalSixthBranch.v ((654833327:ℝ)/168755200)/ClassicalSixthBranch.r = (91477975364657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3128
  · change upperPayment 3129 ≤ upperValue ((point split endpoint 4096 3129+point split endpoint 4096 3130)/2)
    have hp : upperPayment 3129 = (144631844413:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3129+point split endpoint 4096 3130)/2 = (654858477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654858477:ℝ)/168755200)*ClassicalSixthBranch.v ((654858477:ℝ)/168755200)/ClassicalSixthBranch.r = (91458291369081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3129
  · change upperPayment 3130 ≤ upperValue ((point split endpoint 4096 3130+point split endpoint 4096 3131)/2)
    have hp : upperPayment 3130 = (144499835054:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3130+point split endpoint 4096 3131)/2 = (654883627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654883627:ℝ)/168755200)*ClassicalSixthBranch.v ((654883627:ℝ)/168755200)/ClassicalSixthBranch.r = (91438609397577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3130
  · change upperPayment 3131 ≤ upperValue ((point split endpoint 4096 3131+point split endpoint 4096 3132)/2)
    have hp : upperPayment 3131 = (144367792071:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3131+point split endpoint 4096 3132)/2 = (654908777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654908777:ℝ)/168755200)*ClassicalSixthBranch.v ((654908777:ℝ)/168755200)/ClassicalSixthBranch.r = (91418929450145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3131
  · change upperPayment 3132 ≤ upperValue ((point split endpoint 4096 3132+point split endpoint 4096 3133)/2)
    have hp : upperPayment 3132 = (144235715456:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3132+point split endpoint 4096 3133)/2 = (654933927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654933927:ℝ)/168755200)*ClassicalSixthBranch.v ((654933927:ℝ)/168755200)/ClassicalSixthBranch.r = (91399251526785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3132
  · change upperPayment 3133 ≤ upperValue ((point split endpoint 4096 3133+point split endpoint 4096 3134)/2)
    have hp : upperPayment 3133 = (144103605199:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3133+point split endpoint 4096 3134)/2 = (654959077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654959077:ℝ)/168755200)*ClassicalSixthBranch.v ((654959077:ℝ)/168755200)/ClassicalSixthBranch.r = (91379575627497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3133
  · change upperPayment 3134 ≤ upperValue ((point split endpoint 4096 3134+point split endpoint 4096 3135)/2)
    have hp : upperPayment 3134 = (143971461294:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3134+point split endpoint 4096 3135)/2 = (654984227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654984227:ℝ)/168755200)*ClassicalSixthBranch.v ((654984227:ℝ)/168755200)/ClassicalSixthBranch.r = (91359901752281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3134
  · change upperPayment 3135 ≤ upperValue ((point split endpoint 4096 3135+point split endpoint 4096 3136)/2)
    have hp : upperPayment 3135 = (143839283731:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3135+point split endpoint 4096 3136)/2 = (655009377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655009377:ℝ)/168755200)*ClassicalSixthBranch.v ((655009377:ℝ)/168755200)/ClassicalSixthBranch.r = (91340229901137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3135
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_195
