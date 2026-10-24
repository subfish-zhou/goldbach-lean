import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints196
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_196 (j : Fin 16) : upperPayment (16*196+j.val) ≤
    upperValue ((point split endpoint 4096 (16*196+j.val)+point split endpoint 4096 (16*196+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3136 ≤ upperValue ((point split endpoint 4096 3136+point split endpoint 4096 3137)/2)
    have hp : upperPayment 3136 = (143707072504:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3136+point split endpoint 4096 3137)/2 = (655034527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655034527:ℝ)/168755200)*ClassicalSixthBranch.v ((655034527:ℝ)/168755200)/ClassicalSixthBranch.r = (91320560074065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3136
  · change upperPayment 3137 ≤ upperValue ((point split endpoint 4096 3137+point split endpoint 4096 3138)/2)
    have hp : upperPayment 3137 = (143574827603:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3137+point split endpoint 4096 3138)/2 = (655059677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655059677:ℝ)/168755200)*ClassicalSixthBranch.v ((655059677:ℝ)/168755200)/ClassicalSixthBranch.r = (91300892271065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3137
  · change upperPayment 3138 ≤ upperValue ((point split endpoint 4096 3138+point split endpoint 4096 3139)/2)
    have hp : upperPayment 3138 = (143442549020:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3138+point split endpoint 4096 3139)/2 = (655084827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655084827:ℝ)/168755200)*ClassicalSixthBranch.v ((655084827:ℝ)/168755200)/ClassicalSixthBranch.r = (91281226492137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3138
  · change upperPayment 3139 ≤ upperValue ((point split endpoint 4096 3139+point split endpoint 4096 3140)/2)
    have hp : upperPayment 3139 = (143310236747:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3139+point split endpoint 4096 3140)/2 = (655109977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655109977:ℝ)/168755200)*ClassicalSixthBranch.v ((655109977:ℝ)/168755200)/ClassicalSixthBranch.r = (91261562737281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3139
  · change upperPayment 3140 ≤ upperValue ((point split endpoint 4096 3140+point split endpoint 4096 3141)/2)
    have hp : upperPayment 3140 = (143177890777:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3140+point split endpoint 4096 3141)/2 = (655135127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655135127:ℝ)/168755200)*ClassicalSixthBranch.v ((655135127:ℝ)/168755200)/ClassicalSixthBranch.r = (91241901006497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3140
  · change upperPayment 3141 ≤ upperValue ((point split endpoint 4096 3141+point split endpoint 4096 3142)/2)
    have hp : upperPayment 3141 = (143045511100:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3141+point split endpoint 4096 3142)/2 = (655160277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655160277:ℝ)/168755200)*ClassicalSixthBranch.v ((655160277:ℝ)/168755200)/ClassicalSixthBranch.r = (91222241299785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3141
  · change upperPayment 3142 ≤ upperValue ((point split endpoint 4096 3142+point split endpoint 4096 3143)/2)
    have hp : upperPayment 3142 = (142913097709:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3142+point split endpoint 4096 3143)/2 = (655185427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655185427:ℝ)/168755200)*ClassicalSixthBranch.v ((655185427:ℝ)/168755200)/ClassicalSixthBranch.r = (91202583617145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3142
  · change upperPayment 3143 ≤ upperValue ((point split endpoint 4096 3143+point split endpoint 4096 3144)/2)
    have hp : upperPayment 3143 = (142780650595:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3143+point split endpoint 4096 3144)/2 = (655210577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655210577:ℝ)/168755200)*ClassicalSixthBranch.v ((655210577:ℝ)/168755200)/ClassicalSixthBranch.r = (91182927958577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3143
  · change upperPayment 3144 ≤ upperValue ((point split endpoint 4096 3144+point split endpoint 4096 3145)/2)
    have hp : upperPayment 3144 = (142648169750:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3144+point split endpoint 4096 3145)/2 = (655235727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655235727:ℝ)/168755200)*ClassicalSixthBranch.v ((655235727:ℝ)/168755200)/ClassicalSixthBranch.r = (91163274324081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3144
  · change upperPayment 3145 ≤ upperValue ((point split endpoint 4096 3145+point split endpoint 4096 3146)/2)
    have hp : upperPayment 3145 = (142515655167:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3145+point split endpoint 4096 3146)/2 = (655260877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655260877:ℝ)/168755200)*ClassicalSixthBranch.v ((655260877:ℝ)/168755200)/ClassicalSixthBranch.r = (91143622713657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3145
  · change upperPayment 3146 ≤ upperValue ((point split endpoint 4096 3146+point split endpoint 4096 3147)/2)
    have hp : upperPayment 3146 = (142383106836:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3146+point split endpoint 4096 3147)/2 = (655286027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655286027:ℝ)/168755200)*ClassicalSixthBranch.v ((655286027:ℝ)/168755200)/ClassicalSixthBranch.r = (91123973127305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3146
  · change upperPayment 3147 ≤ upperValue ((point split endpoint 4096 3147+point split endpoint 4096 3148)/2)
    have hp : upperPayment 3147 = (142250524749:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3147+point split endpoint 4096 3148)/2 = (655311177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655311177:ℝ)/168755200)*ClassicalSixthBranch.v ((655311177:ℝ)/168755200)/ClassicalSixthBranch.r = (91104325565025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3147
  · change upperPayment 3148 ≤ upperValue ((point split endpoint 4096 3148+point split endpoint 4096 3149)/2)
    have hp : upperPayment 3148 = (142117908900:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3148+point split endpoint 4096 3149)/2 = (655336327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655336327:ℝ)/168755200)*ClassicalSixthBranch.v ((655336327:ℝ)/168755200)/ClassicalSixthBranch.r = (91084680026817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3148
  · change upperPayment 3149 ≤ upperValue ((point split endpoint 4096 3149+point split endpoint 4096 3150)/2)
    have hp : upperPayment 3149 = (141985259278:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3149+point split endpoint 4096 3150)/2 = (655361477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655361477:ℝ)/168755200)*ClassicalSixthBranch.v ((655361477:ℝ)/168755200)/ClassicalSixthBranch.r = (91065036512681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3149
  · change upperPayment 3150 ≤ upperValue ((point split endpoint 4096 3150+point split endpoint 4096 3151)/2)
    have hp : upperPayment 3150 = (141852575876:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3150+point split endpoint 4096 3151)/2 = (655386627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655386627:ℝ)/168755200)*ClassicalSixthBranch.v ((655386627:ℝ)/168755200)/ClassicalSixthBranch.r = (91045395022617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3150
  · change upperPayment 3151 ≤ upperValue ((point split endpoint 4096 3151+point split endpoint 4096 3152)/2)
    have hp : upperPayment 3151 = (141719858686:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3151+point split endpoint 4096 3152)/2 = (655411777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((655411777:ℝ)/168755200)*ClassicalSixthBranch.v ((655411777:ℝ)/168755200)/ClassicalSixthBranch.r = (91025755556625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3151
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_196
