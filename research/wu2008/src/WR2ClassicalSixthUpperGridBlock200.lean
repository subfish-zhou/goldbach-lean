import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints200
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_200 (j : Fin 16) : upperPayment (16*200+j.val) ≤
    upperValue ((point split endpoint 4096 (16*200+j.val)+point split endpoint 4096 (16*200+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3200 ≤ upperValue ((point split endpoint 4096 3200+point split endpoint 4096 3201)/2)
    have hp : upperPayment 3200 = (135175153476:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3200+point split endpoint 4096 3201)/2 = (656644127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656644127:ℝ)/168755200)*ClassicalSixthBranch.v ((656644127:ℝ)/168755200)/ClassicalSixthBranch.r = (90065901211217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3200
  · change upperPayment 3201 ≤ upperValue ((point split endpoint 4096 3201+point split endpoint 4096 3202)/2)
    have hp : upperPayment 3201 = (135040736308:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3201+point split endpoint 4096 3202)/2 = (656669277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656669277:ℝ)/168755200)*ClassicalSixthBranch.v ((656669277:ℝ)/168755200)/ClassicalSixthBranch.r = (90046362948825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3201
  · change upperPayment 3202 ≤ upperValue ((point split endpoint 4096 3202+point split endpoint 4096 3203)/2)
    have hp : upperPayment 3202 = (134906284928:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3202+point split endpoint 4096 3203)/2 = (656694427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656694427:ℝ)/168755200)*ClassicalSixthBranch.v ((656694427:ℝ)/168755200)/ClassicalSixthBranch.r = (90026826710505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3202
  · change upperPayment 3203 ≤ upperValue ((point split endpoint 4096 3203+point split endpoint 4096 3204)/2)
    have hp : upperPayment 3203 = (134771799327:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3203+point split endpoint 4096 3204)/2 = (656719577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656719577:ℝ)/168755200)*ClassicalSixthBranch.v ((656719577:ℝ)/168755200)/ClassicalSixthBranch.r = (90007292496257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3203
  · change upperPayment 3204 ≤ upperValue ((point split endpoint 4096 3204+point split endpoint 4096 3205)/2)
    have hp : upperPayment 3204 = (134637279496:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3204+point split endpoint 4096 3205)/2 = (656744727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656744727:ℝ)/168755200)*ClassicalSixthBranch.v ((656744727:ℝ)/168755200)/ClassicalSixthBranch.r = (89987760306081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3204
  · change upperPayment 3205 ≤ upperValue ((point split endpoint 4096 3205+point split endpoint 4096 3206)/2)
    have hp : upperPayment 3205 = (134502725429:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3205+point split endpoint 4096 3206)/2 = (656769877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656769877:ℝ)/168755200)*ClassicalSixthBranch.v ((656769877:ℝ)/168755200)/ClassicalSixthBranch.r = (89968230139977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3205
  · change upperPayment 3206 ≤ upperValue ((point split endpoint 4096 3206+point split endpoint 4096 3207)/2)
    have hp : upperPayment 3206 = (134368137115:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3206+point split endpoint 4096 3207)/2 = (656795027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656795027:ℝ)/168755200)*ClassicalSixthBranch.v ((656795027:ℝ)/168755200)/ClassicalSixthBranch.r = (89948701997945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3206
  · change upperPayment 3207 ≤ upperValue ((point split endpoint 4096 3207+point split endpoint 4096 3208)/2)
    have hp : upperPayment 3207 = (134233514547:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3207+point split endpoint 4096 3208)/2 = (656820177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656820177:ℝ)/168755200)*ClassicalSixthBranch.v ((656820177:ℝ)/168755200)/ClassicalSixthBranch.r = (89929175879985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3207
  · change upperPayment 3208 ≤ upperValue ((point split endpoint 4096 3208+point split endpoint 4096 3209)/2)
    have hp : upperPayment 3208 = (134098857716:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3208+point split endpoint 4096 3209)/2 = (656845327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656845327:ℝ)/168755200)*ClassicalSixthBranch.v ((656845327:ℝ)/168755200)/ClassicalSixthBranch.r = (89909651786097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3208
  · change upperPayment 3209 ≤ upperValue ((point split endpoint 4096 3209+point split endpoint 4096 3210)/2)
    have hp : upperPayment 3209 = (133964166614:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3209+point split endpoint 4096 3210)/2 = (656870477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656870477:ℝ)/168755200)*ClassicalSixthBranch.v ((656870477:ℝ)/168755200)/ClassicalSixthBranch.r = (89890129716281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3209
  · change upperPayment 3210 ≤ upperValue ((point split endpoint 4096 3210+point split endpoint 4096 3211)/2)
    have hp : upperPayment 3210 = (133829441233:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3210+point split endpoint 4096 3211)/2 = (656895627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656895627:ℝ)/168755200)*ClassicalSixthBranch.v ((656895627:ℝ)/168755200)/ClassicalSixthBranch.r = (89870609670537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3210
  · change upperPayment 3211 ≤ upperValue ((point split endpoint 4096 3211+point split endpoint 4096 3212)/2)
    have hp : upperPayment 3211 = (133694681563:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3211+point split endpoint 4096 3212)/2 = (656920777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656920777:ℝ)/168755200)*ClassicalSixthBranch.v ((656920777:ℝ)/168755200)/ClassicalSixthBranch.r = (89851091648865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3211
  · change upperPayment 3212 ≤ upperValue ((point split endpoint 4096 3212+point split endpoint 4096 3213)/2)
    have hp : upperPayment 3212 = (133559887597:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3212+point split endpoint 4096 3213)/2 = (656945927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656945927:ℝ)/168755200)*ClassicalSixthBranch.v ((656945927:ℝ)/168755200)/ClassicalSixthBranch.r = (89831575651265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3212
  · change upperPayment 3213 ≤ upperValue ((point split endpoint 4096 3213+point split endpoint 4096 3214)/2)
    have hp : upperPayment 3213 = (133425059326:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3213+point split endpoint 4096 3214)/2 = (656971077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656971077:ℝ)/168755200)*ClassicalSixthBranch.v ((656971077:ℝ)/168755200)/ClassicalSixthBranch.r = (89812061677737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3213
  · change upperPayment 3214 ≤ upperValue ((point split endpoint 4096 3214+point split endpoint 4096 3215)/2)
    have hp : upperPayment 3214 = (133290196741:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3214+point split endpoint 4096 3215)/2 = (656996227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((656996227:ℝ)/168755200)*ClassicalSixthBranch.v ((656996227:ℝ)/168755200)/ClassicalSixthBranch.r = (89792549728281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3214
  · change upperPayment 3215 ≤ upperValue ((point split endpoint 4096 3215+point split endpoint 4096 3216)/2)
    have hp : upperPayment 3215 = (133155299835:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3215+point split endpoint 4096 3216)/2 = (657021377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657021377:ℝ)/168755200)*ClassicalSixthBranch.v ((657021377:ℝ)/168755200)/ClassicalSixthBranch.r = (89773039802897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3215
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_200
