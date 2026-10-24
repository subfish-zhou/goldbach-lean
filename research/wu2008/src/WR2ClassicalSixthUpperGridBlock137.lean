import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints137
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_137 (j : Fin 16) : upperPayment (16*137+j.val) ≤
    upperValue ((point split endpoint 4096 (16*137+j.val)+point split endpoint 4096 (16*137+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2192 ≤ upperValue ((point split endpoint 4096 2192+point split endpoint 4096 2193)/2)
    have hp : upperPayment 2192 = (254571631611:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2192+point split endpoint 4096 2193)/2 = (631292927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631292927:ℝ)/168755200)*ClassicalSixthBranch.v ((631292927:ℝ)/168755200)/ClassicalSixthBranch.r = (110789783180945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2192
  · change upperPayment 2193 ≤ upperValue ((point split endpoint 4096 2193+point split endpoint 4096 2194)/2)
    have hp : upperPayment 2193 = (254467956014:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2193+point split endpoint 4096 2194)/2 = (631318077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631318077:ℝ)/168755200)*ClassicalSixthBranch.v ((631318077:ℝ)/168755200)/ClassicalSixthBranch.r = (110768204653977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2193
  · change upperPayment 2194 ≤ upperValue ((point split endpoint 4096 2194+point split endpoint 4096 2195)/2)
    have hp : upperPayment 2194 = (254364253156:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2194+point split endpoint 4096 2195)/2 = (631343227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631343227:ℝ)/168755200)*ClassicalSixthBranch.v ((631343227:ℝ)/168755200)/ClassicalSixthBranch.r = (110746628151081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2194
  · change upperPayment 2195 ≤ upperValue ((point split endpoint 4096 2195+point split endpoint 4096 2196)/2)
    have hp : upperPayment 2195 = (254260523034:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2195+point split endpoint 4096 2196)/2 = (631368377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631368377:ℝ)/168755200)*ClassicalSixthBranch.v ((631368377:ℝ)/168755200)/ClassicalSixthBranch.r = (110725053672257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2195
  · change upperPayment 2196 ≤ upperValue ((point split endpoint 4096 2196+point split endpoint 4096 2197)/2)
    have hp : upperPayment 2196 = (254156765641:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2196+point split endpoint 4096 2197)/2 = (631393527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631393527:ℝ)/168755200)*ClassicalSixthBranch.v ((631393527:ℝ)/168755200)/ClassicalSixthBranch.r = (110703481217505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2196
  · change upperPayment 2197 ≤ upperValue ((point split endpoint 4096 2197+point split endpoint 4096 2198)/2)
    have hp : upperPayment 2197 = (254052980972:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2197+point split endpoint 4096 2198)/2 = (631418677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631418677:ℝ)/168755200)*ClassicalSixthBranch.v ((631418677:ℝ)/168755200)/ClassicalSixthBranch.r = (110681910786825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2197
  · change upperPayment 2198 ≤ upperValue ((point split endpoint 4096 2198+point split endpoint 4096 2199)/2)
    have hp : upperPayment 2198 = (253949169021:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2198+point split endpoint 4096 2199)/2 = (631443827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631443827:ℝ)/168755200)*ClassicalSixthBranch.v ((631443827:ℝ)/168755200)/ClassicalSixthBranch.r = (110660342380217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2198
  · change upperPayment 2199 ≤ upperValue ((point split endpoint 4096 2199+point split endpoint 4096 2200)/2)
    have hp : upperPayment 2199 = (253845329783:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2199+point split endpoint 4096 2200)/2 = (631468977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631468977:ℝ)/168755200)*ClassicalSixthBranch.v ((631468977:ℝ)/168755200)/ClassicalSixthBranch.r = (110638775997681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2199
  · change upperPayment 2200 ≤ upperValue ((point split endpoint 4096 2200+point split endpoint 4096 2201)/2)
    have hp : upperPayment 2200 = (253741463252:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2200+point split endpoint 4096 2201)/2 = (631494127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631494127:ℝ)/168755200)*ClassicalSixthBranch.v ((631494127:ℝ)/168755200)/ClassicalSixthBranch.r = (110617211639217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2200
  · change upperPayment 2201 ≤ upperValue ((point split endpoint 4096 2201+point split endpoint 4096 2202)/2)
    have hp : upperPayment 2201 = (253637569422:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2201+point split endpoint 4096 2202)/2 = (631519277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631519277:ℝ)/168755200)*ClassicalSixthBranch.v ((631519277:ℝ)/168755200)/ClassicalSixthBranch.r = (110595649304825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2201
  · change upperPayment 2202 ≤ upperValue ((point split endpoint 4096 2202+point split endpoint 4096 2203)/2)
    have hp : upperPayment 2202 = (253533648288:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2202+point split endpoint 4096 2203)/2 = (631544427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631544427:ℝ)/168755200)*ClassicalSixthBranch.v ((631544427:ℝ)/168755200)/ClassicalSixthBranch.r = (110574088994505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2202
  · change upperPayment 2203 ≤ upperValue ((point split endpoint 4096 2203+point split endpoint 4096 2204)/2)
    have hp : upperPayment 2203 = (253429699844:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2203+point split endpoint 4096 2204)/2 = (631569577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631569577:ℝ)/168755200)*ClassicalSixthBranch.v ((631569577:ℝ)/168755200)/ClassicalSixthBranch.r = (110552530708257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2203
  · change upperPayment 2204 ≤ upperValue ((point split endpoint 4096 2204+point split endpoint 4096 2205)/2)
    have hp : upperPayment 2204 = (253325724085:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2204+point split endpoint 4096 2205)/2 = (631594727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631594727:ℝ)/168755200)*ClassicalSixthBranch.v ((631594727:ℝ)/168755200)/ClassicalSixthBranch.r = (110530974446081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2204
  · change upperPayment 2205 ≤ upperValue ((point split endpoint 4096 2205+point split endpoint 4096 2206)/2)
    have hp : upperPayment 2205 = (253221721004:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2205+point split endpoint 4096 2206)/2 = (631619877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631619877:ℝ)/168755200)*ClassicalSixthBranch.v ((631619877:ℝ)/168755200)/ClassicalSixthBranch.r = (110509420207977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2205
  · change upperPayment 2206 ≤ upperValue ((point split endpoint 4096 2206+point split endpoint 4096 2207)/2)
    have hp : upperPayment 2206 = (253117690597:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2206+point split endpoint 4096 2207)/2 = (631645027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631645027:ℝ)/168755200)*ClassicalSixthBranch.v ((631645027:ℝ)/168755200)/ClassicalSixthBranch.r = (110487867993945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2206
  · change upperPayment 2207 ≤ upperValue ((point split endpoint 4096 2207+point split endpoint 4096 2208)/2)
    have hp : upperPayment 2207 = (253013632857:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2207+point split endpoint 4096 2208)/2 = (631670177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631670177:ℝ)/168755200)*ClassicalSixthBranch.v ((631670177:ℝ)/168755200)/ClassicalSixthBranch.r = (110466317803985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2207
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_137
