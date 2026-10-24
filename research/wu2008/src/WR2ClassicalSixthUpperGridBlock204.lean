import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints204
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_204 (j : Fin 16) : upperPayment (16*204+j.val) ≤
    upperValue ((point split endpoint 4096 (16*204+j.val)+point split endpoint 4096 (16*204+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3264 ≤ upperValue ((point split endpoint 4096 3264+point split endpoint 4096 3265)/2)
    have hp : upperPayment 3264 = (126503130424:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3264+point split endpoint 4096 3265)/2 = (658253727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658253727:ℝ)/168755200)*ClassicalSixthBranch.v ((658253727:ℝ)/168755200)/ClassicalSixthBranch.r = (88819532947281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3264
  · change upperPayment 3265 ≤ upperValue ((point split endpoint 4096 3265+point split endpoint 4096 3266)/2)
    have hp : upperPayment 3265 = (126366506584:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3265+point split endpoint 4096 3266)/2 = (658278877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658278877:ℝ)/168755200)*ClassicalSixthBranch.v ((658278877:ℝ)/168755200)/ClassicalSixthBranch.r = (88800124225497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3265
  · change upperPayment 3266 ≤ upperValue ((point split endpoint 4096 3266+point split endpoint 4096 3267)/2)
    have hp : upperPayment 3266 = (126229847987:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3266+point split endpoint 4096 3267)/2 = (658304027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658304027:ℝ)/168755200)*ClassicalSixthBranch.v ((658304027:ℝ)/168755200)/ClassicalSixthBranch.r = (88780717527785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3266
  · change upperPayment 3267 ≤ upperValue ((point split endpoint 4096 3267+point split endpoint 4096 3268)/2)
    have hp : upperPayment 3267 = (126093154625:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3267+point split endpoint 4096 3268)/2 = (658329177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658329177:ℝ)/168755200)*ClassicalSixthBranch.v ((658329177:ℝ)/168755200)/ClassicalSixthBranch.r = (88761312854145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3267
  · change upperPayment 3268 ≤ upperValue ((point split endpoint 4096 3268+point split endpoint 4096 3269)/2)
    have hp : upperPayment 3268 = (125956426488:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3268+point split endpoint 4096 3269)/2 = (658354327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658354327:ℝ)/168755200)*ClassicalSixthBranch.v ((658354327:ℝ)/168755200)/ClassicalSixthBranch.r = (88741910204577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3268
  · change upperPayment 3269 ≤ upperValue ((point split endpoint 4096 3269+point split endpoint 4096 3270)/2)
    have hp : upperPayment 3269 = (125819663568:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3269+point split endpoint 4096 3270)/2 = (658379477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658379477:ℝ)/168755200)*ClassicalSixthBranch.v ((658379477:ℝ)/168755200)/ClassicalSixthBranch.r = (88722509579081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3269
  · change upperPayment 3270 ≤ upperValue ((point split endpoint 4096 3270+point split endpoint 4096 3271)/2)
    have hp : upperPayment 3270 = (125682865857:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3270+point split endpoint 4096 3271)/2 = (658404627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658404627:ℝ)/168755200)*ClassicalSixthBranch.v ((658404627:ℝ)/168755200)/ClassicalSixthBranch.r = (88703110977657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3270
  · change upperPayment 3271 ≤ upperValue ((point split endpoint 4096 3271+point split endpoint 4096 3272)/2)
    have hp : upperPayment 3271 = (125546033345:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3271+point split endpoint 4096 3272)/2 = (658429777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658429777:ℝ)/168755200)*ClassicalSixthBranch.v ((658429777:ℝ)/168755200)/ClassicalSixthBranch.r = (88683714400305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3271
  · change upperPayment 3272 ≤ upperValue ((point split endpoint 4096 3272+point split endpoint 4096 3273)/2)
    have hp : upperPayment 3272 = (125409166025:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3272+point split endpoint 4096 3273)/2 = (658454927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658454927:ℝ)/168755200)*ClassicalSixthBranch.v ((658454927:ℝ)/168755200)/ClassicalSixthBranch.r = (88664319847025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3272
  · change upperPayment 3273 ≤ upperValue ((point split endpoint 4096 3273+point split endpoint 4096 3274)/2)
    have hp : upperPayment 3273 = (125272263887:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3273+point split endpoint 4096 3274)/2 = (658480077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658480077:ℝ)/168755200)*ClassicalSixthBranch.v ((658480077:ℝ)/168755200)/ClassicalSixthBranch.r = (88644927317817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3273
  · change upperPayment 3274 ≤ upperValue ((point split endpoint 4096 3274+point split endpoint 4096 3275)/2)
    have hp : upperPayment 3274 = (125135326923:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3274+point split endpoint 4096 3275)/2 = (658505227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658505227:ℝ)/168755200)*ClassicalSixthBranch.v ((658505227:ℝ)/168755200)/ClassicalSixthBranch.r = (88625536812681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3274
  · change upperPayment 3275 ≤ upperValue ((point split endpoint 4096 3275+point split endpoint 4096 3276)/2)
    have hp : upperPayment 3275 = (124998355124:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3275+point split endpoint 4096 3276)/2 = (658530377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658530377:ℝ)/168755200)*ClassicalSixthBranch.v ((658530377:ℝ)/168755200)/ClassicalSixthBranch.r = (88606148331617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3275
  · change upperPayment 3276 ≤ upperValue ((point split endpoint 4096 3276+point split endpoint 4096 3277)/2)
    have hp : upperPayment 3276 = (124861348481:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3276+point split endpoint 4096 3277)/2 = (658555527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658555527:ℝ)/168755200)*ClassicalSixthBranch.v ((658555527:ℝ)/168755200)/ClassicalSixthBranch.r = (88586761874625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3276
  · change upperPayment 3277 ≤ upperValue ((point split endpoint 4096 3277+point split endpoint 4096 3278)/2)
    have hp : upperPayment 3277 = (124724306987:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3277+point split endpoint 4096 3278)/2 = (658580677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658580677:ℝ)/168755200)*ClassicalSixthBranch.v ((658580677:ℝ)/168755200)/ClassicalSixthBranch.r = (88567377441705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3277
  · change upperPayment 3278 ≤ upperValue ((point split endpoint 4096 3278+point split endpoint 4096 3279)/2)
    have hp : upperPayment 3278 = (124587230631:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3278+point split endpoint 4096 3279)/2 = (658605827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658605827:ℝ)/168755200)*ClassicalSixthBranch.v ((658605827:ℝ)/168755200)/ClassicalSixthBranch.r = (88547995032857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3278
  · change upperPayment 3279 ≤ upperValue ((point split endpoint 4096 3279+point split endpoint 4096 3280)/2)
    have hp : upperPayment 3279 = (124450119406:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3279+point split endpoint 4096 3280)/2 = (658630977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((658630977:ℝ)/168755200)*ClassicalSixthBranch.v ((658630977:ℝ)/168755200)/ClassicalSixthBranch.r = (88528614648081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3279
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_204
