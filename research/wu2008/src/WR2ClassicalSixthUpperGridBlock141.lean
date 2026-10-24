import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints141
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_141 (j : Fin 16) : upperPayment (16*141+j.val) ≤
    upperValue ((point split endpoint 4096 (16*141+j.val)+point split endpoint 4096 (16*141+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2256 ≤ upperValue ((point split endpoint 4096 2256+point split endpoint 4096 2257)/2)
    have hp : upperPayment 2256 = (247881203854:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2256+point split endpoint 4096 2257)/2 = (632902527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632902527:ℝ)/168755200)*ClassicalSixthBranch.v ((632902527:ℝ)/168755200)/ClassicalSixthBranch.r = (109412837984145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2256
  · change upperPayment 2257 ≤ upperValue ((point split endpoint 4096 2257+point split endpoint 4096 2258)/2)
    have hp : upperPayment 2257 = (247775772281:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2257+point split endpoint 4096 2258)/2 = (632927677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632927677:ℝ)/168755200)*ClassicalSixthBranch.v ((632927677:ℝ)/168755200)/ClassicalSixthBranch.r = (109391388997785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2257
  · change upperPayment 2258 ≤ upperValue ((point split endpoint 4096 2258+point split endpoint 4096 2259)/2)
    have hp : upperPayment 2258 = (247670313086:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2258+point split endpoint 4096 2259)/2 = (632952827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632952827:ℝ)/168755200)*ClassicalSixthBranch.v ((632952827:ℝ)/168755200)/ClassicalSixthBranch.r = (109369942035497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2258
  · change upperPayment 2259 ≤ upperValue ((point split endpoint 4096 2259+point split endpoint 4096 2260)/2)
    have hp : upperPayment 2259 = (247564826263:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2259+point split endpoint 4096 2260)/2 = (632977977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632977977:ℝ)/168755200)*ClassicalSixthBranch.v ((632977977:ℝ)/168755200)/ClassicalSixthBranch.r = (109348497097281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2259
  · change upperPayment 2260 ≤ upperValue ((point split endpoint 4096 2260+point split endpoint 4096 2261)/2)
    have hp : upperPayment 2260 = (247459311807:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2260+point split endpoint 4096 2261)/2 = (633003127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633003127:ℝ)/168755200)*ClassicalSixthBranch.v ((633003127:ℝ)/168755200)/ClassicalSixthBranch.r = (109327054183137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2260
  · change upperPayment 2261 ≤ upperValue ((point split endpoint 4096 2261+point split endpoint 4096 2262)/2)
    have hp : upperPayment 2261 = (247353769711:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2261+point split endpoint 4096 2262)/2 = (633028277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633028277:ℝ)/168755200)*ClassicalSixthBranch.v ((633028277:ℝ)/168755200)/ClassicalSixthBranch.r = (109305613293065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2261
  · change upperPayment 2262 ≤ upperValue ((point split endpoint 4096 2262+point split endpoint 4096 2263)/2)
    have hp : upperPayment 2262 = (247248199971:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2262+point split endpoint 4096 2263)/2 = (633053427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633053427:ℝ)/168755200)*ClassicalSixthBranch.v ((633053427:ℝ)/168755200)/ClassicalSixthBranch.r = (109284174427065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2262
  · change upperPayment 2263 ≤ upperValue ((point split endpoint 4096 2263+point split endpoint 4096 2264)/2)
    have hp : upperPayment 2263 = (247142602579:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2263+point split endpoint 4096 2264)/2 = (633078577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633078577:ℝ)/168755200)*ClassicalSixthBranch.v ((633078577:ℝ)/168755200)/ClassicalSixthBranch.r = (109262737585137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2263
  · change upperPayment 2264 ≤ upperValue ((point split endpoint 4096 2264+point split endpoint 4096 2265)/2)
    have hp : upperPayment 2264 = (247036977531:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2264+point split endpoint 4096 2265)/2 = (633103727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633103727:ℝ)/168755200)*ClassicalSixthBranch.v ((633103727:ℝ)/168755200)/ClassicalSixthBranch.r = (109241302767281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2264
  · change upperPayment 2265 ≤ upperValue ((point split endpoint 4096 2265+point split endpoint 4096 2266)/2)
    have hp : upperPayment 2265 = (246931324821:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2265+point split endpoint 4096 2266)/2 = (633128877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633128877:ℝ)/168755200)*ClassicalSixthBranch.v ((633128877:ℝ)/168755200)/ClassicalSixthBranch.r = (109219869973497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2265
  · change upperPayment 2266 ≤ upperValue ((point split endpoint 4096 2266+point split endpoint 4096 2267)/2)
    have hp : upperPayment 2266 = (246825644443:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2266+point split endpoint 4096 2267)/2 = (633154027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633154027:ℝ)/168755200)*ClassicalSixthBranch.v ((633154027:ℝ)/168755200)/ClassicalSixthBranch.r = (109198439203785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2266
  · change upperPayment 2267 ≤ upperValue ((point split endpoint 4096 2267+point split endpoint 4096 2268)/2)
    have hp : upperPayment 2267 = (246719936391:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2267+point split endpoint 4096 2268)/2 = (633179177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633179177:ℝ)/168755200)*ClassicalSixthBranch.v ((633179177:ℝ)/168755200)/ClassicalSixthBranch.r = (109177010458145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2267
  · change upperPayment 2268 ≤ upperValue ((point split endpoint 4096 2268+point split endpoint 4096 2269)/2)
    have hp : upperPayment 2268 = (246614200660:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2268+point split endpoint 4096 2269)/2 = (633204327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633204327:ℝ)/168755200)*ClassicalSixthBranch.v ((633204327:ℝ)/168755200)/ClassicalSixthBranch.r = (109155583736577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2268
  · change upperPayment 2269 ≤ upperValue ((point split endpoint 4096 2269+point split endpoint 4096 2270)/2)
    have hp : upperPayment 2269 = (246508437243:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2269+point split endpoint 4096 2270)/2 = (6147859:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((6147859:ℝ)/1638400)*ClassicalSixthBranch.v ((6147859:ℝ)/1638400)/ClassicalSixthBranch.r = (1059554942127:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2269
  · change upperPayment 2270 ≤ upperValue ((point split endpoint 4096 2270+point split endpoint 4096 2271)/2)
    have hp : upperPayment 2270 = (246402646135:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2270+point split endpoint 4096 2271)/2 = (633254627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633254627:ℝ)/168755200)*ClassicalSixthBranch.v ((633254627:ℝ)/168755200)/ClassicalSixthBranch.r = (109112736365657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2270
  · change upperPayment 2271 ≤ upperValue ((point split endpoint 4096 2271+point split endpoint 4096 2272)/2)
    have hp : upperPayment 2271 = (246296827331:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2271+point split endpoint 4096 2272)/2 = (633279777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633279777:ℝ)/168755200)*ClassicalSixthBranch.v ((633279777:ℝ)/168755200)/ClassicalSixthBranch.r = (109091315716305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2271
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_141
