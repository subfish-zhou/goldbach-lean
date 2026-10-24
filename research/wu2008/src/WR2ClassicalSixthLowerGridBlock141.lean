import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints141
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_141 (j : Fin 16) : lowerPayment (16*141+j.val) ≤
    lowerValue ((point 2 split 4096 (16*141+j.val)+point 2 split 4096 (16*141+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2256 ≤ lowerValue ((point 2 split 4096 2256+point 2 split 4096 2257)/2)
    have hp : lowerPayment 2256 = (255740098525:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2256+point 2 split 4096 2257)/2 = (468978603:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((468978603:ℝ)/168755200)/ClassicalSixthBranch.v ((468978603:ℝ)/168755200) = (639556871323:ℝ)/312248660376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2256
  · change lowerPayment 2257 ≤ lowerValue ((point 2 split 4096 2257+point 2 split 4096 2258)/2)
    have hp : lowerPayment 2257 = (255829094847:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2257+point 2 split 4096 2258)/2 = (93807373:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((93807373:ℝ)/33751040)/ClassicalSixthBranch.v ((93807373:ℝ)/33751040) = (639479557649:ℝ)/312200652488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2257
  · change lowerPayment 2258 ≤ lowerValue ((point 2 split 4096 2258+point 2 split 4096 2259)/2)
    have hp : lowerPayment 2258 = (255918085096:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2258+point 2 split 4096 2259)/2 = (469095127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((469095127:ℝ)/168755200)/ClassicalSixthBranch.v ((469095127:ℝ)/168755200) = (25576089759:ℝ)/12486105784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2258
  · change lowerPayment 2259 ≤ lowerValue ((point 2 split 4096 2259+point 2 split 4096 2260)/2)
    have hp : lowerPayment 2259 = (256007069286:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2259+point 2 split 4096 2260)/2 = (469153389:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((469153389:ℝ)/168755200)/ClassicalSixthBranch.v ((469153389:ℝ)/168755200) = (639324930301:ℝ)/312104636712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2259
  · change lowerPayment 2260 ≤ lowerValue ((point 2 split 4096 2260+point 2 split 4096 2261)/2)
    have hp : lowerPayment 2260 = (256096047435:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2260+point 2 split 4096 2261)/2 = (469211651:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((469211651:ℝ)/168755200)/ClassicalSixthBranch.v ((469211651:ℝ)/168755200) = (639247616627:ℝ)/312056628824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2260
  · change lowerPayment 2261 ≤ lowerValue ((point 2 split 4096 2261+point 2 split 4096 2262)/2)
    have hp : lowerPayment 2261 = (256185019556:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2261+point 2 split 4096 2262)/2 = (469269913:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((469269913:ℝ)/168755200)/ClassicalSixthBranch.v ((469269913:ℝ)/168755200) = (639170302953:ℝ)/312008620936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2261
  · change lowerPayment 2262 ≤ lowerValue ((point 2 split 4096 2262+point 2 split 4096 2263)/2)
    have hp : lowerPayment 2262 = (256273985666:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2262+point 2 split 4096 2263)/2 = (18773127:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((18773127:ℝ)/6750208)/ClassicalSixthBranch.v ((18773127:ℝ)/6750208) = (639092989279:ℝ)/311960613048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2262
  · change lowerPayment 2263 ≤ lowerValue ((point 2 split 4096 2263+point 2 split 4096 2264)/2)
    have hp : lowerPayment 2263 = (256362945779:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2263+point 2 split 4096 2264)/2 = (469386437:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((469386437:ℝ)/168755200)/ClassicalSixthBranch.v ((469386437:ℝ)/168755200) = (127803135121:ℝ)/62382521032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2263
  · change lowerPayment 2264 ≤ lowerValue ((point 2 split 4096 2264+point 2 split 4096 2265)/2)
    have hp : lowerPayment 2264 = (256451899911:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2264+point 2 split 4096 2265)/2 = (469444699:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((469444699:ℝ)/168755200)/ClassicalSixthBranch.v ((469444699:ℝ)/168755200) = (638938361931:ℝ)/311864597272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2264
  · change lowerPayment 2265 ≤ lowerValue ((point 2 split 4096 2265+point 2 split 4096 2266)/2)
    have hp : lowerPayment 2265 = (256540848077:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2265+point 2 split 4096 2266)/2 = (469502961:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((469502961:ℝ)/168755200)/ClassicalSixthBranch.v ((469502961:ℝ)/168755200) = (638861048257:ℝ)/311816589384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2265
  · change lowerPayment 2266 ≤ lowerValue ((point 2 split 4096 2266+point 2 split 4096 2267)/2)
    have hp : lowerPayment 2266 = (256629790292:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2266+point 2 split 4096 2267)/2 = (469561223:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((469561223:ℝ)/168755200)/ClassicalSixthBranch.v ((469561223:ℝ)/168755200) = (638783734583:ℝ)/311768581496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2266
  · change lowerPayment 2267 ≤ lowerValue ((point 2 split 4096 2267+point 2 split 4096 2268)/2)
    have hp : lowerPayment 2267 = (256718726573:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2267+point 2 split 4096 2268)/2 = (93923897:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((93923897:ℝ)/33751040)/ClassicalSixthBranch.v ((93923897:ℝ)/33751040) = (638706420909:ℝ)/311720573608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2267
  · change lowerPayment 2268 ≤ lowerValue ((point 2 split 4096 2268+point 2 split 4096 2269)/2)
    have hp : lowerPayment 2268 = (256807656933:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2268+point 2 split 4096 2269)/2 = (469677747:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((469677747:ℝ)/168755200)/ClassicalSixthBranch.v ((469677747:ℝ)/168755200) = (127725821447:ℝ)/62334513144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2268
  · change lowerPayment 2269 ≤ lowerValue ((point 2 split 4096 2269+point 2 split 4096 2270)/2)
    have hp : lowerPayment 2269 = (256896581389:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2269+point 2 split 4096 2270)/2 = (469736009:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((469736009:ℝ)/168755200)/ClassicalSixthBranch.v ((469736009:ℝ)/168755200) = (638551793561:ℝ)/311624557832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2269
  · change lowerPayment 2270 ≤ lowerValue ((point 2 split 4096 2270+point 2 split 4096 2271)/2)
    have hp : lowerPayment 2270 = (256985499956:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2270+point 2 split 4096 2271)/2 = (469794271:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((469794271:ℝ)/168755200)/ClassicalSixthBranch.v ((469794271:ℝ)/168755200) = (638474479887:ℝ)/311576549944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2270
  · change lowerPayment 2271 ≤ lowerValue ((point 2 split 4096 2271+point 2 split 4096 2272)/2)
    have hp : lowerPayment 2271 = (257074412649:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2271+point 2 split 4096 2272)/2 = (469852533:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((469852533:ℝ)/168755200)/ClassicalSixthBranch.v ((469852533:ℝ)/168755200) = (638397166213:ℝ)/311528542056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2271
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_141
