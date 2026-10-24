import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints142
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_142 (j : Fin 16) : lowerPayment (16*142+j.val) ≤
    lowerValue ((point 2 split 4096 (16*142+j.val)+point 2 split 4096 (16*142+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2272 ≤ lowerValue ((point 2 split 4096 2272+point 2 split 4096 2273)/2)
    have hp : lowerPayment 2272 = (257163319483:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2272+point 2 split 4096 2273)/2 = (93982159:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((93982159:ℝ)/33751040)/ClassicalSixthBranch.v ((93982159:ℝ)/33751040) = (638319852539:ℝ)/311480534168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2272
  · change lowerPayment 2273 ≤ lowerValue ((point 2 split 4096 2273+point 2 split 4096 2274)/2)
    have hp : lowerPayment 2273 = (257252220473:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2273+point 2 split 4096 2274)/2 = (469969057:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((469969057:ℝ)/168755200)/ClassicalSixthBranch.v ((469969057:ℝ)/168755200) = (127648507773:ℝ)/62286505256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2273
  · change lowerPayment 2274 ≤ lowerValue ((point 2 split 4096 2274+point 2 split 4096 2275)/2)
    have hp : lowerPayment 2274 = (257341115636:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2274+point 2 split 4096 2275)/2 = (470027319:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((470027319:ℝ)/168755200)/ClassicalSixthBranch.v ((470027319:ℝ)/168755200) = (638165225191:ℝ)/311384518392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2274
  · change lowerPayment 2275 ≤ lowerValue ((point 2 split 4096 2275+point 2 split 4096 2276)/2)
    have hp : lowerPayment 2275 = (257430004986:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2275+point 2 split 4096 2276)/2 = (470085581:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((470085581:ℝ)/168755200)/ClassicalSixthBranch.v ((470085581:ℝ)/168755200) = (638087911517:ℝ)/311336510504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2275
  · change lowerPayment 2276 ≤ lowerValue ((point 2 split 4096 2276+point 2 split 4096 2277)/2)
    have hp : lowerPayment 2276 = (257518888538:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2276+point 2 split 4096 2277)/2 = (470143843:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((470143843:ℝ)/168755200)/ClassicalSixthBranch.v ((470143843:ℝ)/168755200) = (638010597843:ℝ)/311288502616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2276
  · change lowerPayment 2277 ≤ lowerValue ((point 2 split 4096 2277+point 2 split 4096 2278)/2)
    have hp : lowerPayment 2277 = (257607766307:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2277+point 2 split 4096 2278)/2 = (94040421:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((94040421:ℝ)/33751040)/ClassicalSixthBranch.v ((94040421:ℝ)/33751040) = (637933284169:ℝ)/311240494728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2277
  · change lowerPayment 2278 ≤ lowerValue ((point 2 split 4096 2278+point 2 split 4096 2279)/2)
    have hp : lowerPayment 2278 = (257696638310:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2278+point 2 split 4096 2279)/2 = (470260367:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((470260367:ℝ)/168755200)/ClassicalSixthBranch.v ((470260367:ℝ)/168755200) = (127571194099:ℝ)/62238497368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2278
  · change lowerPayment 2279 ≤ lowerValue ((point 2 split 4096 2279+point 2 split 4096 2280)/2)
    have hp : lowerPayment 2279 = (257785504561:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2279+point 2 split 4096 2280)/2 = (470318629:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((470318629:ℝ)/168755200)/ClassicalSixthBranch.v ((470318629:ℝ)/168755200) = (637778656821:ℝ)/311144478952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2279
  · change lowerPayment 2280 ≤ lowerValue ((point 2 split 4096 2280+point 2 split 4096 2281)/2)
    have hp : lowerPayment 2280 = (257874365075:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2280+point 2 split 4096 2281)/2 = (470376891:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((470376891:ℝ)/168755200)/ClassicalSixthBranch.v ((470376891:ℝ)/168755200) = (637701343147:ℝ)/311096471064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2280
  · change lowerPayment 2281 ≤ lowerValue ((point 2 split 4096 2281+point 2 split 4096 2282)/2)
    have hp : lowerPayment 2281 = (257963219868:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2281+point 2 split 4096 2282)/2 = (470435153:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((470435153:ℝ)/168755200)/ClassicalSixthBranch.v ((470435153:ℝ)/168755200) = (637624029473:ℝ)/311048463176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2281
  · change lowerPayment 2282 ≤ lowerValue ((point 2 split 4096 2282+point 2 split 4096 2283)/2)
    have hp : lowerPayment 2282 = (258052068955:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2282+point 2 split 4096 2283)/2 = (94098683:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((94098683:ℝ)/33751040)/ClassicalSixthBranch.v ((94098683:ℝ)/33751040) = (637546715799:ℝ)/311000455288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2282
  · change lowerPayment 2283 ≤ lowerValue ((point 2 split 4096 2283+point 2 split 4096 2284)/2)
    have hp : lowerPayment 2283 = (258140912351:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2283+point 2 split 4096 2284)/2 = (470551677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((470551677:ℝ)/168755200)/ClassicalSixthBranch.v ((470551677:ℝ)/168755200) = (25498776085:ℝ)/12438097896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2283
  · change lowerPayment 2284 ≤ lowerValue ((point 2 split 4096 2284+point 2 split 4096 2285)/2)
    have hp : lowerPayment 2284 = (258229750072:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2284+point 2 split 4096 2285)/2 = (470609939:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((470609939:ℝ)/168755200)/ClassicalSixthBranch.v ((470609939:ℝ)/168755200) = (637392088451:ℝ)/310904439512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2284
  · change lowerPayment 2285 ≤ lowerValue ((point 2 split 4096 2285+point 2 split 4096 2286)/2)
    have hp : lowerPayment 2285 = (258318582132:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2285+point 2 split 4096 2286)/2 = (470668201:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((470668201:ℝ)/168755200)/ClassicalSixthBranch.v ((470668201:ℝ)/168755200) = (637314774777:ℝ)/310856431624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2285
  · change lowerPayment 2286 ≤ lowerValue ((point 2 split 4096 2286+point 2 split 4096 2287)/2)
    have hp : lowerPayment 2286 = (258407408547:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2286+point 2 split 4096 2287)/2 = (470726463:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((470726463:ℝ)/168755200)/ClassicalSixthBranch.v ((470726463:ℝ)/168755200) = (637237461103:ℝ)/310808423736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2286
  · change lowerPayment 2287 ≤ lowerValue ((point 2 split 4096 2287+point 2 split 4096 2288)/2)
    have hp : lowerPayment 2287 = (258496229333:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2287+point 2 split 4096 2288)/2 = (18831389:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((18831389:ℝ)/6750208)/ClassicalSixthBranch.v ((18831389:ℝ)/6750208) = (637160147429:ℝ)/310760415848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2287
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_142
