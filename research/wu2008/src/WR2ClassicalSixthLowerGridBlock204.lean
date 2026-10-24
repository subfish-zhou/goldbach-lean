import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints204
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_204 (j : Fin 16) : lowerPayment (16*204+j.val) ≤
    lowerValue ((point 2 split 4096 (16*204+j.val)+point 2 split 4096 (16*204+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3264 ≤ lowerValue ((point 2 split 4096 3264+point 2 split 4096 3265)/2)
    have hp : lowerPayment 3264 = (344859183882:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3264+point 2 split 4096 3265)/2 = (527706699:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((527706699:ℝ)/168755200)/ClassicalSixthBranch.v ((527706699:ℝ)/168755200) = (561624687931:ℝ)/263856709272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3264
  · change lowerPayment 3265 ≤ lowerValue ((point 2 split 4096 3265+point 2 split 4096 3266)/2)
    have hp : lowerPayment 3265 = (344949435302:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3265+point 2 split 4096 3266)/2 = (527764961:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((527764961:ℝ)/168755200)/ClassicalSixthBranch.v ((527764961:ℝ)/168755200) = (561547374257:ℝ)/263808701384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3265
  · change lowerPayment 3266 ≤ lowerValue ((point 2 split 4096 3266+point 2 split 4096 3267)/2)
    have hp : lowerPayment 3266 = (345039695186:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3266+point 2 split 4096 3267)/2 = (527823223:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((527823223:ℝ)/168755200)/ClassicalSixthBranch.v ((527823223:ℝ)/168755200) = (561470060583:ℝ)/263760693496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3266
  · change lowerPayment 3267 ≤ lowerValue ((point 2 split 4096 3267+point 2 split 4096 3268)/2)
    have hp : lowerPayment 3267 = (345129963549:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3267+point 2 split 4096 3268)/2 = (105576297:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((105576297:ℝ)/33751040)/ClassicalSixthBranch.v ((105576297:ℝ)/33751040) = (561392746909:ℝ)/263712685608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3267
  · change lowerPayment 3268 ≤ lowerValue ((point 2 split 4096 3268+point 2 split 4096 3269)/2)
    have hp : lowerPayment 3268 = (345220240407:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3268+point 2 split 4096 3269)/2 = (527939747:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((527939747:ℝ)/168755200)/ClassicalSixthBranch.v ((527939747:ℝ)/168755200) = (112263086647:ℝ)/52732935544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3268
  · change lowerPayment 3269 ≤ lowerValue ((point 2 split 4096 3269+point 2 split 4096 3270)/2)
    have hp : lowerPayment 3269 = (345310525773:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3269+point 2 split 4096 3270)/2 = (527998009:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((527998009:ℝ)/168755200)/ClassicalSixthBranch.v ((527998009:ℝ)/168755200) = (561238119561:ℝ)/263616669832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3269
  · change lowerPayment 3270 ≤ lowerValue ((point 2 split 4096 3270+point 2 split 4096 3271)/2)
    have hp : lowerPayment 3270 = (345400819663:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3270+point 2 split 4096 3271)/2 = (528056271:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((528056271:ℝ)/168755200)/ClassicalSixthBranch.v ((528056271:ℝ)/168755200) = (561160805887:ℝ)/263568661944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3270
  · change lowerPayment 3271 ≤ lowerValue ((point 2 split 4096 3271+point 2 split 4096 3272)/2)
    have hp : lowerPayment 3271 = (345491122090:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3271+point 2 split 4096 3272)/2 = (528114533:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((528114533:ℝ)/168755200)/ClassicalSixthBranch.v ((528114533:ℝ)/168755200) = (561083492213:ℝ)/263520654056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3271
  · change lowerPayment 3272 ≤ lowerValue ((point 2 split 4096 3272+point 2 split 4096 3273)/2)
    have hp : lowerPayment 3272 = (345581433071:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3272+point 2 split 4096 3273)/2 = (105634559:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((105634559:ℝ)/33751040)/ClassicalSixthBranch.v ((105634559:ℝ)/33751040) = (561006178539:ℝ)/263472646168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3272
  · change lowerPayment 3273 ≤ lowerValue ((point 2 split 4096 3273+point 2 split 4096 3274)/2)
    have hp : lowerPayment 3273 = (345671752619:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3273+point 2 split 4096 3274)/2 = (528231057:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((528231057:ℝ)/168755200)/ClassicalSixthBranch.v ((528231057:ℝ)/168755200) = (112185772973:ℝ)/52684927656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3273
  · change lowerPayment 3274 ≤ lowerValue ((point 2 split 4096 3274+point 2 split 4096 3275)/2)
    have hp : lowerPayment 3274 = (345762080749:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3274+point 2 split 4096 3275)/2 = (528289319:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((528289319:ℝ)/168755200)/ClassicalSixthBranch.v ((528289319:ℝ)/168755200) = (560851551191:ℝ)/263376630392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3274
  · change lowerPayment 3275 ≤ lowerValue ((point 2 split 4096 3275+point 2 split 4096 3276)/2)
    have hp : lowerPayment 3275 = (345852417475:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3275+point 2 split 4096 3276)/2 = (528347581:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((528347581:ℝ)/168755200)/ClassicalSixthBranch.v ((528347581:ℝ)/168755200) = (560774237517:ℝ)/263328622504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3275
  · change lowerPayment 3276 ≤ lowerValue ((point 2 split 4096 3276+point 2 split 4096 3277)/2)
    have hp : lowerPayment 3276 = (345942762814:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3276+point 2 split 4096 3277)/2 = (528405843:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((528405843:ℝ)/168755200)/ClassicalSixthBranch.v ((528405843:ℝ)/168755200) = (560696923843:ℝ)/263280614616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3276
  · change lowerPayment 3277 ≤ lowerValue ((point 2 split 4096 3277+point 2 split 4096 3278)/2)
    have hp : lowerPayment 3277 = (346033116778:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3277+point 2 split 4096 3278)/2 = (105692821:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((105692821:ℝ)/33751040)/ClassicalSixthBranch.v ((105692821:ℝ)/33751040) = (560619610169:ℝ)/263232606728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3277
  · change lowerPayment 3278 ≤ lowerValue ((point 2 split 4096 3278+point 2 split 4096 3279)/2)
    have hp : lowerPayment 3278 = (346123479383:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3278+point 2 split 4096 3279)/2 = (528522367:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((528522367:ℝ)/168755200)/ClassicalSixthBranch.v ((528522367:ℝ)/168755200) = (112108459299:ℝ)/52636919768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3278
  · change lowerPayment 3279 ≤ lowerValue ((point 2 split 4096 3279+point 2 split 4096 3280)/2)
    have hp : lowerPayment 3279 = (346213850644:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3279+point 2 split 4096 3280)/2 = (528580629:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((528580629:ℝ)/168755200)/ClassicalSixthBranch.v ((528580629:ℝ)/168755200) = (560464982821:ℝ)/263136590952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3279
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_204
