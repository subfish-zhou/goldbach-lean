import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints021
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_021 (j : Fin 16) : lowerPayment (16*21+j.val) ≤
    lowerValue ((point 2 split 4096 (16*21+j.val)+point 2 split 4096 (16*21+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 336 ≤ lowerValue ((point 2 split 4096 336+point 2 split 4096 337)/2)
    have hp : lowerPayment 336 = (50867463815:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 336+point 2 split 4096 337)/2 = (357115563:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((357115563:ℝ)/168755200)/ClassicalSixthBranch.v ((357115563:ℝ)/168755200) = (787999125403:ℝ)/404423805336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_336
  · change lowerPayment 337 ≤ lowerValue ((point 2 split 4096 337+point 2 split 4096 338)/2)
    have hp : lowerPayment 337 = (51007747964:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 337+point 2 split 4096 338)/2 = (14286953:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((14286953:ℝ)/6750208)/ClassicalSixthBranch.v ((14286953:ℝ)/6750208) = (787921811729:ℝ)/404375797448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_337
  · change lowerPayment 338 ≤ lowerValue ((point 2 split 4096 338+point 2 split 4096 339)/2)
    have hp : lowerPayment 338 = (51147973989:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 338+point 2 split 4096 339)/2 = (357232087:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((357232087:ℝ)/168755200)/ClassicalSixthBranch.v ((357232087:ℝ)/168755200) = (157568899611:ℝ)/80865557912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_338
  · change lowerPayment 339 ≤ lowerValue ((point 2 split 4096 339+point 2 split 4096 340)/2)
    have hp : lowerPayment 339 = (51288141944:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 339+point 2 split 4096 340)/2 = (357290349:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((357290349:ℝ)/168755200)/ClassicalSixthBranch.v ((357290349:ℝ)/168755200) = (787767184381:ℝ)/404279781672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_339
  · change lowerPayment 340 ≤ lowerValue ((point 2 split 4096 340+point 2 split 4096 341)/2)
    have hp : lowerPayment 340 = (51428251880:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 340+point 2 split 4096 341)/2 = (357348611:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((357348611:ℝ)/168755200)/ClassicalSixthBranch.v ((357348611:ℝ)/168755200) = (787689870707:ℝ)/404231773784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_340
  · change lowerPayment 341 ≤ lowerValue ((point 2 split 4096 341+point 2 split 4096 342)/2)
    have hp : lowerPayment 341 = (51568303848:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 341+point 2 split 4096 342)/2 = (357406873:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((357406873:ℝ)/168755200)/ClassicalSixthBranch.v ((357406873:ℝ)/168755200) = (787612557033:ℝ)/404183765896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_341
  · change lowerPayment 342 ≤ lowerValue ((point 2 split 4096 342+point 2 split 4096 343)/2)
    have hp : lowerPayment 342 = (51708297900:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 342+point 2 split 4096 343)/2 = (71493027:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((71493027:ℝ)/33751040)/ClassicalSixthBranch.v ((71493027:ℝ)/33751040) = (787535243359:ℝ)/404135758008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_342
  · change lowerPayment 343 ≤ lowerValue ((point 2 split 4096 343+point 2 split 4096 344)/2)
    have hp : lowerPayment 343 = (51848234089:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 343+point 2 split 4096 344)/2 = (357523397:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((357523397:ℝ)/168755200)/ClassicalSixthBranch.v ((357523397:ℝ)/168755200) = (157491585937:ℝ)/80817550024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_343
  · change lowerPayment 344 ≤ lowerValue ((point 2 split 4096 344+point 2 split 4096 345)/2)
    have hp : lowerPayment 344 = (51988112465:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 344+point 2 split 4096 345)/2 = (357581659:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((357581659:ℝ)/168755200)/ClassicalSixthBranch.v ((357581659:ℝ)/168755200) = (787380616011:ℝ)/404039742232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_344
  · change lowerPayment 345 ≤ lowerValue ((point 2 split 4096 345+point 2 split 4096 346)/2)
    have hp : lowerPayment 345 = (52127933080:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 345+point 2 split 4096 346)/2 = (357639921:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((357639921:ℝ)/168755200)/ClassicalSixthBranch.v ((357639921:ℝ)/168755200) = (787303302337:ℝ)/403991734344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_345
  · change lowerPayment 346 ≤ lowerValue ((point 2 split 4096 346+point 2 split 4096 347)/2)
    have hp : lowerPayment 346 = (52267695985:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 346+point 2 split 4096 347)/2 = (357698183:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((357698183:ℝ)/168755200)/ClassicalSixthBranch.v ((357698183:ℝ)/168755200) = (787225988663:ℝ)/403943726456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_346
  · change lowerPayment 347 ≤ lowerValue ((point 2 split 4096 347+point 2 split 4096 348)/2)
    have hp : lowerPayment 347 = (52407401233:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 347+point 2 split 4096 348)/2 = (71551289:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((71551289:ℝ)/33751040)/ClassicalSixthBranch.v ((71551289:ℝ)/33751040) = (787148674989:ℝ)/403895718568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_347
  · change lowerPayment 348 ≤ lowerValue ((point 2 split 4096 348+point 2 split 4096 349)/2)
    have hp : lowerPayment 348 = (52547048874:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 348+point 2 split 4096 349)/2 = (357814707:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((357814707:ℝ)/168755200)/ClassicalSixthBranch.v ((357814707:ℝ)/168755200) = (157414272263:ℝ)/80769542136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_348
  · change lowerPayment 349 ≤ lowerValue ((point 2 split 4096 349+point 2 split 4096 350)/2)
    have hp : lowerPayment 349 = (52686638960:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 349+point 2 split 4096 350)/2 = (357872969:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((357872969:ℝ)/168755200)/ClassicalSixthBranch.v ((357872969:ℝ)/168755200) = (786994047641:ℝ)/403799702792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_349
  · change lowerPayment 350 ≤ lowerValue ((point 2 split 4096 350+point 2 split 4096 351)/2)
    have hp : lowerPayment 350 = (52826171541:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 350+point 2 split 4096 351)/2 = (357931231:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((357931231:ℝ)/168755200)/ClassicalSixthBranch.v ((357931231:ℝ)/168755200) = (786916733967:ℝ)/403751694904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_350
  · change lowerPayment 351 ≤ lowerValue ((point 2 split 4096 351+point 2 split 4096 352)/2)
    have hp : lowerPayment 351 = (52965646670:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 351+point 2 split 4096 352)/2 = (357989493:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((357989493:ℝ)/168755200)/ClassicalSixthBranch.v ((357989493:ℝ)/168755200) = (786839420293:ℝ)/403703687016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_351
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_021
