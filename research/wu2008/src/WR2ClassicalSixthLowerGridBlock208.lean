import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints208
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_208 (j : Fin 16) : lowerPayment (16*208+j.val) ≤
    lowerValue ((point 2 split 4096 (16*208+j.val)+point 2 split 4096 (16*208+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3328 ≤ lowerValue ((point 2 split 4096 3328+point 2 split 4096 3329)/2)
    have hp : lowerPayment 3328 = (350652952275:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3328+point 2 split 4096 3329)/2 = (531435467:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((531435467:ℝ)/168755200)/ClassicalSixthBranch.v ((531435467:ℝ)/168755200) = (111335322559:ℝ)/52156840888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3328
  · change lowerPayment 3329 ≤ lowerValue ((point 2 split 4096 3329+point 2 split 4096 3330)/2)
    have hp : lowerPayment 3329 = (350743775114:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3329+point 2 split 4096 3330)/2 = (531493729:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((531493729:ℝ)/168755200)/ClassicalSixthBranch.v ((531493729:ℝ)/168755200) = (556599299121:ℝ)/260736196552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3329
  · change lowerPayment 3330 ≤ lowerValue ((point 2 split 4096 3330+point 2 split 4096 3331)/2)
    have hp : lowerPayment 3330 = (350834607362:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3330+point 2 split 4096 3331)/2 = (531551991:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((531551991:ℝ)/168755200)/ClassicalSixthBranch.v ((531551991:ℝ)/168755200) = (556521985447:ℝ)/260688188664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3330
  · change lowerPayment 3331 ≤ lowerValue ((point 2 split 4096 3331+point 2 split 4096 3332)/2)
    have hp : lowerPayment 3331 = (350925449033:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3331+point 2 split 4096 3332)/2 = (531610253:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((531610253:ℝ)/168755200)/ClassicalSixthBranch.v ((531610253:ℝ)/168755200) = (556444671773:ℝ)/260640180776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3331
  · change lowerPayment 3332 ≤ lowerValue ((point 2 split 4096 3332+point 2 split 4096 3333)/2)
    have hp : lowerPayment 3332 = (351016300143:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3332+point 2 split 4096 3333)/2 = (106333703:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((106333703:ℝ)/33751040)/ClassicalSixthBranch.v ((106333703:ℝ)/33751040) = (556367358099:ℝ)/260592172888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3332
  · change lowerPayment 3333 ≤ lowerValue ((point 2 split 4096 3333+point 2 split 4096 3334)/2)
    have hp : lowerPayment 3333 = (351107160707:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3333+point 2 split 4096 3334)/2 = (531726777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((531726777:ℝ)/168755200)/ClassicalSixthBranch.v ((531726777:ℝ)/168755200) = (22251601777:ℝ)/10421766600 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3333
  · change lowerPayment 3334 ≤ lowerValue ((point 2 split 4096 3334+point 2 split 4096 3335)/2)
    have hp : lowerPayment 3334 = (351198030739:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3334+point 2 split 4096 3335)/2 = (531785039:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((531785039:ℝ)/168755200)/ClassicalSixthBranch.v ((531785039:ℝ)/168755200) = (556212730751:ℝ)/260496157112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3334
  · change lowerPayment 3335 ≤ lowerValue ((point 2 split 4096 3335+point 2 split 4096 3336)/2)
    have hp : lowerPayment 3335 = (351288910254:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3335+point 2 split 4096 3336)/2 = (531843301:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((531843301:ℝ)/168755200)/ClassicalSixthBranch.v ((531843301:ℝ)/168755200) = (556135417077:ℝ)/260448149224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3335
  · change lowerPayment 3336 ≤ lowerValue ((point 2 split 4096 3336+point 2 split 4096 3337)/2)
    have hp : lowerPayment 3336 = (351379799268:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3336+point 2 split 4096 3337)/2 = (531901563:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((531901563:ℝ)/168755200)/ClassicalSixthBranch.v ((531901563:ℝ)/168755200) = (556058103403:ℝ)/260400141336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3336
  · change lowerPayment 3337 ≤ lowerValue ((point 2 split 4096 3337+point 2 split 4096 3338)/2)
    have hp : lowerPayment 3337 = (351470697794:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3337+point 2 split 4096 3338)/2 = (21278393:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((21278393:ℝ)/6750208)/ClassicalSixthBranch.v ((21278393:ℝ)/6750208) = (555980789729:ℝ)/260352133448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3337
  · change lowerPayment 3338 ≤ lowerValue ((point 2 split 4096 3338+point 2 split 4096 3339)/2)
    have hp : lowerPayment 3338 = (351561605848:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3338+point 2 split 4096 3339)/2 = (532018087:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((532018087:ℝ)/168755200)/ClassicalSixthBranch.v ((532018087:ℝ)/168755200) = (111180695211:ℝ)/52060825112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3338
  · change lowerPayment 3339 ≤ lowerValue ((point 2 split 4096 3339+point 2 split 4096 3340)/2)
    have hp : lowerPayment 3339 = (351652523445:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3339+point 2 split 4096 3340)/2 = (532076349:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((532076349:ℝ)/168755200)/ClassicalSixthBranch.v ((532076349:ℝ)/168755200) = (555826162381:ℝ)/260256117672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3339
  · change lowerPayment 3340 ≤ lowerValue ((point 2 split 4096 3340+point 2 split 4096 3341)/2)
    have hp : lowerPayment 3340 = (351743450600:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3340+point 2 split 4096 3341)/2 = (532134611:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((532134611:ℝ)/168755200)/ClassicalSixthBranch.v ((532134611:ℝ)/168755200) = (555748848707:ℝ)/260208109784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3340
  · change lowerPayment 3341 ≤ lowerValue ((point 2 split 4096 3341+point 2 split 4096 3342)/2)
    have hp : lowerPayment 3341 = (351834387327:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3341+point 2 split 4096 3342)/2 = (532192873:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((532192873:ℝ)/168755200)/ClassicalSixthBranch.v ((532192873:ℝ)/168755200) = (555671535033:ℝ)/260160101896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3341
  · change lowerPayment 3342 ≤ lowerValue ((point 2 split 4096 3342+point 2 split 4096 3343)/2)
    have hp : lowerPayment 3342 = (351925333641:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3342+point 2 split 4096 3343)/2 = (106450227:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((106450227:ℝ)/33751040)/ClassicalSixthBranch.v ((106450227:ℝ)/33751040) = (555594221359:ℝ)/260112094008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3342
  · change lowerPayment 3343 ≤ lowerValue ((point 2 split 4096 3343+point 2 split 4096 3344)/2)
    have hp : lowerPayment 3343 = (352016289558:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3343+point 2 split 4096 3344)/2 = (532309397:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((532309397:ℝ)/168755200)/ClassicalSixthBranch.v ((532309397:ℝ)/168755200) = (111103381537:ℝ)/52012817224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3343
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_208
