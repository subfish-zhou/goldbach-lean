import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints149
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_149 (j : Fin 16) : lowerPayment (16*149+j.val) ≤
    lowerValue ((point 2 split 4096 (16*149+j.val)+point 2 split 4096 (16*149+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2384 ≤ lowerValue ((point 2 split 4096 2384+point 2 split 4096 2385)/2)
    have hp : lowerPayment 2384 = (267087459920:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2384+point 2 split 4096 2385)/2 = (476436139:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((476436139:ℝ)/168755200)/ClassicalSixthBranch.v ((476436139:ℝ)/168755200) = (629660721051:ℝ)/306103650712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2384
  · change lowerPayment 2385 ≤ lowerValue ((point 2 split 4096 2385+point 2 split 4096 2386)/2)
    have hp : lowerPayment 2385 = (267175802225:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2385+point 2 split 4096 2386)/2 = (476494401:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((476494401:ℝ)/168755200)/ClassicalSixthBranch.v ((476494401:ℝ)/168755200) = (629583407377:ℝ)/306055642824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2385
  · change lowerPayment 2386 ≤ lowerValue ((point 2 split 4096 2386+point 2 split 4096 2387)/2)
    have hp : lowerPayment 2386 = (267264140388:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2386+point 2 split 4096 2387)/2 = (476552663:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((476552663:ℝ)/168755200)/ClassicalSixthBranch.v ((476552663:ℝ)/168755200) = (629506093703:ℝ)/306007634936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2386
  · change lowerPayment 2387 ≤ lowerValue ((point 2 split 4096 2387+point 2 split 4096 2388)/2)
    have hp : lowerPayment 2387 = (267352474426:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2387+point 2 split 4096 2388)/2 = (19064437:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((19064437:ℝ)/6750208)/ClassicalSixthBranch.v ((19064437:ℝ)/6750208) = (629428780029:ℝ)/305959627048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2387
  · change lowerPayment 2388 ≤ lowerValue ((point 2 split 4096 2388+point 2 split 4096 2389)/2)
    have hp : lowerPayment 2388 = (267440804352:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2388+point 2 split 4096 2389)/2 = (476669187:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((476669187:ℝ)/168755200)/ClassicalSixthBranch.v ((476669187:ℝ)/168755200) = (125870293271:ℝ)/61182323832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2388
  · change lowerPayment 2389 ≤ lowerValue ((point 2 split 4096 2389+point 2 split 4096 2390)/2)
    have hp : lowerPayment 2389 = (267529130182:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2389+point 2 split 4096 2390)/2 = (476727449:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((476727449:ℝ)/168755200)/ClassicalSixthBranch.v ((476727449:ℝ)/168755200) = (629274152681:ℝ)/305863611272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2389
  · change lowerPayment 2390 ≤ lowerValue ((point 2 split 4096 2390+point 2 split 4096 2391)/2)
    have hp : lowerPayment 2390 = (267617451930:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2390+point 2 split 4096 2391)/2 = (476785711:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((476785711:ℝ)/168755200)/ClassicalSixthBranch.v ((476785711:ℝ)/168755200) = (629196839007:ℝ)/305815603384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2390
  · change lowerPayment 2391 ≤ lowerValue ((point 2 split 4096 2391+point 2 split 4096 2392)/2)
    have hp : lowerPayment 2391 = (267705769612:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2391+point 2 split 4096 2392)/2 = (476843973:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((476843973:ℝ)/168755200)/ClassicalSixthBranch.v ((476843973:ℝ)/168755200) = (629119525333:ℝ)/305767595496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2391
  · change lowerPayment 2392 ≤ lowerValue ((point 2 split 4096 2392+point 2 split 4096 2393)/2)
    have hp : lowerPayment 2392 = (267794083241:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2392+point 2 split 4096 2393)/2 = (95380447:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((95380447:ℝ)/33751040)/ClassicalSixthBranch.v ((95380447:ℝ)/33751040) = (629042211659:ℝ)/305719587608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2392
  · change lowerPayment 2393 ≤ lowerValue ((point 2 split 4096 2393+point 2 split 4096 2394)/2)
    have hp : lowerPayment 2393 = (267882392834:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2393+point 2 split 4096 2394)/2 = (476960497:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((476960497:ℝ)/168755200)/ClassicalSixthBranch.v ((476960497:ℝ)/168755200) = (125792979597:ℝ)/61134315944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2393
  · change lowerPayment 2394 ≤ lowerValue ((point 2 split 4096 2394+point 2 split 4096 2395)/2)
    have hp : lowerPayment 2394 = (267970698404:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2394+point 2 split 4096 2395)/2 = (477018759:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((477018759:ℝ)/168755200)/ClassicalSixthBranch.v ((477018759:ℝ)/168755200) = (628887584311:ℝ)/305623571832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2394
  · change lowerPayment 2395 ≤ lowerValue ((point 2 split 4096 2395+point 2 split 4096 2396)/2)
    have hp : lowerPayment 2395 = (268058999967:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2395+point 2 split 4096 2396)/2 = (477077021:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((477077021:ℝ)/168755200)/ClassicalSixthBranch.v ((477077021:ℝ)/168755200) = (628810270637:ℝ)/305575563944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2395
  · change lowerPayment 2396 ≤ lowerValue ((point 2 split 4096 2396+point 2 split 4096 2397)/2)
    have hp : lowerPayment 2396 = (268147297537:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2396+point 2 split 4096 2397)/2 = (477135283:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((477135283:ℝ)/168755200)/ClassicalSixthBranch.v ((477135283:ℝ)/168755200) = (628732956963:ℝ)/305527556056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2396
  · change lowerPayment 2397 ≤ lowerValue ((point 2 split 4096 2397+point 2 split 4096 2398)/2)
    have hp : lowerPayment 2397 = (268235591129:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2397+point 2 split 4096 2398)/2 = (95438709:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((95438709:ℝ)/33751040)/ClassicalSixthBranch.v ((95438709:ℝ)/33751040) = (628655643289:ℝ)/305479548168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2397
  · change lowerPayment 2398 ≤ lowerValue ((point 2 split 4096 2398+point 2 split 4096 2399)/2)
    have hp : lowerPayment 2398 = (268323880759:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2398+point 2 split 4096 2399)/2 = (477251807:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((477251807:ℝ)/168755200)/ClassicalSixthBranch.v ((477251807:ℝ)/168755200) = (125715665923:ℝ)/61086308056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2398
  · change lowerPayment 2399 ≤ lowerValue ((point 2 split 4096 2399+point 2 split 4096 2400)/2)
    have hp : lowerPayment 2399 = (268412166440:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2399+point 2 split 4096 2400)/2 = (477310069:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((477310069:ℝ)/168755200)/ClassicalSixthBranch.v ((477310069:ℝ)/168755200) = (628501015941:ℝ)/305383532392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2399
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_149
