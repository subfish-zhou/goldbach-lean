import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints212
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_212 (j : Fin 16) : lowerPayment (16*212+j.val) ≤
    lowerValue ((point 2 split 4096 (16*212+j.val)+point 2 split 4096 (16*212+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3392 ≤ lowerValue ((point 2 split 4096 3392+point 2 split 4096 3393)/2)
    have hp : lowerPayment 3392 = (356485203304:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3392+point 2 split 4096 3393)/2 = (107032847:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((107032847:ℝ)/33751040)/ClassicalSixthBranch.v ((107032847:ℝ)/33751040) = (551728537659:ℝ)/257711699608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3392
  · change lowerPayment 3393 ≤ lowerValue ((point 2 split 4096 3393+point 2 split 4096 3394)/2)
    have hp : lowerPayment 3393 = (356576658398:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3393+point 2 split 4096 3394)/2 = (535222497:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((535222497:ℝ)/168755200)/ClassicalSixthBranch.v ((535222497:ℝ)/168755200) = (110330244797:ℝ)/51532738344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3393
  · change lowerPayment 3394 ≤ lowerValue ((point 2 split 4096 3394+point 2 split 4096 3395)/2)
    have hp : lowerPayment 3394 = (356668123857:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3394+point 2 split 4096 3395)/2 = (535280759:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((535280759:ℝ)/168755200)/ClassicalSixthBranch.v ((535280759:ℝ)/168755200) = (551573910311:ℝ)/257615683832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3394
  · change lowerPayment 3395 ≤ lowerValue ((point 2 split 4096 3395+point 2 split 4096 3396)/2)
    have hp : lowerPayment 3395 = (356759599698:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3395+point 2 split 4096 3396)/2 = (535339021:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((535339021:ℝ)/168755200)/ClassicalSixthBranch.v ((535339021:ℝ)/168755200) = (551496596637:ℝ)/257567675944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3395
  · change lowerPayment 3396 ≤ lowerValue ((point 2 split 4096 3396+point 2 split 4096 3397)/2)
    have hp : lowerPayment 3396 = (356851085936:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3396+point 2 split 4096 3397)/2 = (535397283:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((535397283:ℝ)/168755200)/ClassicalSixthBranch.v ((535397283:ℝ)/168755200) = (551419282963:ℝ)/257519668056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3396
  · change lowerPayment 3397 ≤ lowerValue ((point 2 split 4096 3397+point 2 split 4096 3398)/2)
    have hp : lowerPayment 3397 = (356942582585:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3397+point 2 split 4096 3398)/2 = (107091109:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((107091109:ℝ)/33751040)/ClassicalSixthBranch.v ((107091109:ℝ)/33751040) = (551341969289:ℝ)/257471660168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3397
  · change lowerPayment 3398 ≤ lowerValue ((point 2 split 4096 3398+point 2 split 4096 3399)/2)
    have hp : lowerPayment 3398 = (357034089661:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3398+point 2 split 4096 3399)/2 = (535513807:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((535513807:ℝ)/168755200)/ClassicalSixthBranch.v ((535513807:ℝ)/168755200) = (110252931123:ℝ)/51484730456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3398
  · change lowerPayment 3399 ≤ lowerValue ((point 2 split 4096 3399+point 2 split 4096 3400)/2)
    have hp : lowerPayment 3399 = (357125607179:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3399+point 2 split 4096 3400)/2 = (535572069:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((535572069:ℝ)/168755200)/ClassicalSixthBranch.v ((535572069:ℝ)/168755200) = (551187341941:ℝ)/257375644392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3399
  · change lowerPayment 3400 ≤ lowerValue ((point 2 split 4096 3400+point 2 split 4096 3401)/2)
    have hp : lowerPayment 3400 = (357217135153:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3400+point 2 split 4096 3401)/2 = (535630331:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((535630331:ℝ)/168755200)/ClassicalSixthBranch.v ((535630331:ℝ)/168755200) = (551110028267:ℝ)/257327636504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3400
  · change lowerPayment 3401 ≤ lowerValue ((point 2 split 4096 3401+point 2 split 4096 3402)/2)
    have hp : lowerPayment 3401 = (357308673599:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3401+point 2 split 4096 3402)/2 = (535688593:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((535688593:ℝ)/168755200)/ClassicalSixthBranch.v ((535688593:ℝ)/168755200) = (551032714593:ℝ)/257279628616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3401
  · change lowerPayment 3402 ≤ lowerValue ((point 2 split 4096 3402+point 2 split 4096 3403)/2)
    have hp : lowerPayment 3402 = (357400222533:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3402+point 2 split 4096 3403)/2 = (107149371:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((107149371:ℝ)/33751040)/ClassicalSixthBranch.v ((107149371:ℝ)/33751040) = (550955400919:ℝ)/257231620728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3402
  · change lowerPayment 3403 ≤ lowerValue ((point 2 split 4096 3403+point 2 split 4096 3404)/2)
    have hp : lowerPayment 3403 = (357491781969:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3403+point 2 split 4096 3404)/2 = (535805117:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((535805117:ℝ)/168755200)/ClassicalSixthBranch.v ((535805117:ℝ)/168755200) = (110175617449:ℝ)/51436722568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3403
  · change lowerPayment 3404 ≤ lowerValue ((point 2 split 4096 3404+point 2 split 4096 3405)/2)
    have hp : lowerPayment 3404 = (357583351921:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3404+point 2 split 4096 3405)/2 = (535863379:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((535863379:ℝ)/168755200)/ClassicalSixthBranch.v ((535863379:ℝ)/168755200) = (550800773571:ℝ)/257135604952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3404
  · change lowerPayment 3405 ≤ lowerValue ((point 2 split 4096 3405+point 2 split 4096 3406)/2)
    have hp : lowerPayment 3405 = (357674932407:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3405+point 2 split 4096 3406)/2 = (535921641:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((535921641:ℝ)/168755200)/ClassicalSixthBranch.v ((535921641:ℝ)/168755200) = (550723459897:ℝ)/257087597064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3405
  · change lowerPayment 3406 ≤ lowerValue ((point 2 split 4096 3406+point 2 split 4096 3407)/2)
    have hp : lowerPayment 3406 = (357766523439:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3406+point 2 split 4096 3407)/2 = (535979903:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((535979903:ℝ)/168755200)/ClassicalSixthBranch.v ((535979903:ℝ)/168755200) = (550646146223:ℝ)/257039589176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3406
  · change lowerPayment 3407 ≤ lowerValue ((point 2 split 4096 3407+point 2 split 4096 3408)/2)
    have hp : lowerPayment 3407 = (357858125035:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3407+point 2 split 4096 3408)/2 = (107207633:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((107207633:ℝ)/33751040)/ClassicalSixthBranch.v ((107207633:ℝ)/33751040) = (550568832549:ℝ)/256991581288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3407
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_212
