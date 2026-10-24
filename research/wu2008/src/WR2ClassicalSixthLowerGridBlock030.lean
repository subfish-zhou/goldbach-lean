import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints030
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_030 (j : Fin 16) : lowerPayment (16*30+j.val) ≤
    lowerValue ((point 2 split 4096 (16*30+j.val)+point 2 split 4096 (16*30+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 480 ≤ lowerValue ((point 2 split 4096 480+point 2 split 4096 481)/2)
    have hp : lowerPayment 480 = (70494397083:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 480+point 2 split 4096 481)/2 = (365505291:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((365505291:ℝ)/168755200)/ClassicalSixthBranch.v ((365505291:ℝ)/168755200) = (776865956347:ℝ)/397510669464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_480
  · change lowerPayment 481 ≤ lowerValue ((point 2 split 4096 481+point 2 split 4096 482)/2)
    have hp : lowerPayment 481 = (70626822369:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 481+point 2 split 4096 482)/2 = (365563553:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((365563553:ℝ)/168755200)/ClassicalSixthBranch.v ((365563553:ℝ)/168755200) = (776788642673:ℝ)/397462661576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_481
  · change lowerPayment 482 ≤ lowerValue ((point 2 split 4096 482+point 2 split 4096 483)/2)
    have hp : lowerPayment 482 = (70759196521:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 482+point 2 split 4096 483)/2 = (73124363:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((73124363:ℝ)/33751040)/ClassicalSixthBranch.v ((73124363:ℝ)/33751040) = (776711328999:ℝ)/397414653688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_482
  · change lowerPayment 483 ≤ lowerValue ((point 2 split 4096 483+point 2 split 4096 484)/2)
    have hp : lowerPayment 483 = (70891519583:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 483+point 2 split 4096 484)/2 = (365680077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((365680077:ℝ)/168755200)/ClassicalSixthBranch.v ((365680077:ℝ)/168755200) = (31065360613:ℝ)/15894665832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_483
  · change lowerPayment 484 ≤ lowerValue ((point 2 split 4096 484+point 2 split 4096 485)/2)
    have hp : lowerPayment 484 = (71023791602:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 484+point 2 split 4096 485)/2 = (365738339:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((365738339:ℝ)/168755200)/ClassicalSixthBranch.v ((365738339:ℝ)/168755200) = (776556701651:ℝ)/397318637912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_484
  · change lowerPayment 485 ≤ lowerValue ((point 2 split 4096 485+point 2 split 4096 486)/2)
    have hp : lowerPayment 485 = (71156012622:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 485+point 2 split 4096 486)/2 = (365796601:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((365796601:ℝ)/168755200)/ClassicalSixthBranch.v ((365796601:ℝ)/168755200) = (776479387977:ℝ)/397270630024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_485
  · change lowerPayment 486 ≤ lowerValue ((point 2 split 4096 486+point 2 split 4096 487)/2)
    have hp : lowerPayment 486 = (71288182688:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 486+point 2 split 4096 487)/2 = (365854863:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((365854863:ℝ)/168755200)/ClassicalSixthBranch.v ((365854863:ℝ)/168755200) = (776402074303:ℝ)/397222622136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_486
  · change lowerPayment 487 ≤ lowerValue ((point 2 split 4096 487+point 2 split 4096 488)/2)
    have hp : lowerPayment 487 = (71420301846:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 487+point 2 split 4096 488)/2 = (14636525:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((14636525:ℝ)/6750208)/ClassicalSixthBranch.v ((14636525:ℝ)/6750208) = (776324760629:ℝ)/397174614248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_487
  · change lowerPayment 488 ≤ lowerValue ((point 2 split 4096 488+point 2 split 4096 489)/2)
    have hp : lowerPayment 488 = (71552370141:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 488+point 2 split 4096 489)/2 = (365971387:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((365971387:ℝ)/168755200)/ClassicalSixthBranch.v ((365971387:ℝ)/168755200) = (155249489391:ℝ)/79425321272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_488
  · change lowerPayment 489 ≤ lowerValue ((point 2 split 4096 489+point 2 split 4096 490)/2)
    have hp : lowerPayment 489 = (71684387618:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 489+point 2 split 4096 490)/2 = (366029649:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((366029649:ℝ)/168755200)/ClassicalSixthBranch.v ((366029649:ℝ)/168755200) = (776170133281:ℝ)/397078598472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_489
  · change lowerPayment 490 ≤ lowerValue ((point 2 split 4096 490+point 2 split 4096 491)/2)
    have hp : lowerPayment 490 = (71816354322:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 490+point 2 split 4096 491)/2 = (366087911:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((366087911:ℝ)/168755200)/ClassicalSixthBranch.v ((366087911:ℝ)/168755200) = (776092819607:ℝ)/397030590584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_490
  · change lowerPayment 491 ≤ lowerValue ((point 2 split 4096 491+point 2 split 4096 492)/2)
    have hp : lowerPayment 491 = (71948270299:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 491+point 2 split 4096 492)/2 = (366146173:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((366146173:ℝ)/168755200)/ClassicalSixthBranch.v ((366146173:ℝ)/168755200) = (776015505933:ℝ)/396982582696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_491
  · change lowerPayment 492 ≤ lowerValue ((point 2 split 4096 492+point 2 split 4096 493)/2)
    have hp : lowerPayment 492 = (72080135592:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 492+point 2 split 4096 493)/2 = (73240887:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((73240887:ℝ)/33751040)/ClassicalSixthBranch.v ((73240887:ℝ)/33751040) = (775938192259:ℝ)/396934574808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_492
  · change lowerPayment 493 ≤ lowerValue ((point 2 split 4096 493+point 2 split 4096 494)/2)
    have hp : lowerPayment 493 = (72211950248:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 493+point 2 split 4096 494)/2 = (366262697:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((366262697:ℝ)/168755200)/ClassicalSixthBranch.v ((366262697:ℝ)/168755200) = (155172175717:ℝ)/79377313384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_493
  · change lowerPayment 494 ≤ lowerValue ((point 2 split 4096 494+point 2 split 4096 495)/2)
    have hp : lowerPayment 494 = (72343714311:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 494+point 2 split 4096 495)/2 = (366320959:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((366320959:ℝ)/168755200)/ClassicalSixthBranch.v ((366320959:ℝ)/168755200) = (775783564911:ℝ)/396838559032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_494
  · change lowerPayment 495 ≤ lowerValue ((point 2 split 4096 495+point 2 split 4096 496)/2)
    have hp : lowerPayment 495 = (72475427825:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 495+point 2 split 4096 496)/2 = (366379221:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((366379221:ℝ)/168755200)/ClassicalSixthBranch.v ((366379221:ℝ)/168755200) = (775706251237:ℝ)/396790551144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_495
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_030
