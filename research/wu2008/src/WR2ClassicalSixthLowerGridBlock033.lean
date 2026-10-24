import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints033
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_033 (j : Fin 16) : lowerPayment (16*33+j.val) ≤
    lowerValue ((point 2 split 4096 (16*33+j.val)+point 2 split 4096 (16*33+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 528 ≤ lowerValue ((point 2 split 4096 528+point 2 split 4096 529)/2)
    have hp : lowerPayment 528 = (76793907775:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 528+point 2 split 4096 529)/2 = (368301867:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((368301867:ℝ)/168755200)/ClassicalSixthBranch.v ((368301867:ℝ)/168755200) = (154630979999:ℝ)/79041258168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_528
  · change lowerPayment 529 ≤ lowerValue ((point 2 split 4096 529+point 2 split 4096 530)/2)
    have hp : lowerPayment 529 = (76923929078:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 529+point 2 split 4096 530)/2 = (368360129:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((368360129:ℝ)/168755200)/ClassicalSixthBranch.v ((368360129:ℝ)/168755200) = (773077586321:ℝ)/395158282952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_529
  · change lowerPayment 530 ≤ lowerValue ((point 2 split 4096 530+point 2 split 4096 531)/2)
    have hp : lowerPayment 530 = (77053901379:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 530+point 2 split 4096 531)/2 = (368418391:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((368418391:ℝ)/168755200)/ClassicalSixthBranch.v ((368418391:ℝ)/168755200) = (773000272647:ℝ)/395110275064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_530
  · change lowerPayment 531 ≤ lowerValue ((point 2 split 4096 531+point 2 split 4096 532)/2)
    have hp : lowerPayment 531 = (77183824721:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 531+point 2 split 4096 532)/2 = (368476653:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((368476653:ℝ)/168755200)/ClassicalSixthBranch.v ((368476653:ℝ)/168755200) = (772922958973:ℝ)/395062267176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_531
  · change lowerPayment 532 ≤ lowerValue ((point 2 split 4096 532+point 2 split 4096 533)/2)
    have hp : lowerPayment 532 = (77313699148:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 532+point 2 split 4096 533)/2 = (73706983:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((73706983:ℝ)/33751040)/ClassicalSixthBranch.v ((73706983:ℝ)/33751040) = (772845645299:ℝ)/395014259288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_532
  · change lowerPayment 533 ≤ lowerValue ((point 2 split 4096 533+point 2 split 4096 534)/2)
    have hp : lowerPayment 533 = (77443524703:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 533+point 2 split 4096 534)/2 = (368593177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((368593177:ℝ)/168755200)/ClassicalSixthBranch.v ((368593177:ℝ)/168755200) = (30910733265:ℝ)/15798650056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_533
  · change lowerPayment 534 ≤ lowerValue ((point 2 split 4096 534+point 2 split 4096 535)/2)
    have hp : lowerPayment 534 = (77573301429:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 534+point 2 split 4096 535)/2 = (368651439:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((368651439:ℝ)/168755200)/ClassicalSixthBranch.v ((368651439:ℝ)/168755200) = (772691017951:ℝ)/394918243512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_534
  · change lowerPayment 535 ≤ lowerValue ((point 2 split 4096 535+point 2 split 4096 536)/2)
    have hp : lowerPayment 535 = (77703029371:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 535+point 2 split 4096 536)/2 = (368709701:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((368709701:ℝ)/168755200)/ClassicalSixthBranch.v ((368709701:ℝ)/168755200) = (772613704277:ℝ)/394870235624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_535
  · change lowerPayment 536 ≤ lowerValue ((point 2 split 4096 536+point 2 split 4096 537)/2)
    have hp : lowerPayment 536 = (77832708570:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 536+point 2 split 4096 537)/2 = (368767963:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((368767963:ℝ)/168755200)/ClassicalSixthBranch.v ((368767963:ℝ)/168755200) = (772536390603:ℝ)/394822227736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_536
  · change lowerPayment 537 ≤ lowerValue ((point 2 split 4096 537+point 2 split 4096 538)/2)
    have hp : lowerPayment 537 = (77962339071:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 537+point 2 split 4096 538)/2 = (14753049:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((14753049:ℝ)/6750208)/ClassicalSixthBranch.v ((14753049:ℝ)/6750208) = (772459076929:ℝ)/394774219848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_537
  · change lowerPayment 538 ≤ lowerValue ((point 2 split 4096 538+point 2 split 4096 539)/2)
    have hp : lowerPayment 538 = (78091920916:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 538+point 2 split 4096 539)/2 = (368884487:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((368884487:ℝ)/168755200)/ClassicalSixthBranch.v ((368884487:ℝ)/168755200) = (154476352651:ℝ)/78945242392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_538
  · change lowerPayment 539 ≤ lowerValue ((point 2 split 4096 539+point 2 split 4096 540)/2)
    have hp : lowerPayment 539 = (78221454149:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 539+point 2 split 4096 540)/2 = (368942749:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((368942749:ℝ)/168755200)/ClassicalSixthBranch.v ((368942749:ℝ)/168755200) = (772304449581:ℝ)/394678204072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_539
  · change lowerPayment 540 ≤ lowerValue ((point 2 split 4096 540+point 2 split 4096 541)/2)
    have hp : lowerPayment 540 = (78350938813:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 540+point 2 split 4096 541)/2 = (369001011:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((369001011:ℝ)/168755200)/ClassicalSixthBranch.v ((369001011:ℝ)/168755200) = (772227135907:ℝ)/394630196184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_540
  · change lowerPayment 541 ≤ lowerValue ((point 2 split 4096 541+point 2 split 4096 542)/2)
    have hp : lowerPayment 541 = (78480374951:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 541+point 2 split 4096 542)/2 = (369059273:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((369059273:ℝ)/168755200)/ClassicalSixthBranch.v ((369059273:ℝ)/168755200) = (772149822233:ℝ)/394582188296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_541
  · change lowerPayment 542 ≤ lowerValue ((point 2 split 4096 542+point 2 split 4096 543)/2)
    have hp : lowerPayment 542 = (78609762605:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 542+point 2 split 4096 543)/2 = (73823507:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((73823507:ℝ)/33751040)/ClassicalSixthBranch.v ((73823507:ℝ)/33751040) = (772072508559:ℝ)/394534180408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_542
  · change lowerPayment 543 ≤ lowerValue ((point 2 split 4096 543+point 2 split 4096 544)/2)
    have hp : lowerPayment 543 = (78739101820:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 543+point 2 split 4096 544)/2 = (369175797:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((369175797:ℝ)/168755200)/ClassicalSixthBranch.v ((369175797:ℝ)/168755200) = (154399038977:ℝ)/78897234504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_543
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_033
