import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints040
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_040 (j : Fin 16) : lowerPayment (16*40+j.val) ≤
    lowerValue ((point 2 split 4096 (16*40+j.val)+point 2 split 4096 (16*40+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 640 ≤ lowerValue ((point 2 split 4096 640+point 2 split 4096 641)/2)
    have hp : lowerPayment 640 = (91061369883:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 640+point 2 split 4096 641)/2 = (374827211:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((374827211:ℝ)/168755200)/ClassicalSixthBranch.v ((374827211:ℝ)/168755200) = (764495768507:ℝ)/389829407384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_640
  · change lowerPayment 641 ≤ lowerValue ((point 2 split 4096 641+point 2 split 4096 642)/2)
    have hp : lowerPayment 641 = (91186164629:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 641+point 2 split 4096 642)/2 = (374885473:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((374885473:ℝ)/168755200)/ClassicalSixthBranch.v ((374885473:ℝ)/168755200) = (764418454833:ℝ)/389781399496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_641
  · change lowerPayment 642 ≤ lowerValue ((point 2 split 4096 642+point 2 split 4096 643)/2)
    have hp : lowerPayment 642 = (91310915011:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 642+point 2 split 4096 643)/2 = (74988747:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((74988747:ℝ)/33751040)/ClassicalSixthBranch.v ((74988747:ℝ)/33751040) = (764341141159:ℝ)/389733391608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_642
  · change lowerPayment 643 ≤ lowerValue ((point 2 split 4096 643+point 2 split 4096 644)/2)
    have hp : lowerPayment 643 = (91435621070:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 643+point 2 split 4096 644)/2 = (375001997:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((375001997:ℝ)/168755200)/ClassicalSixthBranch.v ((375001997:ℝ)/168755200) = (152852765497:ℝ)/77937076744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_643
  · change lowerPayment 644 ≤ lowerValue ((point 2 split 4096 644+point 2 split 4096 645)/2)
    have hp : lowerPayment 644 = (91560282844:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 644+point 2 split 4096 645)/2 = (375060259:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((375060259:ℝ)/168755200)/ClassicalSixthBranch.v ((375060259:ℝ)/168755200) = (764186513811:ℝ)/389637375832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_644
  · change lowerPayment 645 ≤ lowerValue ((point 2 split 4096 645+point 2 split 4096 646)/2)
    have hp : lowerPayment 645 = (91684900374:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 645+point 2 split 4096 646)/2 = (375118521:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((375118521:ℝ)/168755200)/ClassicalSixthBranch.v ((375118521:ℝ)/168755200) = (764109200137:ℝ)/389589367944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_645
  · change lowerPayment 646 ≤ lowerValue ((point 2 split 4096 646+point 2 split 4096 647)/2)
    have hp : lowerPayment 646 = (91809473698:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 646+point 2 split 4096 647)/2 = (375176783:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((375176783:ℝ)/168755200)/ClassicalSixthBranch.v ((375176783:ℝ)/168755200) = (764031886463:ℝ)/389541360056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_646
  · change lowerPayment 647 ≤ lowerValue ((point 2 split 4096 647+point 2 split 4096 648)/2)
    have hp : lowerPayment 647 = (91934002855:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 647+point 2 split 4096 648)/2 = (75047009:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((75047009:ℝ)/33751040)/ClassicalSixthBranch.v ((75047009:ℝ)/33751040) = (763954572789:ℝ)/389493352168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_647
  · change lowerPayment 648 ≤ lowerValue ((point 2 split 4096 648+point 2 split 4096 649)/2)
    have hp : lowerPayment 648 = (92058487885:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 648+point 2 split 4096 649)/2 = (375293307:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((375293307:ℝ)/168755200)/ClassicalSixthBranch.v ((375293307:ℝ)/168755200) = (152775451823:ℝ)/77889068856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_648
  · change lowerPayment 649 ≤ lowerValue ((point 2 split 4096 649+point 2 split 4096 650)/2)
    have hp : lowerPayment 649 = (92182928828:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 649+point 2 split 4096 650)/2 = (375351569:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((375351569:ℝ)/168755200)/ClassicalSixthBranch.v ((375351569:ℝ)/168755200) = (763799945441:ℝ)/389397336392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_649
  · change lowerPayment 650 ≤ lowerValue ((point 2 split 4096 650+point 2 split 4096 651)/2)
    have hp : lowerPayment 650 = (92307325722:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 650+point 2 split 4096 651)/2 = (375409831:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((375409831:ℝ)/168755200)/ClassicalSixthBranch.v ((375409831:ℝ)/168755200) = (763722631767:ℝ)/389349328504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_650
  · change lowerPayment 651 ≤ lowerValue ((point 2 split 4096 651+point 2 split 4096 652)/2)
    have hp : lowerPayment 651 = (92431678606:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 651+point 2 split 4096 652)/2 = (375468093:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((375468093:ℝ)/168755200)/ClassicalSixthBranch.v ((375468093:ℝ)/168755200) = (763645318093:ℝ)/389301320616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_651
  · change lowerPayment 652 ≤ lowerValue ((point 2 split 4096 652+point 2 split 4096 653)/2)
    have hp : lowerPayment 652 = (92555987520:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 652+point 2 split 4096 653)/2 = (75105271:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((75105271:ℝ)/33751040)/ClassicalSixthBranch.v ((75105271:ℝ)/33751040) = (763568004419:ℝ)/389253312728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_652
  · change lowerPayment 653 ≤ lowerValue ((point 2 split 4096 653+point 2 split 4096 654)/2)
    have hp : lowerPayment 653 = (92680252502:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 653+point 2 split 4096 654)/2 = (375584617:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((375584617:ℝ)/168755200)/ClassicalSixthBranch.v ((375584617:ℝ)/168755200) = (152698138149:ℝ)/77841060968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_653
  · change lowerPayment 654 ≤ lowerValue ((point 2 split 4096 654+point 2 split 4096 655)/2)
    have hp : lowerPayment 654 = (92804473593:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 654+point 2 split 4096 655)/2 = (375642879:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((375642879:ℝ)/168755200)/ClassicalSixthBranch.v ((375642879:ℝ)/168755200) = (763413377071:ℝ)/389157296952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_654
  · change lowerPayment 655 ≤ lowerValue ((point 2 split 4096 655+point 2 split 4096 656)/2)
    have hp : lowerPayment 655 = (92928650830:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 655+point 2 split 4096 656)/2 = (375701141:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((375701141:ℝ)/168755200)/ClassicalSixthBranch.v ((375701141:ℝ)/168755200) = (763336063397:ℝ)/389109289064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_655
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_040
