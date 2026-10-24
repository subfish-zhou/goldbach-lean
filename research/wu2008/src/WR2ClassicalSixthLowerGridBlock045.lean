import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints045
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_045 (j : Fin 16) : lowerPayment (16*45+j.val) ≤
    lowerValue ((point 2 split 4096 (16*45+j.val)+point 2 split 4096 (16*45+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 720 ≤ lowerValue ((point 2 split 4096 720+point 2 split 4096 721)/2)
    have hp : lowerPayment 720 = (100907949300:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 720+point 2 split 4096 721)/2 = (379488171:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((379488171:ℝ)/168755200)/ClassicalSixthBranch.v ((379488171:ℝ)/168755200) = (758310674587:ℝ)/385988776344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_720
  · change lowerPayment 721 ≤ lowerValue ((point 2 split 4096 721+point 2 split 4096 722)/2)
    have hp : lowerPayment 721 = (101029316893:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 721+point 2 split 4096 722)/2 = (379546433:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((379546433:ℝ)/168755200)/ClassicalSixthBranch.v ((379546433:ℝ)/168755200) = (758233360913:ℝ)/385940768456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_721
  · change lowerPayment 722 ≤ lowerValue ((point 2 split 4096 722+point 2 split 4096 723)/2)
    have hp : lowerPayment 722 = (101150643175:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 722+point 2 split 4096 723)/2 = (75920939:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((75920939:ℝ)/33751040)/ClassicalSixthBranch.v ((75920939:ℝ)/33751040) = (758156047239:ℝ)/385892760568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_722
  · change lowerPayment 723 ≤ lowerValue ((point 2 split 4096 723+point 2 split 4096 724)/2)
    have hp : lowerPayment 723 = (101271928181:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 723+point 2 split 4096 724)/2 = (379662957:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((379662957:ℝ)/168755200)/ClassicalSixthBranch.v ((379662957:ℝ)/168755200) = (151615746713:ℝ)/77168950536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_723
  · change lowerPayment 724 ≤ lowerValue ((point 2 split 4096 724+point 2 split 4096 725)/2)
    have hp : lowerPayment 724 = (101393171950:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 724+point 2 split 4096 725)/2 = (379721219:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((379721219:ℝ)/168755200)/ClassicalSixthBranch.v ((379721219:ℝ)/168755200) = (758001419891:ℝ)/385796744792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_724
  · change lowerPayment 725 ≤ lowerValue ((point 2 split 4096 725+point 2 split 4096 726)/2)
    have hp : lowerPayment 725 = (101514374518:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 725+point 2 split 4096 726)/2 = (379779481:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((379779481:ℝ)/168755200)/ClassicalSixthBranch.v ((379779481:ℝ)/168755200) = (757924106217:ℝ)/385748736904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_725
  · change lowerPayment 726 ≤ lowerValue ((point 2 split 4096 726+point 2 split 4096 727)/2)
    have hp : lowerPayment 726 = (101635535921:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 726+point 2 split 4096 727)/2 = (379837743:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((379837743:ℝ)/168755200)/ClassicalSixthBranch.v ((379837743:ℝ)/168755200) = (757846792543:ℝ)/385700729016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_726
  · change lowerPayment 727 ≤ lowerValue ((point 2 split 4096 727+point 2 split 4096 728)/2)
    have hp : lowerPayment 727 = (101756656196:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 727+point 2 split 4096 728)/2 = (75979201:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((75979201:ℝ)/33751040)/ClassicalSixthBranch.v ((75979201:ℝ)/33751040) = (757769478869:ℝ)/385652721128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_727
  · change lowerPayment 728 ≤ lowerValue ((point 2 split 4096 728+point 2 split 4096 729)/2)
    have hp : lowerPayment 728 = (101877735381:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 728+point 2 split 4096 729)/2 = (379954267:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((379954267:ℝ)/168755200)/ClassicalSixthBranch.v ((379954267:ℝ)/168755200) = (151538433039:ℝ)/77120942648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_728
  · change lowerPayment 729 ≤ lowerValue ((point 2 split 4096 729+point 2 split 4096 730)/2)
    have hp : lowerPayment 729 = (101998773511:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 729+point 2 split 4096 730)/2 = (380012529:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((380012529:ℝ)/168755200)/ClassicalSixthBranch.v ((380012529:ℝ)/168755200) = (757614851521:ℝ)/385556705352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_729
  · change lowerPayment 730 ≤ lowerValue ((point 2 split 4096 730+point 2 split 4096 731)/2)
    have hp : lowerPayment 730 = (102119770624:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 730+point 2 split 4096 731)/2 = (380070791:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((380070791:ℝ)/168755200)/ClassicalSixthBranch.v ((380070791:ℝ)/168755200) = (757537537847:ℝ)/385508697464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_730
  · change lowerPayment 731 ≤ lowerValue ((point 2 split 4096 731+point 2 split 4096 732)/2)
    have hp : lowerPayment 731 = (102240726755:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 731+point 2 split 4096 732)/2 = (380129053:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((380129053:ℝ)/168755200)/ClassicalSixthBranch.v ((380129053:ℝ)/168755200) = (757460224173:ℝ)/385460689576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_731
  · change lowerPayment 732 ≤ lowerValue ((point 2 split 4096 732+point 2 split 4096 733)/2)
    have hp : lowerPayment 732 = (102361641942:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 732+point 2 split 4096 733)/2 = (76037463:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((76037463:ℝ)/33751040)/ClassicalSixthBranch.v ((76037463:ℝ)/33751040) = (757382910499:ℝ)/385412681688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_732
  · change lowerPayment 733 ≤ lowerValue ((point 2 split 4096 733+point 2 split 4096 734)/2)
    have hp : lowerPayment 733 = (102482516222:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 733+point 2 split 4096 734)/2 = (380245577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((380245577:ℝ)/168755200)/ClassicalSixthBranch.v ((380245577:ℝ)/168755200) = (30292223873:ℝ)/15414586952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_733
  · change lowerPayment 734 ≤ lowerValue ((point 2 split 4096 734+point 2 split 4096 735)/2)
    have hp : lowerPayment 734 = (102603349630:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 734+point 2 split 4096 735)/2 = (380303839:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((380303839:ℝ)/168755200)/ClassicalSixthBranch.v ((380303839:ℝ)/168755200) = (757228283151:ℝ)/385316665912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_734
  · change lowerPayment 735 ≤ lowerValue ((point 2 split 4096 735+point 2 split 4096 736)/2)
    have hp : lowerPayment 735 = (102724142203:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 735+point 2 split 4096 736)/2 = (380362101:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((380362101:ℝ)/168755200)/ClassicalSixthBranch.v ((380362101:ℝ)/168755200) = (757150969477:ℝ)/385268658024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_735
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_045
