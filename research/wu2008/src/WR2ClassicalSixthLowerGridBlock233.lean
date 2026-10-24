import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints233
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_233 (j : Fin 16) : lowerPayment (16*233+j.val) ≤
    lowerValue ((point 2 split 4096 (16*233+j.val)+point 2 split 4096 (16*233+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3728 ≤ lowerValue ((point 2 split 4096 3728+point 2 split 4096 3729)/2)
    have hp : lowerPayment 3728 = (387894198831:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3728+point 2 split 4096 3729)/2 = (554740267:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((554740267:ℝ)/168755200)/ClassicalSixthBranch.v ((554740267:ℝ)/168755200) = (105150228639:ℝ)/48316209848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3728
  · change lowerPayment 3729 ≤ lowerValue ((point 2 split 4096 3729+point 2 split 4096 3730)/2)
    have hp : lowerPayment 3729 = (387990012813:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3729+point 2 split 4096 3730)/2 = (554798529:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((554798529:ℝ)/168755200)/ClassicalSixthBranch.v ((554798529:ℝ)/168755200) = (525673829521:ℝ)/241533041352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3729
  · change lowerPayment 3730 ≤ lowerValue ((point 2 split 4096 3730+point 2 split 4096 3731)/2)
    have hp : lowerPayment 3730 = (388085842485:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3730+point 2 split 4096 3731)/2 = (554856791:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((554856791:ℝ)/168755200)/ClassicalSixthBranch.v ((554856791:ℝ)/168755200) = (525596515847:ℝ)/241485033464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3730
  · change lowerPayment 3731 ≤ lowerValue ((point 2 split 4096 3731+point 2 split 4096 3732)/2)
    have hp : lowerPayment 3731 = (388181687864:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3731+point 2 split 4096 3732)/2 = (554915053:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((554915053:ℝ)/168755200)/ClassicalSixthBranch.v ((554915053:ℝ)/168755200) = (525519202173:ℝ)/241437025576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3731
  · change lowerPayment 3732 ≤ lowerValue ((point 2 split 4096 3732+point 2 split 4096 3733)/2)
    have hp : lowerPayment 3732 = (388277548968:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3732+point 2 split 4096 3733)/2 = (110994663:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((110994663:ℝ)/33751040)/ClassicalSixthBranch.v ((110994663:ℝ)/33751040) = (525441888499:ℝ)/241389017688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3732
  · change lowerPayment 3733 ≤ lowerValue ((point 2 split 4096 3733+point 2 split 4096 3734)/2)
    have hp : lowerPayment 3733 = (388373425811:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3733+point 2 split 4096 3734)/2 = (555031577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((555031577:ℝ)/168755200)/ClassicalSixthBranch.v ((555031577:ℝ)/168755200) = (21014582993:ℝ)/9653640392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3733
  · change lowerPayment 3734 ≤ lowerValue ((point 2 split 4096 3734+point 2 split 4096 3735)/2)
    have hp : lowerPayment 3734 = (388469318412:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3734+point 2 split 4096 3735)/2 = (555089839:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((555089839:ℝ)/168755200)/ClassicalSixthBranch.v ((555089839:ℝ)/168755200) = (525287261151:ℝ)/241293001912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3734
  · change lowerPayment 3735 ≤ lowerValue ((point 2 split 4096 3735+point 2 split 4096 3736)/2)
    have hp : lowerPayment 3735 = (388565226788:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3735+point 2 split 4096 3736)/2 = (555148101:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((555148101:ℝ)/168755200)/ClassicalSixthBranch.v ((555148101:ℝ)/168755200) = (525209947477:ℝ)/241244994024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3735
  · change lowerPayment 3736 ≤ lowerValue ((point 2 split 4096 3736+point 2 split 4096 3737)/2)
    have hp : lowerPayment 3736 = (388661150954:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3736+point 2 split 4096 3737)/2 = (555206363:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((555206363:ℝ)/168755200)/ClassicalSixthBranch.v ((555206363:ℝ)/168755200) = (525132633803:ℝ)/241196986136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3736
  · change lowerPayment 3737 ≤ lowerValue ((point 2 split 4096 3737+point 2 split 4096 3738)/2)
    have hp : lowerPayment 3737 = (388757090929:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3737+point 2 split 4096 3738)/2 = (22210585:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((22210585:ℝ)/6750208)/ClassicalSixthBranch.v ((22210585:ℝ)/6750208) = (525055320129:ℝ)/241148978248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3737
  · change lowerPayment 3738 ≤ lowerValue ((point 2 split 4096 3738+point 2 split 4096 3739)/2)
    have hp : lowerPayment 3738 = (388853046728:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3738+point 2 split 4096 3739)/2 = (555322887:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((555322887:ℝ)/168755200)/ClassicalSixthBranch.v ((555322887:ℝ)/168755200) = (104995601291:ℝ)/48220194072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3738
  · change lowerPayment 3739 ≤ lowerValue ((point 2 split 4096 3739+point 2 split 4096 3740)/2)
    have hp : lowerPayment 3739 = (388949018368:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3739+point 2 split 4096 3740)/2 = (555381149:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((555381149:ℝ)/168755200)/ClassicalSixthBranch.v ((555381149:ℝ)/168755200) = (524900692781:ℝ)/241052962472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3739
  · change lowerPayment 3740 ≤ lowerValue ((point 2 split 4096 3740+point 2 split 4096 3741)/2)
    have hp : lowerPayment 3740 = (389045005867:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3740+point 2 split 4096 3741)/2 = (555439411:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((555439411:ℝ)/168755200)/ClassicalSixthBranch.v ((555439411:ℝ)/168755200) = (524823379107:ℝ)/241004954584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3740
  · change lowerPayment 3741 ≤ lowerValue ((point 2 split 4096 3741+point 2 split 4096 3742)/2)
    have hp : lowerPayment 3741 = (389141009241:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3741+point 2 split 4096 3742)/2 = (555497673:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((555497673:ℝ)/168755200)/ClassicalSixthBranch.v ((555497673:ℝ)/168755200) = (524746065433:ℝ)/240956946696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3741
  · change lowerPayment 3742 ≤ lowerValue ((point 2 split 4096 3742+point 2 split 4096 3743)/2)
    have hp : lowerPayment 3742 = (389237028507:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3742+point 2 split 4096 3743)/2 = (111111187:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((111111187:ℝ)/33751040)/ClassicalSixthBranch.v ((111111187:ℝ)/33751040) = (524668751759:ℝ)/240908938808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3742
  · change lowerPayment 3743 ≤ lowerValue ((point 2 split 4096 3743+point 2 split 4096 3744)/2)
    have hp : lowerPayment 3743 = (389333063682:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3743+point 2 split 4096 3744)/2 = (555614197:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((555614197:ℝ)/168755200)/ClassicalSixthBranch.v ((555614197:ℝ)/168755200) = (104918287617:ℝ)/48172186184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3743
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_233
