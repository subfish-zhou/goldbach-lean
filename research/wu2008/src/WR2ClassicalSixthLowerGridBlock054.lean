import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints054
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_054 (j : Fin 16) : lowerPayment (16*54+j.val) ≤
    lowerValue ((point 2 split 4096 (16*54+j.val)+point 2 split 4096 (16*54+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 864 ≤ lowerValue ((point 2 split 4096 864+point 2 split 4096 865)/2)
    have hp : lowerPayment 864 = (117976997247:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 864+point 2 split 4096 865)/2 = (387877899:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((387877899:ℝ)/168755200)/ClassicalSixthBranch.v ((387877899:ℝ)/168755200) = (747177505531:ℝ)/379075640472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_864
  · change lowerPayment 865 ≤ lowerValue ((point 2 split 4096 865+point 2 split 4096 866)/2)
    have hp : lowerPayment 865 = (118092781273:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 865+point 2 split 4096 866)/2 = (387936161:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((387936161:ℝ)/168755200)/ClassicalSixthBranch.v ((387936161:ℝ)/168755200) = (747100191857:ℝ)/379027632584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_865
  · change lowerPayment 866 ≤ lowerValue ((point 2 split 4096 866+point 2 split 4096 867)/2)
    have hp : lowerPayment 866 = (118208528999:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 866+point 2 split 4096 867)/2 = (387994423:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((387994423:ℝ)/168755200)/ClassicalSixthBranch.v ((387994423:ℝ)/168755200) = (747022878183:ℝ)/378979624696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_866
  · change lowerPayment 867 ≤ lowerValue ((point 2 split 4096 867+point 2 split 4096 868)/2)
    have hp : lowerPayment 867 = (118324240458:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 867+point 2 split 4096 868)/2 = (77610537:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((77610537:ℝ)/33751040)/ClassicalSixthBranch.v ((77610537:ℝ)/33751040) = (746945564509:ℝ)/378931616808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_867
  · change lowerPayment 868 ≤ lowerValue ((point 2 split 4096 868+point 2 split 4096 869)/2)
    have hp : lowerPayment 868 = (118439915682:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 868+point 2 split 4096 869)/2 = (388110947:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((388110947:ℝ)/168755200)/ClassicalSixthBranch.v ((388110947:ℝ)/168755200) = (149373650167:ℝ)/75776721784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_868
  · change lowerPayment 869 ≤ lowerValue ((point 2 split 4096 869+point 2 split 4096 870)/2)
    have hp : lowerPayment 869 = (118555554705:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 869+point 2 split 4096 870)/2 = (388169209:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((388169209:ℝ)/168755200)/ClassicalSixthBranch.v ((388169209:ℝ)/168755200) = (746790937161:ℝ)/378835601032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_869
  · change lowerPayment 870 ≤ lowerValue ((point 2 split 4096 870+point 2 split 4096 871)/2)
    have hp : lowerPayment 870 = (118671157559:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 870+point 2 split 4096 871)/2 = (388227471:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((388227471:ℝ)/168755200)/ClassicalSixthBranch.v ((388227471:ℝ)/168755200) = (746713623487:ℝ)/378787593144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_870
  · change lowerPayment 871 ≤ lowerValue ((point 2 split 4096 871+point 2 split 4096 872)/2)
    have hp : lowerPayment 871 = (118786724277:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 871+point 2 split 4096 872)/2 = (388285733:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((388285733:ℝ)/168755200)/ClassicalSixthBranch.v ((388285733:ℝ)/168755200) = (746636309813:ℝ)/378739585256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_871
  · change lowerPayment 872 ≤ lowerValue ((point 2 split 4096 872+point 2 split 4096 873)/2)
    have hp : lowerPayment 872 = (118902254891:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 872+point 2 split 4096 873)/2 = (77668799:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((77668799:ℝ)/33751040)/ClassicalSixthBranch.v ((77668799:ℝ)/33751040) = (746558996139:ℝ)/378691577368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_872
  · change lowerPayment 873 ≤ lowerValue ((point 2 split 4096 873+point 2 split 4096 874)/2)
    have hp : lowerPayment 873 = (119017749435:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 873+point 2 split 4096 874)/2 = (388402257:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((388402257:ℝ)/168755200)/ClassicalSixthBranch.v ((388402257:ℝ)/168755200) = (149296336493:ℝ)/75728713896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_873
  · change lowerPayment 874 ≤ lowerValue ((point 2 split 4096 874+point 2 split 4096 875)/2)
    have hp : lowerPayment 874 = (119133207941:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 874+point 2 split 4096 875)/2 = (388460519:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((388460519:ℝ)/168755200)/ClassicalSixthBranch.v ((388460519:ℝ)/168755200) = (746404368791:ℝ)/378595561592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_874
  · change lowerPayment 875 ≤ lowerValue ((point 2 split 4096 875+point 2 split 4096 876)/2)
    have hp : lowerPayment 875 = (119248630441:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 875+point 2 split 4096 876)/2 = (3772027:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((3772027:ℝ)/1638400)/ClassicalSixthBranch.v ((3772027:ℝ)/1638400) = (7245893739:ℝ)/3675218968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_875
  · change lowerPayment 876 ≤ lowerValue ((point 2 split 4096 876+point 2 split 4096 877)/2)
    have hp : lowerPayment 876 = (119364016968:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 876+point 2 split 4096 877)/2 = (388577043:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((388577043:ℝ)/168755200)/ClassicalSixthBranch.v ((388577043:ℝ)/168755200) = (746249741443:ℝ)/378499545816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_876
  · change lowerPayment 877 ≤ lowerValue ((point 2 split 4096 877+point 2 split 4096 878)/2)
    have hp : lowerPayment 877 = (119479367555:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 877+point 2 split 4096 878)/2 = (77727061:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((77727061:ℝ)/33751040)/ClassicalSixthBranch.v ((77727061:ℝ)/33751040) = (746172427769:ℝ)/378451537928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_877
  · change lowerPayment 878 ≤ lowerValue ((point 2 split 4096 878+point 2 split 4096 879)/2)
    have hp : lowerPayment 878 = (119594682234:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 878+point 2 split 4096 879)/2 = (388693567:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((388693567:ℝ)/168755200)/ClassicalSixthBranch.v ((388693567:ℝ)/168755200) = (149219022819:ℝ)/75680706008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_878
  · change lowerPayment 879 ≤ lowerValue ((point 2 split 4096 879+point 2 split 4096 880)/2)
    have hp : lowerPayment 879 = (119709961039:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 879+point 2 split 4096 880)/2 = (388751829:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((388751829:ℝ)/168755200)/ClassicalSixthBranch.v ((388751829:ℝ)/168755200) = (746017800421:ℝ)/378355522152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_879
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_054
