import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints179
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_179 (j : Fin 16) : lowerPayment (16*179+j.val) ≤
    lowerValue ((point 2 split 4096 (16*179+j.val)+point 2 split 4096 (16*179+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2864 ≤ lowerValue ((point 2 split 4096 2864+point 2 split 4096 2865)/2)
    have hp : lowerPayment 2864 = (309282319605:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2864+point 2 split 4096 2865)/2 = (504401899:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((504401899:ℝ)/168755200)/ClassicalSixthBranch.v ((504401899:ℝ)/168755200) = (592550157531:ℝ)/283059864472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2864
  · change lowerPayment 2865 ≤ lowerValue ((point 2 split 4096 2865+point 2 split 4096 2866)/2)
    have hp : lowerPayment 2865 = (309370338692:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2865+point 2 split 4096 2866)/2 = (504460161:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((504460161:ℝ)/168755200)/ClassicalSixthBranch.v ((504460161:ℝ)/168755200) = (592472843857:ℝ)/283011856584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2865
  · change lowerPayment 2866 ≤ lowerValue ((point 2 split 4096 2866+point 2 split 4096 2867)/2)
    have hp : lowerPayment 2866 = (309458360527:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2866+point 2 split 4096 2867)/2 = (504518423:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((504518423:ℝ)/168755200)/ClassicalSixthBranch.v ((504518423:ℝ)/168755200) = (592395530183:ℝ)/282963848696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2866
  · change lowerPayment 2867 ≤ lowerValue ((point 2 split 4096 2867+point 2 split 4096 2868)/2)
    have hp : lowerPayment 2867 = (309546385124:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2867+point 2 split 4096 2868)/2 = (100915337:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((100915337:ℝ)/33751040)/ClassicalSixthBranch.v ((100915337:ℝ)/33751040) = (592318216509:ℝ)/282915840808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2867
  · change lowerPayment 2868 ≤ lowerValue ((point 2 split 4096 2868+point 2 split 4096 2869)/2)
    have hp : lowerPayment 2868 = (309634412498:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2868+point 2 split 4096 2869)/2 = (504634947:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((504634947:ℝ)/168755200)/ClassicalSixthBranch.v ((504634947:ℝ)/168755200) = (118448180567:ℝ)/56573566584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2868
  · change lowerPayment 2869 ≤ lowerValue ((point 2 split 4096 2869+point 2 split 4096 2870)/2)
    have hp : lowerPayment 2869 = (309722442662:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2869+point 2 split 4096 2870)/2 = (504693209:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((504693209:ℝ)/168755200)/ClassicalSixthBranch.v ((504693209:ℝ)/168755200) = (592163589161:ℝ)/282819825032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2869
  · change lowerPayment 2870 ≤ lowerValue ((point 2 split 4096 2870+point 2 split 4096 2871)/2)
    have hp : lowerPayment 2870 = (309810475631:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2870+point 2 split 4096 2871)/2 = (504751471:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((504751471:ℝ)/168755200)/ClassicalSixthBranch.v ((504751471:ℝ)/168755200) = (592086275487:ℝ)/282771817144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2870
  · change lowerPayment 2871 ≤ lowerValue ((point 2 split 4096 2871+point 2 split 4096 2872)/2)
    have hp : lowerPayment 2871 = (309898511418:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2871+point 2 split 4096 2872)/2 = (504809733:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((504809733:ℝ)/168755200)/ClassicalSixthBranch.v ((504809733:ℝ)/168755200) = (592008961813:ℝ)/282723809256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2871
  · change lowerPayment 2872 ≤ lowerValue ((point 2 split 4096 2872+point 2 split 4096 2873)/2)
    have hp : lowerPayment 2872 = (309986550038:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2872+point 2 split 4096 2873)/2 = (100973599:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((100973599:ℝ)/33751040)/ClassicalSixthBranch.v ((100973599:ℝ)/33751040) = (591931648139:ℝ)/282675801368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2872
  · change lowerPayment 2873 ≤ lowerValue ((point 2 split 4096 2873+point 2 split 4096 2874)/2)
    have hp : lowerPayment 2873 = (310074591505:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2873+point 2 split 4096 2874)/2 = (504926257:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((504926257:ℝ)/168755200)/ClassicalSixthBranch.v ((504926257:ℝ)/168755200) = (118370866893:ℝ)/56525558696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2873
  · change lowerPayment 2874 ≤ lowerValue ((point 2 split 4096 2874+point 2 split 4096 2875)/2)
    have hp : lowerPayment 2874 = (310162635833:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2874+point 2 split 4096 2875)/2 = (504984519:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((504984519:ℝ)/168755200)/ClassicalSixthBranch.v ((504984519:ℝ)/168755200) = (591777020791:ℝ)/282579785592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2874
  · change lowerPayment 2875 ≤ lowerValue ((point 2 split 4096 2875+point 2 split 4096 2876)/2)
    have hp : lowerPayment 2875 = (310250683035:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2875+point 2 split 4096 2876)/2 = (505042781:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((505042781:ℝ)/168755200)/ClassicalSixthBranch.v ((505042781:ℝ)/168755200) = (591699707117:ℝ)/282531777704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2875
  · change lowerPayment 2876 ≤ lowerValue ((point 2 split 4096 2876+point 2 split 4096 2877)/2)
    have hp : lowerPayment 2876 = (310338733128:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2876+point 2 split 4096 2877)/2 = (505101043:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((505101043:ℝ)/168755200)/ClassicalSixthBranch.v ((505101043:ℝ)/168755200) = (591622393443:ℝ)/282483769816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2876
  · change lowerPayment 2877 ≤ lowerValue ((point 2 split 4096 2877+point 2 split 4096 2878)/2)
    have hp : lowerPayment 2877 = (310426786123:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2877+point 2 split 4096 2878)/2 = (101031861:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((101031861:ℝ)/33751040)/ClassicalSixthBranch.v ((101031861:ℝ)/33751040) = (591545079769:ℝ)/282435761928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2877
  · change lowerPayment 2878 ≤ lowerValue ((point 2 split 4096 2878+point 2 split 4096 2879)/2)
    have hp : lowerPayment 2878 = (310514842036:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2878+point 2 split 4096 2879)/2 = (505217567:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((505217567:ℝ)/168755200)/ClassicalSixthBranch.v ((505217567:ℝ)/168755200) = (118293553219:ℝ)/56477550808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2878
  · change lowerPayment 2879 ≤ lowerValue ((point 2 split 4096 2879+point 2 split 4096 2880)/2)
    have hp : lowerPayment 2879 = (310602900880:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2879+point 2 split 4096 2880)/2 = (505275829:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((505275829:ℝ)/168755200)/ClassicalSixthBranch.v ((505275829:ℝ)/168755200) = (591390452421:ℝ)/282339746152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2879
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_179
