import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints193
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_193 (j : Fin 16) : lowerPayment (16*193+j.val) ≤
    lowerValue ((point 2 split 4096 (16*193+j.val)+point 2 split 4096 (16*193+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3088 ≤ lowerValue ((point 2 split 4096 3088+point 2 split 4096 3089)/2)
    have hp : lowerPayment 3088 = (329093335643:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3088+point 2 split 4096 3089)/2 = (517452587:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((517452587:ℝ)/168755200)/ClassicalSixthBranch.v ((517452587:ℝ)/168755200) = (115046378911:ℝ)/54461219512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3088
  · change lowerPayment 3089 ≤ lowerValue ((point 2 split 4096 3089+point 2 split 4096 3090)/2)
    have hp : lowerPayment 3089 = (329182323357:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3089+point 2 split 4096 3090)/2 = (517510849:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((517510849:ℝ)/168755200)/ClassicalSixthBranch.v ((517510849:ℝ)/168755200) = (575154580881:ℝ)/272258089672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3089
  · change lowerPayment 3090 ≤ lowerValue ((point 2 split 4096 3090+point 2 split 4096 3091)/2)
    have hp : lowerPayment 3090 = (329271316992:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3090+point 2 split 4096 3091)/2 = (517569111:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((517569111:ℝ)/168755200)/ClassicalSixthBranch.v ((517569111:ℝ)/168755200) = (575077267207:ℝ)/272210081784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3090
  · change lowerPayment 3091 ≤ lowerValue ((point 2 split 4096 3091+point 2 split 4096 3092)/2)
    have hp : lowerPayment 3091 = (329360316563:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3091+point 2 split 4096 3092)/2 = (517627373:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((517627373:ℝ)/168755200)/ClassicalSixthBranch.v ((517627373:ℝ)/168755200) = (574999953533:ℝ)/272162073896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3091
  · change lowerPayment 3092 ≤ lowerValue ((point 2 split 4096 3092+point 2 split 4096 3093)/2)
    have hp : lowerPayment 3092 = (329449322083:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3092+point 2 split 4096 3093)/2 = (103537127:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((103537127:ℝ)/33751040)/ClassicalSixthBranch.v ((103537127:ℝ)/33751040) = (574922639859:ℝ)/272114066008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3092
  · change lowerPayment 3093 ≤ lowerValue ((point 2 split 4096 3093+point 2 split 4096 3094)/2)
    have hp : lowerPayment 3093 = (329538333567:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3093+point 2 split 4096 3094)/2 = (517743897:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((517743897:ℝ)/168755200)/ClassicalSixthBranch.v ((517743897:ℝ)/168755200) = (114969065237:ℝ)/54413211624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3093
  · change lowerPayment 3094 ≤ lowerValue ((point 2 split 4096 3094+point 2 split 4096 3095)/2)
    have hp : lowerPayment 3094 = (329627351030:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3094+point 2 split 4096 3095)/2 = (517802159:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((517802159:ℝ)/168755200)/ClassicalSixthBranch.v ((517802159:ℝ)/168755200) = (574768012511:ℝ)/272018050232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3094
  · change lowerPayment 3095 ≤ lowerValue ((point 2 split 4096 3095+point 2 split 4096 3096)/2)
    have hp : lowerPayment 3095 = (329716374485:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3095+point 2 split 4096 3096)/2 = (517860421:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((517860421:ℝ)/168755200)/ClassicalSixthBranch.v ((517860421:ℝ)/168755200) = (574690698837:ℝ)/271970042344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3095
  · change lowerPayment 3096 ≤ lowerValue ((point 2 split 4096 3096+point 2 split 4096 3097)/2)
    have hp : lowerPayment 3096 = (329805403946:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3096+point 2 split 4096 3097)/2 = (517918683:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((517918683:ℝ)/168755200)/ClassicalSixthBranch.v ((517918683:ℝ)/168755200) = (574613385163:ℝ)/271922034456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3096
  · change lowerPayment 3097 ≤ lowerValue ((point 2 split 4096 3097+point 2 split 4096 3098)/2)
    have hp : lowerPayment 3097 = (329894439429:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3097+point 2 split 4096 3098)/2 = (103595389:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((103595389:ℝ)/33751040)/ClassicalSixthBranch.v ((103595389:ℝ)/33751040) = (574536071489:ℝ)/271874026568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3097
  · change lowerPayment 3098 ≤ lowerValue ((point 2 split 4096 3098+point 2 split 4096 3099)/2)
    have hp : lowerPayment 3098 = (329983480948:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3098+point 2 split 4096 3099)/2 = (518035207:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((518035207:ℝ)/168755200)/ClassicalSixthBranch.v ((518035207:ℝ)/168755200) = (114891751563:ℝ)/54365203736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3098
  · change lowerPayment 3099 ≤ lowerValue ((point 2 split 4096 3099+point 2 split 4096 3100)/2)
    have hp : lowerPayment 3099 = (330072528516:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3099+point 2 split 4096 3100)/2 = (518093469:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((518093469:ℝ)/168755200)/ClassicalSixthBranch.v ((518093469:ℝ)/168755200) = (574381444141:ℝ)/271778010792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3099
  · change lowerPayment 3100 ≤ lowerValue ((point 2 split 4096 3100+point 2 split 4096 3101)/2)
    have hp : lowerPayment 3100 = (330161582147:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3100+point 2 split 4096 3101)/2 = (518151731:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((518151731:ℝ)/168755200)/ClassicalSixthBranch.v ((518151731:ℝ)/168755200) = (574304130467:ℝ)/271730002904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3100
  · change lowerPayment 3101 ≤ lowerValue ((point 2 split 4096 3101+point 2 split 4096 3102)/2)
    have hp : lowerPayment 3101 = (330250641858:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3101+point 2 split 4096 3102)/2 = (518209993:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((518209993:ℝ)/168755200)/ClassicalSixthBranch.v ((518209993:ℝ)/168755200) = (574226816793:ℝ)/271681995016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3101
  · change lowerPayment 3102 ≤ lowerValue ((point 2 split 4096 3102+point 2 split 4096 3103)/2)
    have hp : lowerPayment 3102 = (330339707660:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3102+point 2 split 4096 3103)/2 = (103653651:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((103653651:ℝ)/33751040)/ClassicalSixthBranch.v ((103653651:ℝ)/33751040) = (574149503119:ℝ)/271633987128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3102
  · change lowerPayment 3103 ≤ lowerValue ((point 2 split 4096 3103+point 2 split 4096 3104)/2)
    have hp : lowerPayment 3103 = (330428779570:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3103+point 2 split 4096 3104)/2 = (518326517:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((518326517:ℝ)/168755200)/ClassicalSixthBranch.v ((518326517:ℝ)/168755200) = (114814437889:ℝ)/54317195848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3103
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_193
