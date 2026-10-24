import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints056
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_056 (j : Fin 16) : lowerPayment (16*56+j.val) ≤
    lowerValue ((point 2 split 4096 (16*56+j.val)+point 2 split 4096 (16*56+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 896 ≤ lowerValue ((point 2 split 4096 896+point 2 split 4096 897)/2)
    have hp : lowerPayment 896 = (121664243187:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 896+point 2 split 4096 897)/2 = (389742283:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((389742283:ℝ)/168755200)/ClassicalSixthBranch.v ((389742283:ℝ)/168755200) = (744703467963:ℝ)/377539388056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_896
  · change lowerPayment 897 ≤ lowerValue ((point 2 split 4096 897+point 2 split 4096 898)/2)
    have hp : lowerPayment 897 = (121778881769:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 897+point 2 split 4096 898)/2 = (77960109:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((77960109:ℝ)/33751040)/ClassicalSixthBranch.v ((77960109:ℝ)/33751040) = (744626154289:ℝ)/377491380168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_897
  · change lowerPayment 898 ≤ lowerValue ((point 2 split 4096 898+point 2 split 4096 899)/2)
    have hp : lowerPayment 898 = (121893485089:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 898+point 2 split 4096 899)/2 = (389858807:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((389858807:ℝ)/168755200)/ClassicalSixthBranch.v ((389858807:ℝ)/168755200) = (148909768123:ℝ)/75488674456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_898
  · change lowerPayment 899 ≤ lowerValue ((point 2 split 4096 899+point 2 split 4096 900)/2)
    have hp : lowerPayment 899 = (122008053179:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 899+point 2 split 4096 900)/2 = (389917069:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((389917069:ℝ)/168755200)/ClassicalSixthBranch.v ((389917069:ℝ)/168755200) = (744471526941:ℝ)/377395364392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_899
  · change lowerPayment 900 ≤ lowerValue ((point 2 split 4096 900+point 2 split 4096 901)/2)
    have hp : lowerPayment 900 = (122122586071:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 900+point 2 split 4096 901)/2 = (389975331:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((389975331:ℝ)/168755200)/ClassicalSixthBranch.v ((389975331:ℝ)/168755200) = (744394213267:ℝ)/377347356504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_900
  · change lowerPayment 901 ≤ lowerValue ((point 2 split 4096 901+point 2 split 4096 902)/2)
    have hp : lowerPayment 901 = (122237083797:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 901+point 2 split 4096 902)/2 = (390033593:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((390033593:ℝ)/168755200)/ClassicalSixthBranch.v ((390033593:ℝ)/168755200) = (744316899593:ℝ)/377299348616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_901
  · change lowerPayment 902 ≤ lowerValue ((point 2 split 4096 902+point 2 split 4096 903)/2)
    have hp : lowerPayment 902 = (122351546389:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 902+point 2 split 4096 903)/2 = (78018371:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((78018371:ℝ)/33751040)/ClassicalSixthBranch.v ((78018371:ℝ)/33751040) = (744239585919:ℝ)/377251340728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_902
  · change lowerPayment 903 ≤ lowerValue ((point 2 split 4096 903+point 2 split 4096 904)/2)
    have hp : lowerPayment 903 = (122465973878:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 903+point 2 split 4096 904)/2 = (390150117:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((390150117:ℝ)/168755200)/ClassicalSixthBranch.v ((390150117:ℝ)/168755200) = (148832454449:ℝ)/75440666568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_903
  · change lowerPayment 904 ≤ lowerValue ((point 2 split 4096 904+point 2 split 4096 905)/2)
    have hp : lowerPayment 904 = (122580366297:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 904+point 2 split 4096 905)/2 = (390208379:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((390208379:ℝ)/168755200)/ClassicalSixthBranch.v ((390208379:ℝ)/168755200) = (744084958571:ℝ)/377155324952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_904
  · change lowerPayment 905 ≤ lowerValue ((point 2 split 4096 905+point 2 split 4096 906)/2)
    have hp : lowerPayment 905 = (122694723677:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 905+point 2 split 4096 906)/2 = (390266641:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((390266641:ℝ)/168755200)/ClassicalSixthBranch.v ((390266641:ℝ)/168755200) = (744007644897:ℝ)/377107317064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_905
  · change lowerPayment 906 ≤ lowerValue ((point 2 split 4096 906+point 2 split 4096 907)/2)
    have hp : lowerPayment 906 = (122809046051:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 906+point 2 split 4096 907)/2 = (390324903:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((390324903:ℝ)/168755200)/ClassicalSixthBranch.v ((390324903:ℝ)/168755200) = (743930331223:ℝ)/377059309176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_906
  · change lowerPayment 907 ≤ lowerValue ((point 2 split 4096 907+point 2 split 4096 908)/2)
    have hp : lowerPayment 907 = (122923333450:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 907+point 2 split 4096 908)/2 = (78076633:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((78076633:ℝ)/33751040)/ClassicalSixthBranch.v ((78076633:ℝ)/33751040) = (743853017549:ℝ)/377011301288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_907
  · change lowerPayment 908 ≤ lowerValue ((point 2 split 4096 908+point 2 split 4096 909)/2)
    have hp : lowerPayment 908 = (123037585906:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 908+point 2 split 4096 909)/2 = (390441427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((390441427:ℝ)/168755200)/ClassicalSixthBranch.v ((390441427:ℝ)/168755200) = (29751028155:ℝ)/15078531736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_908
  · change lowerPayment 909 ≤ lowerValue ((point 2 split 4096 909+point 2 split 4096 910)/2)
    have hp : lowerPayment 909 = (123151803450:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 909+point 2 split 4096 910)/2 = (390499689:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((390499689:ℝ)/168755200)/ClassicalSixthBranch.v ((390499689:ℝ)/168755200) = (743698390201:ℝ)/376915285512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_909
  · change lowerPayment 910 ≤ lowerValue ((point 2 split 4096 910+point 2 split 4096 911)/2)
    have hp : lowerPayment 910 = (123265986116:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 910+point 2 split 4096 911)/2 = (390557951:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((390557951:ℝ)/168755200)/ClassicalSixthBranch.v ((390557951:ℝ)/168755200) = (743621076527:ℝ)/376867277624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_910
  · change lowerPayment 911 ≤ lowerValue ((point 2 split 4096 911+point 2 split 4096 912)/2)
    have hp : lowerPayment 911 = (123380133933:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 911+point 2 split 4096 912)/2 = (390616213:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((390616213:ℝ)/168755200)/ClassicalSixthBranch.v ((390616213:ℝ)/168755200) = (743543762853:ℝ)/376819269736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_911
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_056
