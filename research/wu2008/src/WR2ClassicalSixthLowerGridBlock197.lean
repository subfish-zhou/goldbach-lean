import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints197
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_197 (j : Fin 16) : lowerPayment (16*197+j.val) ≤
    lowerValue ((point 2 split 4096 (16*197+j.val)+point 2 split 4096 (16*197+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3152 ≤ lowerValue ((point 2 split 4096 3152+point 2 split 4096 3153)/2)
    have hp : lowerPayment 3152 = (334801082357:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3152+point 2 split 4096 3153)/2 = (104236271:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((104236271:ℝ)/33751040)/ClassicalSixthBranch.v ((104236271:ℝ)/33751040) = (570283819419:ℝ)/269233592728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3152
  · change lowerPayment 3153 ≤ lowerValue ((point 2 split 4096 3153+point 2 split 4096 3154)/2)
    have hp : lowerPayment 3153 = (334890477883:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3153+point 2 split 4096 3154)/2 = (521239617:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((521239617:ℝ)/168755200)/ClassicalSixthBranch.v ((521239617:ℝ)/168755200) = (114041301149:ℝ)/53837116968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3153
  · change lowerPayment 3154 ≤ lowerValue ((point 2 split 4096 3154+point 2 split 4096 3155)/2)
    have hp : lowerPayment 3154 = (334979880247:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3154+point 2 split 4096 3155)/2 = (521297879:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((521297879:ℝ)/168755200)/ClassicalSixthBranch.v ((521297879:ℝ)/168755200) = (570129192071:ℝ)/269137576952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3154
  · change lowerPayment 3155 ≤ lowerValue ((point 2 split 4096 3155+point 2 split 4096 3156)/2)
    have hp : lowerPayment 3155 = (335069289464:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3155+point 2 split 4096 3156)/2 = (521356141:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((521356141:ℝ)/168755200)/ClassicalSixthBranch.v ((521356141:ℝ)/168755200) = (570051878397:ℝ)/269089569064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3155
  · change lowerPayment 3156 ≤ lowerValue ((point 2 split 4096 3156+point 2 split 4096 3157)/2)
    have hp : lowerPayment 3156 = (335158705549:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3156+point 2 split 4096 3157)/2 = (521414403:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((521414403:ℝ)/168755200)/ClassicalSixthBranch.v ((521414403:ℝ)/168755200) = (569974564723:ℝ)/269041561176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3156
  · change lowerPayment 3157 ≤ lowerValue ((point 2 split 4096 3157+point 2 split 4096 3158)/2)
    have hp : lowerPayment 3157 = (335248128515:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3157+point 2 split 4096 3158)/2 = (104294533:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((104294533:ℝ)/33751040)/ClassicalSixthBranch.v ((104294533:ℝ)/33751040) = (569897251049:ℝ)/268993553288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3157
  · change lowerPayment 3158 ≤ lowerValue ((point 2 split 4096 3158+point 2 split 4096 3159)/2)
    have hp : lowerPayment 3158 = (335337558378:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3158+point 2 split 4096 3159)/2 = (521530927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((521530927:ℝ)/168755200)/ClassicalSixthBranch.v ((521530927:ℝ)/168755200) = (22792797495:ℝ)/10757821816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3158
  · change lowerPayment 3159 ≤ lowerValue ((point 2 split 4096 3159+point 2 split 4096 3160)/2)
    have hp : lowerPayment 3159 = (335426995151:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3159+point 2 split 4096 3160)/2 = (521589189:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((521589189:ℝ)/168755200)/ClassicalSixthBranch.v ((521589189:ℝ)/168755200) = (569742623701:ℝ)/268897537512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3159
  · change lowerPayment 3160 ≤ lowerValue ((point 2 split 4096 3160+point 2 split 4096 3161)/2)
    have hp : lowerPayment 3160 = (335516438849:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3160+point 2 split 4096 3161)/2 = (521647451:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((521647451:ℝ)/168755200)/ClassicalSixthBranch.v ((521647451:ℝ)/168755200) = (569665310027:ℝ)/268849529624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3160
  · change lowerPayment 3161 ≤ lowerValue ((point 2 split 4096 3161+point 2 split 4096 3162)/2)
    have hp : lowerPayment 3161 = (335605889486:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3161+point 2 split 4096 3162)/2 = (521705713:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((521705713:ℝ)/168755200)/ClassicalSixthBranch.v ((521705713:ℝ)/168755200) = (569587996353:ℝ)/268801521736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3161
  · change lowerPayment 3162 ≤ lowerValue ((point 2 split 4096 3162+point 2 split 4096 3163)/2)
    have hp : lowerPayment 3162 = (335695347077:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3162+point 2 split 4096 3163)/2 = (20870559:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((20870559:ℝ)/6750208)/ClassicalSixthBranch.v ((20870559:ℝ)/6750208) = (569510682679:ℝ)/268753513848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3162
  · change lowerPayment 3163 ≤ lowerValue ((point 2 split 4096 3163+point 2 split 4096 3164)/2)
    have hp : lowerPayment 3163 = (335784811636:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3163+point 2 split 4096 3164)/2 = (521822237:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((521822237:ℝ)/168755200)/ClassicalSixthBranch.v ((521822237:ℝ)/168755200) = (113886673801:ℝ)/53741101192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3163
  · change lowerPayment 3164 ≤ lowerValue ((point 2 split 4096 3164+point 2 split 4096 3165)/2)
    have hp : lowerPayment 3164 = (335874283178:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3164+point 2 split 4096 3165)/2 = (521880499:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((521880499:ℝ)/168755200)/ClassicalSixthBranch.v ((521880499:ℝ)/168755200) = (569356055331:ℝ)/268657498072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3164
  · change lowerPayment 3165 ≤ lowerValue ((point 2 split 4096 3165+point 2 split 4096 3166)/2)
    have hp : lowerPayment 3165 = (335963761717:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3165+point 2 split 4096 3166)/2 = (521938761:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((521938761:ℝ)/168755200)/ClassicalSixthBranch.v ((521938761:ℝ)/168755200) = (569278741657:ℝ)/268609490184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3165
  · change lowerPayment 3166 ≤ lowerValue ((point 2 split 4096 3166+point 2 split 4096 3167)/2)
    have hp : lowerPayment 3166 = (336053247267:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3166+point 2 split 4096 3167)/2 = (521997023:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((521997023:ℝ)/168755200)/ClassicalSixthBranch.v ((521997023:ℝ)/168755200) = (569201427983:ℝ)/268561482296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3166
  · change lowerPayment 3167 ≤ lowerValue ((point 2 split 4096 3167+point 2 split 4096 3168)/2)
    have hp : lowerPayment 3167 = (336142739844:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3167+point 2 split 4096 3168)/2 = (104411057:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((104411057:ℝ)/33751040)/ClassicalSixthBranch.v ((104411057:ℝ)/33751040) = (569124114309:ℝ)/268513474408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3167
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_197
