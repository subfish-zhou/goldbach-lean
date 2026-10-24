import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints195
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_195 (j : Fin 16) : lowerPayment (16*195+j.val) ≤
    lowerValue ((point 2 split 4096 (16*195+j.val)+point 2 split 4096 (16*195+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3120 ≤ lowerValue ((point 2 split 4096 3120+point 2 split 4096 3121)/2)
    have hp : lowerPayment 3120 = (331943950254:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3120+point 2 split 4096 3121)/2 = (519316971:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((519316971:ℝ)/168755200)/ClassicalSixthBranch.v ((519316971:ℝ)/168755200) = (572757856987:ℝ)/270769845144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3120
  · change lowerPayment 3121 ≤ lowerValue ((point 2 split 4096 3121+point 2 split 4096 3122)/2)
    have hp : lowerPayment 3121 = (332033134535:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3121+point 2 split 4096 3122)/2 = (519375233:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((519375233:ℝ)/168755200)/ClassicalSixthBranch.v ((519375233:ℝ)/168755200) = (572680543313:ℝ)/270721837256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3121
  · change lowerPayment 3122 ≤ lowerValue ((point 2 split 4096 3122+point 2 split 4096 3123)/2)
    have hp : lowerPayment 3122 = (332122325194:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3122+point 2 split 4096 3123)/2 = (103886699:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((103886699:ℝ)/33751040)/ClassicalSixthBranch.v ((103886699:ℝ)/33751040) = (572603229639:ℝ)/270673829368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3122
  · change lowerPayment 3123 ≤ lowerValue ((point 2 split 4096 3123+point 2 split 4096 3124)/2)
    have hp : lowerPayment 3123 = (332211522248:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3123+point 2 split 4096 3124)/2 = (519491757:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((519491757:ℝ)/168755200)/ClassicalSixthBranch.v ((519491757:ℝ)/168755200) = (114505183193:ℝ)/54125164296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3123
  · change lowerPayment 3124 ≤ lowerValue ((point 2 split 4096 3124+point 2 split 4096 3125)/2)
    have hp : lowerPayment 3124 = (332300725708:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3124+point 2 split 4096 3125)/2 = (519550019:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((519550019:ℝ)/168755200)/ClassicalSixthBranch.v ((519550019:ℝ)/168755200) = (572448602291:ℝ)/270577813592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3124
  · change lowerPayment 3125 ≤ lowerValue ((point 2 split 4096 3125+point 2 split 4096 3126)/2)
    have hp : lowerPayment 3125 = (332389935591:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3125+point 2 split 4096 3126)/2 = (519608281:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((519608281:ℝ)/168755200)/ClassicalSixthBranch.v ((519608281:ℝ)/168755200) = (572371288617:ℝ)/270529805704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3125
  · change lowerPayment 3126 ≤ lowerValue ((point 2 split 4096 3126+point 2 split 4096 3127)/2)
    have hp : lowerPayment 3126 = (332479151910:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3126+point 2 split 4096 3127)/2 = (519666543:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((519666543:ℝ)/168755200)/ClassicalSixthBranch.v ((519666543:ℝ)/168755200) = (572293974943:ℝ)/270481797816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3126
  · change lowerPayment 3127 ≤ lowerValue ((point 2 split 4096 3127+point 2 split 4096 3128)/2)
    have hp : lowerPayment 3127 = (332568374679:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3127+point 2 split 4096 3128)/2 = (103944961:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((103944961:ℝ)/33751040)/ClassicalSixthBranch.v ((103944961:ℝ)/33751040) = (572216661269:ℝ)/270433789928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3127
  · change lowerPayment 3128 ≤ lowerValue ((point 2 split 4096 3128+point 2 split 4096 3129)/2)
    have hp : lowerPayment 3128 = (332657603914:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3128+point 2 split 4096 3129)/2 = (519783067:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((519783067:ℝ)/168755200)/ClassicalSixthBranch.v ((519783067:ℝ)/168755200) = (114427869519:ℝ)/54077156408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3128
  · change lowerPayment 3129 ≤ lowerValue ((point 2 split 4096 3129+point 2 split 4096 3130)/2)
    have hp : lowerPayment 3129 = (332746839628:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3129+point 2 split 4096 3130)/2 = (519841329:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((519841329:ℝ)/168755200)/ClassicalSixthBranch.v ((519841329:ℝ)/168755200) = (572062033921:ℝ)/270337774152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3129
  · change lowerPayment 3130 ≤ lowerValue ((point 2 split 4096 3130+point 2 split 4096 3131)/2)
    have hp : lowerPayment 3130 = (332836081835:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3130+point 2 split 4096 3131)/2 = (519899591:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((519899591:ℝ)/168755200)/ClassicalSixthBranch.v ((519899591:ℝ)/168755200) = (571984720247:ℝ)/270289766264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3130
  · change lowerPayment 3131 ≤ lowerValue ((point 2 split 4096 3131+point 2 split 4096 3132)/2)
    have hp : lowerPayment 3131 = (332925330551:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3131+point 2 split 4096 3132)/2 = (519957853:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((519957853:ℝ)/168755200)/ClassicalSixthBranch.v ((519957853:ℝ)/168755200) = (571907406573:ℝ)/270241758376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3131
  · change lowerPayment 3132 ≤ lowerValue ((point 2 split 4096 3132+point 2 split 4096 3133)/2)
    have hp : lowerPayment 3132 = (333014585789:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3132+point 2 split 4096 3133)/2 = (104003223:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((104003223:ℝ)/33751040)/ClassicalSixthBranch.v ((104003223:ℝ)/33751040) = (571830092899:ℝ)/270193750488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3132
  · change lowerPayment 3133 ≤ lowerValue ((point 2 split 4096 3133+point 2 split 4096 3134)/2)
    have hp : lowerPayment 3133 = (333103847563:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3133+point 2 split 4096 3134)/2 = (520074377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((520074377:ℝ)/168755200)/ClassicalSixthBranch.v ((520074377:ℝ)/168755200) = (22870111169:ℝ)/10805829704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3133
  · change lowerPayment 3134 ≤ lowerValue ((point 2 split 4096 3134+point 2 split 4096 3135)/2)
    have hp : lowerPayment 3134 = (333193115889:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3134+point 2 split 4096 3135)/2 = (520132639:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((520132639:ℝ)/168755200)/ClassicalSixthBranch.v ((520132639:ℝ)/168755200) = (571675465551:ℝ)/270097734712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3134
  · change lowerPayment 3135 ≤ lowerValue ((point 2 split 4096 3135+point 2 split 4096 3136)/2)
    have hp : lowerPayment 3135 = (333282390780:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3135+point 2 split 4096 3136)/2 = (520190901:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((520190901:ℝ)/168755200)/ClassicalSixthBranch.v ((520190901:ℝ)/168755200) = (571598151877:ℝ)/270049726824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3135
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_195
