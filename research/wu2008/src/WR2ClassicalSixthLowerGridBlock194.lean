import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints194
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_194 (j : Fin 16) : lowerPayment (16*194+j.val) ≤
    lowerValue ((point 2 split 4096 (16*194+j.val)+point 2 split 4096 (16*194+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3104 ≤ lowerValue ((point 2 split 4096 3104+point 2 split 4096 3105)/2)
    have hp : lowerPayment 3104 = (330517857601:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3104+point 2 split 4096 3105)/2 = (518384779:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((518384779:ℝ)/168755200)/ClassicalSixthBranch.v ((518384779:ℝ)/168755200) = (573994875771:ℝ)/271537971352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3104
  · change lowerPayment 3105 ≤ lowerValue ((point 2 split 4096 3105+point 2 split 4096 3106)/2)
    have hp : lowerPayment 3105 = (330606941767:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3105+point 2 split 4096 3106)/2 = (518443041:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((518443041:ℝ)/168755200)/ClassicalSixthBranch.v ((518443041:ℝ)/168755200) = (573917562097:ℝ)/271489963464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3105
  · change lowerPayment 3106 ≤ lowerValue ((point 2 split 4096 3106+point 2 split 4096 3107)/2)
    have hp : lowerPayment 3106 = (330696032083:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3106+point 2 split 4096 3107)/2 = (518501303:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((518501303:ℝ)/168755200)/ClassicalSixthBranch.v ((518501303:ℝ)/168755200) = (573840248423:ℝ)/271441955576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3106
  · change lowerPayment 3107 ≤ lowerValue ((point 2 split 4096 3107+point 2 split 4096 3108)/2)
    have hp : lowerPayment 3107 = (330785128564:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3107+point 2 split 4096 3108)/2 = (103711913:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((103711913:ℝ)/33751040)/ClassicalSixthBranch.v ((103711913:ℝ)/33751040) = (573762934749:ℝ)/271393947688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3107
  · change lowerPayment 3108 ≤ lowerValue ((point 2 split 4096 3108+point 2 split 4096 3109)/2)
    have hp : lowerPayment 3108 = (330874231222:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3108+point 2 split 4096 3109)/2 = (518617827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((518617827:ℝ)/168755200)/ClassicalSixthBranch.v ((518617827:ℝ)/168755200) = (22947424843:ℝ)/10853837592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3108
  · change lowerPayment 3109 ≤ lowerValue ((point 2 split 4096 3109+point 2 split 4096 3110)/2)
    have hp : lowerPayment 3109 = (330963340074:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3109+point 2 split 4096 3110)/2 = (518676089:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((518676089:ℝ)/168755200)/ClassicalSixthBranch.v ((518676089:ℝ)/168755200) = (573608307401:ℝ)/271297931912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3109
  · change lowerPayment 3110 ≤ lowerValue ((point 2 split 4096 3110+point 2 split 4096 3111)/2)
    have hp : lowerPayment 3110 = (331052455132:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3110+point 2 split 4096 3111)/2 = (518734351:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((518734351:ℝ)/168755200)/ClassicalSixthBranch.v ((518734351:ℝ)/168755200) = (573530993727:ℝ)/271249924024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3110
  · change lowerPayment 3111 ≤ lowerValue ((point 2 split 4096 3111+point 2 split 4096 3112)/2)
    have hp : lowerPayment 3111 = (331141576412:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3111+point 2 split 4096 3112)/2 = (518792613:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((518792613:ℝ)/168755200)/ClassicalSixthBranch.v ((518792613:ℝ)/168755200) = (573453680053:ℝ)/271201916136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3111
  · change lowerPayment 3112 ≤ lowerValue ((point 2 split 4096 3112+point 2 split 4096 3113)/2)
    have hp : lowerPayment 3112 = (331230703927:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3112+point 2 split 4096 3113)/2 = (20754035:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((20754035:ℝ)/6750208)/ClassicalSixthBranch.v ((20754035:ℝ)/6750208) = (573376366379:ℝ)/271153908248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3112
  · change lowerPayment 3113 ≤ lowerValue ((point 2 split 4096 3113+point 2 split 4096 3114)/2)
    have hp : lowerPayment 3113 = (331319837693:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3113+point 2 split 4096 3114)/2 = (518909137:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((518909137:ℝ)/168755200)/ClassicalSixthBranch.v ((518909137:ℝ)/168755200) = (114659810541:ℝ)/54221180072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3113
  · change lowerPayment 3114 ≤ lowerValue ((point 2 split 4096 3114+point 2 split 4096 3115)/2)
    have hp : lowerPayment 3114 = (331408977723:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3114+point 2 split 4096 3115)/2 = (518967399:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((518967399:ℝ)/168755200)/ClassicalSixthBranch.v ((518967399:ℝ)/168755200) = (573221739031:ℝ)/271057892472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3114
  · change lowerPayment 3115 ≤ lowerValue ((point 2 split 4096 3115+point 2 split 4096 3116)/2)
    have hp : lowerPayment 3115 = (331498124031:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3115+point 2 split 4096 3116)/2 = (519025661:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((519025661:ℝ)/168755200)/ClassicalSixthBranch.v ((519025661:ℝ)/168755200) = (573144425357:ℝ)/271009884584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3115
  · change lowerPayment 3116 ≤ lowerValue ((point 2 split 4096 3116+point 2 split 4096 3117)/2)
    have hp : lowerPayment 3116 = (331587276632:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3116+point 2 split 4096 3117)/2 = (519083923:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((519083923:ℝ)/168755200)/ClassicalSixthBranch.v ((519083923:ℝ)/168755200) = (573067111683:ℝ)/270961876696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3116
  · change lowerPayment 3117 ≤ lowerValue ((point 2 split 4096 3117+point 2 split 4096 3118)/2)
    have hp : lowerPayment 3117 = (331676435541:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3117+point 2 split 4096 3118)/2 = (103828437:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((103828437:ℝ)/33751040)/ClassicalSixthBranch.v ((103828437:ℝ)/33751040) = (572989798009:ℝ)/270913868808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3117
  · change lowerPayment 3118 ≤ lowerValue ((point 2 split 4096 3118+point 2 split 4096 3119)/2)
    have hp : lowerPayment 3118 = (331765600771:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3118+point 2 split 4096 3119)/2 = (519200447:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((519200447:ℝ)/168755200)/ClassicalSixthBranch.v ((519200447:ℝ)/168755200) = (114582496867:ℝ)/54173172184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3118
  · change lowerPayment 3119 ≤ lowerValue ((point 2 split 4096 3119+point 2 split 4096 3120)/2)
    have hp : lowerPayment 3119 = (331854772337:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3119+point 2 split 4096 3120)/2 = (519258709:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((519258709:ℝ)/168755200)/ClassicalSixthBranch.v ((519258709:ℝ)/168755200) = (572835170661:ℝ)/270817853032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3119
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_194
