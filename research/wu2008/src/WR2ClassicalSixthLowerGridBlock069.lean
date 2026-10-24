import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints069
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_069 (j : Fin 16) : lowerPayment (16*69+j.val) ≤
    lowerValue ((point 2 split 4096 (16*69+j.val)+point 2 split 4096 (16*69+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1104 ≤ lowerValue ((point 2 split 4096 1104+point 2 split 4096 1105)/2)
    have hp : lowerPayment 1104 = (144795488850:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1104+point 2 split 4096 1105)/2 = (401860779:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((401860779:ℝ)/168755200)/ClassicalSixthBranch.v ((401860779:ℝ)/168755200) = (728622223771:ℝ)/367553747352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1104
  · change lowerPayment 1105 ≤ lowerValue ((point 2 split 4096 1105+point 2 split 4096 1106)/2)
    have hp : lowerPayment 1105 = (144903447721:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1105+point 2 split 4096 1106)/2 = (401919041:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((401919041:ℝ)/168755200)/ClassicalSixthBranch.v ((401919041:ℝ)/168755200) = (728544910097:ℝ)/367505739464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1105
  · change lowerPayment 1106 ≤ lowerValue ((point 2 split 4096 1106+point 2 split 4096 1107)/2)
    have hp : lowerPayment 1106 = (145011377497:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1106+point 2 split 4096 1107)/2 = (401977303:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((401977303:ℝ)/168755200)/ClassicalSixthBranch.v ((401977303:ℝ)/168755200) = (728467596423:ℝ)/367457731576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1106
  · change lowerPayment 1107 ≤ lowerValue ((point 2 split 4096 1107+point 2 split 4096 1108)/2)
    have hp : lowerPayment 1107 = (145119278205:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1107+point 2 split 4096 1108)/2 = (80407113:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((80407113:ℝ)/33751040)/ClassicalSixthBranch.v ((80407113:ℝ)/33751040) = (728390282749:ℝ)/367409723688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1107
  · change lowerPayment 1108 ≤ lowerValue ((point 2 split 4096 1108+point 2 split 4096 1109)/2)
    have hp : lowerPayment 1108 = (145227149874:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1108+point 2 split 4096 1109)/2 = (402093827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((402093827:ℝ)/168755200)/ClassicalSixthBranch.v ((402093827:ℝ)/168755200) = (29132518763:ℝ)/14694468632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1108
  · change lowerPayment 1109 ≤ lowerValue ((point 2 split 4096 1109+point 2 split 4096 1110)/2)
    have hp : lowerPayment 1109 = (145334992530:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1109+point 2 split 4096 1110)/2 = (402152089:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((402152089:ℝ)/168755200)/ClassicalSixthBranch.v ((402152089:ℝ)/168755200) = (728235655401:ℝ)/367313707912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1109
  · change lowerPayment 1110 ≤ lowerValue ((point 2 split 4096 1110+point 2 split 4096 1111)/2)
    have hp : lowerPayment 1110 = (145442806201:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1110+point 2 split 4096 1111)/2 = (402210351:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((402210351:ℝ)/168755200)/ClassicalSixthBranch.v ((402210351:ℝ)/168755200) = (728158341727:ℝ)/367265700024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1110
  · change lowerPayment 1111 ≤ lowerValue ((point 2 split 4096 1111+point 2 split 4096 1112)/2)
    have hp : lowerPayment 1111 = (145550590915:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1111+point 2 split 4096 1112)/2 = (402268613:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((402268613:ℝ)/168755200)/ClassicalSixthBranch.v ((402268613:ℝ)/168755200) = (728081028053:ℝ)/367217692136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1111
  · change lowerPayment 1112 ≤ lowerValue ((point 2 split 4096 1112+point 2 split 4096 1113)/2)
    have hp : lowerPayment 1112 = (145658346698:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1112+point 2 split 4096 1113)/2 = (16093075:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((16093075:ℝ)/6750208)/ClassicalSixthBranch.v ((16093075:ℝ)/6750208) = (728003714379:ℝ)/367169684248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1112
  · change lowerPayment 1113 ≤ lowerValue ((point 2 split 4096 1113+point 2 split 4096 1114)/2)
    have hp : lowerPayment 1113 = (145766073578:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1113+point 2 split 4096 1114)/2 = (402385137:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((402385137:ℝ)/168755200)/ClassicalSixthBranch.v ((402385137:ℝ)/168755200) = (145585280141:ℝ)/73424335272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1113
  · change lowerPayment 1114 ≤ lowerValue ((point 2 split 4096 1114+point 2 split 4096 1115)/2)
    have hp : lowerPayment 1114 = (145873771582:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1114+point 2 split 4096 1115)/2 = (402443399:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((402443399:ℝ)/168755200)/ClassicalSixthBranch.v ((402443399:ℝ)/168755200) = (727849087031:ℝ)/367073668472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1114
  · change lowerPayment 1115 ≤ lowerValue ((point 2 split 4096 1115+point 2 split 4096 1116)/2)
    have hp : lowerPayment 1115 = (145981440738:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1115+point 2 split 4096 1116)/2 = (402501661:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((402501661:ℝ)/168755200)/ClassicalSixthBranch.v ((402501661:ℝ)/168755200) = (727771773357:ℝ)/367025660584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1115
  · change lowerPayment 1116 ≤ lowerValue ((point 2 split 4096 1116+point 2 split 4096 1117)/2)
    have hp : lowerPayment 1116 = (146089081072:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1116+point 2 split 4096 1117)/2 = (402559923:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((402559923:ℝ)/168755200)/ClassicalSixthBranch.v ((402559923:ℝ)/168755200) = (727694459683:ℝ)/366977652696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1116
  · change lowerPayment 1117 ≤ lowerValue ((point 2 split 4096 1117+point 2 split 4096 1118)/2)
    have hp : lowerPayment 1117 = (146196692613:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1117+point 2 split 4096 1118)/2 = (80523637:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((80523637:ℝ)/33751040)/ClassicalSixthBranch.v ((80523637:ℝ)/33751040) = (727617146009:ℝ)/366929644808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1117
  · change lowerPayment 1118 ≤ lowerValue ((point 2 split 4096 1118+point 2 split 4096 1119)/2)
    have hp : lowerPayment 1118 = (146304275387:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1118+point 2 split 4096 1119)/2 = (402676447:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((402676447:ℝ)/168755200)/ClassicalSixthBranch.v ((402676447:ℝ)/168755200) = (145507966467:ℝ)/73376327384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1118
  · change lowerPayment 1119 ≤ lowerValue ((point 2 split 4096 1119+point 2 split 4096 1120)/2)
    have hp : lowerPayment 1119 = (146411829422:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1119+point 2 split 4096 1120)/2 = (402734709:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((402734709:ℝ)/168755200)/ClassicalSixthBranch.v ((402734709:ℝ)/168755200) = (727462518661:ℝ)/366833629032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1119
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_069
