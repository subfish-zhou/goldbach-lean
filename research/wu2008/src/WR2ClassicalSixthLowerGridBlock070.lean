import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints070
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_070 (j : Fin 16) : lowerPayment (16*70+j.val) ≤
    lowerValue ((point 2 split 4096 (16*70+j.val)+point 2 split 4096 (16*70+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1120 ≤ lowerValue ((point 2 split 4096 1120+point 2 split 4096 1121)/2)
    have hp : lowerPayment 1120 = (146519354744:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1120+point 2 split 4096 1121)/2 = (402792971:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((402792971:ℝ)/168755200)/ClassicalSixthBranch.v ((402792971:ℝ)/168755200) = (727385204987:ℝ)/366785621144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1120
  · change lowerPayment 1121 ≤ lowerValue ((point 2 split 4096 1121+point 2 split 4096 1122)/2)
    have hp : lowerPayment 1121 = (146626851381:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1121+point 2 split 4096 1122)/2 = (402851233:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((402851233:ℝ)/168755200)/ClassicalSixthBranch.v ((402851233:ℝ)/168755200) = (727307891313:ℝ)/366737613256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1121
  · change lowerPayment 1122 ≤ lowerValue ((point 2 split 4096 1122+point 2 split 4096 1123)/2)
    have hp : lowerPayment 1122 = (146734319360:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1122+point 2 split 4096 1123)/2 = (80581899:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((80581899:ℝ)/33751040)/ClassicalSixthBranch.v ((80581899:ℝ)/33751040) = (727230577639:ℝ)/366689605368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1122
  · change lowerPayment 1123 ≤ lowerValue ((point 2 split 4096 1123+point 2 split 4096 1124)/2)
    have hp : lowerPayment 1123 = (146841758708:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1123+point 2 split 4096 1124)/2 = (402967757:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((402967757:ℝ)/168755200)/ClassicalSixthBranch.v ((402967757:ℝ)/168755200) = (145430652793:ℝ)/73328319496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1123
  · change lowerPayment 1124 ≤ lowerValue ((point 2 split 4096 1124+point 2 split 4096 1125)/2)
    have hp : lowerPayment 1124 = (146949169453:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1124+point 2 split 4096 1125)/2 = (403026019:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((403026019:ℝ)/168755200)/ClassicalSixthBranch.v ((403026019:ℝ)/168755200) = (727075950291:ℝ)/366593589592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1124
  · change lowerPayment 1125 ≤ lowerValue ((point 2 split 4096 1125+point 2 split 4096 1126)/2)
    have hp : lowerPayment 1125 = (147056551621:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1125+point 2 split 4096 1126)/2 = (403084281:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((403084281:ℝ)/168755200)/ClassicalSixthBranch.v ((403084281:ℝ)/168755200) = (726998636617:ℝ)/366545581704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1125
  · change lowerPayment 1126 ≤ lowerValue ((point 2 split 4096 1126+point 2 split 4096 1127)/2)
    have hp : lowerPayment 1126 = (147163905239:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1126+point 2 split 4096 1127)/2 = (403142543:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((403142543:ℝ)/168755200)/ClassicalSixthBranch.v ((403142543:ℝ)/168755200) = (726921322943:ℝ)/366497573816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1126
  · change lowerPayment 1127 ≤ lowerValue ((point 2 split 4096 1127+point 2 split 4096 1128)/2)
    have hp : lowerPayment 1127 = (147271230335:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1127+point 2 split 4096 1128)/2 = (80640161:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((80640161:ℝ)/33751040)/ClassicalSixthBranch.v ((80640161:ℝ)/33751040) = (726844009269:ℝ)/366449565928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1127
  · change lowerPayment 1128 ≤ lowerValue ((point 2 split 4096 1128+point 2 split 4096 1129)/2)
    have hp : lowerPayment 1128 = (147378526936:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1128+point 2 split 4096 1129)/2 = (403259067:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((403259067:ℝ)/168755200)/ClassicalSixthBranch.v ((403259067:ℝ)/168755200) = (145353339119:ℝ)/73280311608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1128
  · change lowerPayment 1129 ≤ lowerValue ((point 2 split 4096 1129+point 2 split 4096 1130)/2)
    have hp : lowerPayment 1129 = (147485795068:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1129+point 2 split 4096 1130)/2 = (403317329:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((403317329:ℝ)/168755200)/ClassicalSixthBranch.v ((403317329:ℝ)/168755200) = (726689381921:ℝ)/366353550152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1129
  · change lowerPayment 1130 ≤ lowerValue ((point 2 split 4096 1130+point 2 split 4096 1131)/2)
    have hp : lowerPayment 1130 = (147593034759:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1130+point 2 split 4096 1131)/2 = (403375591:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((403375591:ℝ)/168755200)/ClassicalSixthBranch.v ((403375591:ℝ)/168755200) = (726612068247:ℝ)/366305542264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1130
  · change lowerPayment 1131 ≤ lowerValue ((point 2 split 4096 1131+point 2 split 4096 1132)/2)
    have hp : lowerPayment 1131 = (147700246035:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1131+point 2 split 4096 1132)/2 = (403433853:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((403433853:ℝ)/168755200)/ClassicalSixthBranch.v ((403433853:ℝ)/168755200) = (726534754573:ℝ)/366257534376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1131
  · change lowerPayment 1132 ≤ lowerValue ((point 2 split 4096 1132+point 2 split 4096 1133)/2)
    have hp : lowerPayment 1132 = (147807428924:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1132+point 2 split 4096 1133)/2 = (80698423:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((80698423:ℝ)/33751040)/ClassicalSixthBranch.v ((80698423:ℝ)/33751040) = (726457440899:ℝ)/366209526488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1132
  · change lowerPayment 1133 ≤ lowerValue ((point 2 split 4096 1133+point 2 split 4096 1134)/2)
    have hp : lowerPayment 1133 = (147914583452:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1133+point 2 split 4096 1134)/2 = (403550377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((403550377:ℝ)/168755200)/ClassicalSixthBranch.v ((403550377:ℝ)/168755200) = (29055205089:ℝ)/14646460744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1133
  · change lowerPayment 1134 ≤ lowerValue ((point 2 split 4096 1134+point 2 split 4096 1135)/2)
    have hp : lowerPayment 1134 = (148021709647:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1134+point 2 split 4096 1135)/2 = (403608639:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((403608639:ℝ)/168755200)/ClassicalSixthBranch.v ((403608639:ℝ)/168755200) = (726302813551:ℝ)/366113510712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1134
  · change lowerPayment 1135 ≤ lowerValue ((point 2 split 4096 1135+point 2 split 4096 1136)/2)
    have hp : lowerPayment 1135 = (148128807535:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1135+point 2 split 4096 1136)/2 = (403666901:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((403666901:ℝ)/168755200)/ClassicalSixthBranch.v ((403666901:ℝ)/168755200) = (726225499877:ℝ)/366065502824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1135
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_070
