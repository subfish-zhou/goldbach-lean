import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints068
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_068 (j : Fin 16) : lowerPayment (16*68+j.val) ≤
    lowerValue ((point 2 split 4096 (16*68+j.val)+point 2 split 4096 (16*68+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1088 ≤ lowerValue ((point 2 split 4096 1088+point 2 split 4096 1089)/2)
    have hp : lowerPayment 1088 = (143064167563:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1088+point 2 split 4096 1089)/2 = (400928587:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((400928587:ℝ)/168755200)/ClassicalSixthBranch.v ((400928587:ℝ)/168755200) = (145971848511:ℝ)/73664374712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1088
  · change lowerPayment 1089 ≤ lowerValue ((point 2 split 4096 1089+point 2 split 4096 1090)/2)
    have hp : lowerPayment 1089 = (143172595698:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1089+point 2 split 4096 1090)/2 = (400986849:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((400986849:ℝ)/168755200)/ClassicalSixthBranch.v ((400986849:ℝ)/168755200) = (729781928881:ℝ)/368273865672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1089
  · change lowerPayment 1090 ≤ lowerValue ((point 2 split 4096 1090+point 2 split 4096 1091)/2)
    have hp : lowerPayment 1090 = (143280994296:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1090+point 2 split 4096 1091)/2 = (401045111:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((401045111:ℝ)/168755200)/ClassicalSixthBranch.v ((401045111:ℝ)/168755200) = (729704615207:ℝ)/368225857784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1090
  · change lowerPayment 1091 ≤ lowerValue ((point 2 split 4096 1091+point 2 split 4096 1092)/2)
    have hp : lowerPayment 1091 = (143389363386:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1091+point 2 split 4096 1092)/2 = (401103373:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((401103373:ℝ)/168755200)/ClassicalSixthBranch.v ((401103373:ℝ)/168755200) = (729627301533:ℝ)/368177849896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1091
  · change lowerPayment 1092 ≤ lowerValue ((point 2 split 4096 1092+point 2 split 4096 1093)/2)
    have hp : lowerPayment 1092 = (143497702995:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1092+point 2 split 4096 1093)/2 = (80232327:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((80232327:ℝ)/33751040)/ClassicalSixthBranch.v ((80232327:ℝ)/33751040) = (729549987859:ℝ)/368129842008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1092
  · change lowerPayment 1093 ≤ lowerValue ((point 2 split 4096 1093+point 2 split 4096 1094)/2)
    have hp : lowerPayment 1093 = (143606013150:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1093+point 2 split 4096 1094)/2 = (401219897:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((401219897:ℝ)/168755200)/ClassicalSixthBranch.v ((401219897:ℝ)/168755200) = (145894534837:ℝ)/73616366824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1093
  · change lowerPayment 1094 ≤ lowerValue ((point 2 split 4096 1094+point 2 split 4096 1095)/2)
    have hp : lowerPayment 1094 = (143714293880:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1094+point 2 split 4096 1095)/2 = (401278159:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((401278159:ℝ)/168755200)/ClassicalSixthBranch.v ((401278159:ℝ)/168755200) = (729395360511:ℝ)/368033826232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1094
  · change lowerPayment 1095 ≤ lowerValue ((point 2 split 4096 1095+point 2 split 4096 1096)/2)
    have hp : lowerPayment 1095 = (143822545212:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1095+point 2 split 4096 1096)/2 = (401336421:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((401336421:ℝ)/168755200)/ClassicalSixthBranch.v ((401336421:ℝ)/168755200) = (729318046837:ℝ)/367985818344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1095
  · change lowerPayment 1096 ≤ lowerValue ((point 2 split 4096 1096+point 2 split 4096 1097)/2)
    have hp : lowerPayment 1096 = (143930767174:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1096+point 2 split 4096 1097)/2 = (401394683:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((401394683:ℝ)/168755200)/ClassicalSixthBranch.v ((401394683:ℝ)/168755200) = (729240733163:ℝ)/367937810456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1096
  · change lowerPayment 1097 ≤ lowerValue ((point 2 split 4096 1097+point 2 split 4096 1098)/2)
    have hp : lowerPayment 1097 = (144038959793:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1097+point 2 split 4096 1098)/2 = (80290589:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((80290589:ℝ)/33751040)/ClassicalSixthBranch.v ((80290589:ℝ)/33751040) = (729163419489:ℝ)/367889802568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1097
  · change lowerPayment 1098 ≤ lowerValue ((point 2 split 4096 1098+point 2 split 4096 1099)/2)
    have hp : lowerPayment 1098 = (144147123097:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1098+point 2 split 4096 1099)/2 = (401511207:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((401511207:ℝ)/168755200)/ClassicalSixthBranch.v ((401511207:ℝ)/168755200) = (145817221163:ℝ)/73568358936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1098
  · change lowerPayment 1099 ≤ lowerValue ((point 2 split 4096 1099+point 2 split 4096 1100)/2)
    have hp : lowerPayment 1099 = (144255257114:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1099+point 2 split 4096 1100)/2 = (401569469:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((401569469:ℝ)/168755200)/ClassicalSixthBranch.v ((401569469:ℝ)/168755200) = (729008792141:ℝ)/367793786792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1099
  · change lowerPayment 1100 ≤ lowerValue ((point 2 split 4096 1100+point 2 split 4096 1101)/2)
    have hp : lowerPayment 1100 = (144363361870:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1100+point 2 split 4096 1101)/2 = (401627731:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((401627731:ℝ)/168755200)/ClassicalSixthBranch.v ((401627731:ℝ)/168755200) = (728931478467:ℝ)/367745778904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1100
  · change lowerPayment 1101 ≤ lowerValue ((point 2 split 4096 1101+point 2 split 4096 1102)/2)
    have hp : lowerPayment 1101 = (144471437395:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1101+point 2 split 4096 1102)/2 = (401685993:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((401685993:ℝ)/168755200)/ClassicalSixthBranch.v ((401685993:ℝ)/168755200) = (728854164793:ℝ)/367697771016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1101
  · change lowerPayment 1102 ≤ lowerValue ((point 2 split 4096 1102+point 2 split 4096 1103)/2)
    have hp : lowerPayment 1102 = (144579483715:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1102+point 2 split 4096 1103)/2 = (80348851:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((80348851:ℝ)/33751040)/ClassicalSixthBranch.v ((80348851:ℝ)/33751040) = (728776851119:ℝ)/367649763128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1102
  · change lowerPayment 1103 ≤ lowerValue ((point 2 split 4096 1103+point 2 split 4096 1104)/2)
    have hp : lowerPayment 1103 = (144687500857:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1103+point 2 split 4096 1104)/2 = (401802517:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((401802517:ℝ)/168755200)/ClassicalSixthBranch.v ((401802517:ℝ)/168755200) = (145739907489:ℝ)/73520351048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1103
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_068
