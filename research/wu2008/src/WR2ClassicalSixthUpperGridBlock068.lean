import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints068
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_068 (j : Fin 16) : upperPayment (16*68+j.val) ≤
    upperValue ((point split endpoint 4096 (16*68+j.val)+point split endpoint 4096 (16*68+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1088 ≤ upperValue ((point split endpoint 4096 1088+point split endpoint 4096 1089)/2)
    have hp : upperPayment 1088 = (353531294411:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1088+point split endpoint 4096 1089)/2 = (603527327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603527327:ℝ)/168755200)*ClassicalSixthBranch.v ((603527327:ℝ)/168755200)/ClassicalSixthBranch.r = (135847079910737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1088
  · change upperPayment 1089 ≤ upperValue ((point split endpoint 4096 1089+point split endpoint 4096 1090)/2)
    have hp : upperPayment 1089 = (353454758459:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1089+point split endpoint 4096 1090)/2 = (603552477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603552477:ℝ)/168755200)*ClassicalSixthBranch.v ((603552477:ℝ)/168755200)/ClassicalSixthBranch.r = (135823266808281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1089
  · change upperPayment 1090 ≤ upperValue ((point split endpoint 4096 1090+point split endpoint 4096 1091)/2)
    have hp : upperPayment 1090 = (353378200220:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1090+point split endpoint 4096 1091)/2 = (603577627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603577627:ℝ)/168755200)*ClassicalSixthBranch.v ((603577627:ℝ)/168755200)/ClassicalSixthBranch.r = (135799455729897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1090
  · change upperPayment 1091 ≤ upperValue ((point split endpoint 4096 1091+point split endpoint 4096 1092)/2)
    have hp : upperPayment 1091 = (353301619692:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1091+point split endpoint 4096 1092)/2 = (603602777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603602777:ℝ)/168755200)*ClassicalSixthBranch.v ((603602777:ℝ)/168755200)/ClassicalSixthBranch.r = (135775646675585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1091
  · change upperPayment 1092 ≤ upperValue ((point split endpoint 4096 1092+point split endpoint 4096 1093)/2)
    have hp : upperPayment 1092 = (353225016870:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1092+point split endpoint 4096 1093)/2 = (603627927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603627927:ℝ)/168755200)*ClassicalSixthBranch.v ((603627927:ℝ)/168755200)/ClassicalSixthBranch.r = (135751839645345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1092
  · change upperPayment 1093 ≤ upperValue ((point split endpoint 4096 1093+point split endpoint 4096 1094)/2)
    have hp : upperPayment 1093 = (353148391752:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1093+point split endpoint 4096 1094)/2 = (603653077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603653077:ℝ)/168755200)*ClassicalSixthBranch.v ((603653077:ℝ)/168755200)/ClassicalSixthBranch.r = (135728034639177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1093
  · change upperPayment 1094 ≤ upperValue ((point split endpoint 4096 1094+point split endpoint 4096 1095)/2)
    have hp : upperPayment 1094 = (353071744333:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1094+point split endpoint 4096 1095)/2 = (603678227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603678227:ℝ)/168755200)*ClassicalSixthBranch.v ((603678227:ℝ)/168755200)/ClassicalSixthBranch.r = (135704231657081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1094
  · change upperPayment 1095 ≤ upperValue ((point split endpoint 4096 1095+point split endpoint 4096 1096)/2)
    have hp : upperPayment 1095 = (352995074609:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1095+point split endpoint 4096 1096)/2 = (603703377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603703377:ℝ)/168755200)*ClassicalSixthBranch.v ((603703377:ℝ)/168755200)/ClassicalSixthBranch.r = (135680430699057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1095
  · change upperPayment 1096 ≤ upperValue ((point split endpoint 4096 1096+point split endpoint 4096 1097)/2)
    have hp : upperPayment 1096 = (352918382579:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1096+point split endpoint 4096 1097)/2 = (603728527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603728527:ℝ)/168755200)*ClassicalSixthBranch.v ((603728527:ℝ)/168755200)/ClassicalSixthBranch.r = (135656631765105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1096
  · change upperPayment 1097 ≤ upperValue ((point split endpoint 4096 1097+point split endpoint 4096 1098)/2)
    have hp : upperPayment 1097 = (352841668237:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1097+point split endpoint 4096 1098)/2 = (603753677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603753677:ℝ)/168755200)*ClassicalSixthBranch.v ((603753677:ℝ)/168755200)/ClassicalSixthBranch.r = (135632834855225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1097
  · change upperPayment 1098 ≤ upperValue ((point split endpoint 4096 1098+point split endpoint 4096 1099)/2)
    have hp : upperPayment 1098 = (352764931580:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1098+point split endpoint 4096 1099)/2 = (603778827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603778827:ℝ)/168755200)*ClassicalSixthBranch.v ((603778827:ℝ)/168755200)/ClassicalSixthBranch.r = (135609039969417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1098
  · change upperPayment 1099 ≤ upperValue ((point split endpoint 4096 1099+point split endpoint 4096 1100)/2)
    have hp : upperPayment 1099 = (352688172605:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1099+point split endpoint 4096 1100)/2 = (603803977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603803977:ℝ)/168755200)*ClassicalSixthBranch.v ((603803977:ℝ)/168755200)/ClassicalSixthBranch.r = (135585247107681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1099
  · change upperPayment 1100 ≤ upperValue ((point split endpoint 4096 1100+point split endpoint 4096 1101)/2)
    have hp : upperPayment 1100 = (352611391308:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1100+point split endpoint 4096 1101)/2 = (603829127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603829127:ℝ)/168755200)*ClassicalSixthBranch.v ((603829127:ℝ)/168755200)/ClassicalSixthBranch.r = (135561456270017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1100
  · change upperPayment 1101 ≤ upperValue ((point split endpoint 4096 1101+point split endpoint 4096 1102)/2)
    have hp : upperPayment 1101 = (352534587686:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1101+point split endpoint 4096 1102)/2 = (603854277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603854277:ℝ)/168755200)*ClassicalSixthBranch.v ((603854277:ℝ)/168755200)/ClassicalSixthBranch.r = (135537667456425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1101
  · change upperPayment 1102 ≤ upperValue ((point split endpoint 4096 1102+point split endpoint 4096 1103)/2)
    have hp : upperPayment 1102 = (352457761734:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1102+point split endpoint 4096 1103)/2 = (603879427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603879427:ℝ)/168755200)*ClassicalSixthBranch.v ((603879427:ℝ)/168755200)/ClassicalSixthBranch.r = (135513880666905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1102
  · change upperPayment 1103 ≤ upperValue ((point split endpoint 4096 1103+point split endpoint 4096 1104)/2)
    have hp : upperPayment 1103 = (352380913450:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1103+point split endpoint 4096 1104)/2 = (603904577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603904577:ℝ)/168755200)*ClassicalSixthBranch.v ((603904577:ℝ)/168755200)/ClassicalSixthBranch.r = (135490095901457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1103
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_068
