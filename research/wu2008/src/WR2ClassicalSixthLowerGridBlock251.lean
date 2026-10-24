import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints251
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_251 (j : Fin 16) : lowerPayment (16*251+j.val) ≤
    lowerValue ((point 2 split 4096 (16*251+j.val)+point 2 split 4096 (16*251+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 4016 ≤ lowerValue ((point 2 split 4096 4016+point 2 split 4096 4017)/2)
    have hp : lowerPayment 4016 = (416205156685:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4016+point 2 split 4096 4017)/2 = (571519723:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((571519723:ℝ)/168755200)/ClassicalSixthBranch.v ((571519723:ℝ)/168755200) = (503484805083:ℝ)/227754777496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4016
  · change lowerPayment 4017 ≤ lowerValue ((point 2 split 4096 4017+point 2 split 4096 4018)/2)
    have hp : lowerPayment 4017 = (416306211232:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4017+point 2 split 4096 4018)/2 = (114315597:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((114315597:ℝ)/33751040)/ClassicalSixthBranch.v ((114315597:ℝ)/33751040) = (503407491409:ℝ)/227706769608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4017
  · change lowerPayment 4018 ≤ lowerValue ((point 2 split 4096 4018+point 2 split 4096 4019)/2)
    have hp : lowerPayment 4018 = (416407286609:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4018+point 2 split 4096 4019)/2 = (571636247:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((571636247:ℝ)/168755200)/ClassicalSixthBranch.v ((571636247:ℝ)/168755200) = (100666035547:ℝ)/45531752344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4018
  · change lowerPayment 4019 ≤ lowerValue ((point 2 split 4096 4019+point 2 split 4096 4020)/2)
    have hp : lowerPayment 4019 = (416508382835:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4019+point 2 split 4096 4020)/2 = (571694509:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((571694509:ℝ)/168755200)/ClassicalSixthBranch.v ((571694509:ℝ)/168755200) = (503252864061:ℝ)/227610753832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4019
  · change lowerPayment 4020 ≤ lowerValue ((point 2 split 4096 4020+point 2 split 4096 4021)/2)
    have hp : lowerPayment 4020 = (416609499930:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4020+point 2 split 4096 4021)/2 = (571752771:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((571752771:ℝ)/168755200)/ClassicalSixthBranch.v ((571752771:ℝ)/168755200) = (503175550387:ℝ)/227562745944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4020
  · change lowerPayment 4021 ≤ lowerValue ((point 2 split 4096 4021+point 2 split 4096 4022)/2)
    have hp : lowerPayment 4021 = (416710637912:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4021+point 2 split 4096 4022)/2 = (571811033:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((571811033:ℝ)/168755200)/ClassicalSixthBranch.v ((571811033:ℝ)/168755200) = (503098236713:ℝ)/227514738056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4021
  · change lowerPayment 4022 ≤ lowerValue ((point 2 split 4096 4022+point 2 split 4096 4023)/2)
    have hp : lowerPayment 4022 = (416811796800:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4022+point 2 split 4096 4023)/2 = (114373859:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((114373859:ℝ)/33751040)/ClassicalSixthBranch.v ((114373859:ℝ)/33751040) = (503020923039:ℝ)/227466730168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4022
  · change lowerPayment 4023 ≤ lowerValue ((point 2 split 4096 4023+point 2 split 4096 4024)/2)
    have hp : lowerPayment 4023 = (416912976615:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4023+point 2 split 4096 4024)/2 = (571927557:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((571927557:ℝ)/168755200)/ClassicalSixthBranch.v ((571927557:ℝ)/168755200) = (100588721873:ℝ)/45483744456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4023
  · change lowerPayment 4024 ≤ lowerValue ((point 2 split 4096 4024+point 2 split 4096 4025)/2)
    have hp : lowerPayment 4024 = (417014177374:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4024+point 2 split 4096 4025)/2 = (571985819:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((571985819:ℝ)/168755200)/ClassicalSixthBranch.v ((571985819:ℝ)/168755200) = (502866295691:ℝ)/227370714392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4024
  · change lowerPayment 4025 ≤ lowerValue ((point 2 split 4096 4025+point 2 split 4096 4026)/2)
    have hp : lowerPayment 4025 = (417115399097:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4025+point 2 split 4096 4026)/2 = (572044081:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((572044081:ℝ)/168755200)/ClassicalSixthBranch.v ((572044081:ℝ)/168755200) = (502788982017:ℝ)/227322706504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4025
  · change lowerPayment 4026 ≤ lowerValue ((point 2 split 4096 4026+point 2 split 4096 4027)/2)
    have hp : lowerPayment 4026 = (417216641803:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4026+point 2 split 4096 4027)/2 = (572102343:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((572102343:ℝ)/168755200)/ClassicalSixthBranch.v ((572102343:ℝ)/168755200) = (502711668343:ℝ)/227274698616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4026
  · change lowerPayment 4027 ≤ lowerValue ((point 2 split 4096 4027+point 2 split 4096 4028)/2)
    have hp : lowerPayment 4027 = (417317905511:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4027+point 2 split 4096 4028)/2 = (114432121:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((114432121:ℝ)/33751040)/ClassicalSixthBranch.v ((114432121:ℝ)/33751040) = (502634354669:ℝ)/227226690728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4027
  · change lowerPayment 4028 ≤ lowerValue ((point 2 split 4096 4028+point 2 split 4096 4029)/2)
    have hp : lowerPayment 4028 = (417419190240:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4028+point 2 split 4096 4029)/2 = (572218867:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((572218867:ℝ)/168755200)/ClassicalSixthBranch.v ((572218867:ℝ)/168755200) = (100511408199:ℝ)/45435736568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4028
  · change lowerPayment 4029 ≤ lowerValue ((point 2 split 4096 4029+point 2 split 4096 4030)/2)
    have hp : lowerPayment 4029 = (417520496010:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4029+point 2 split 4096 4030)/2 = (572277129:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((572277129:ℝ)/168755200)/ClassicalSixthBranch.v ((572277129:ℝ)/168755200) = (502479727321:ℝ)/227130674952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4029
  · change lowerPayment 4030 ≤ lowerValue ((point 2 split 4096 4030+point 2 split 4096 4031)/2)
    have hp : lowerPayment 4030 = (417621822840:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4030+point 2 split 4096 4031)/2 = (572335391:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((572335391:ℝ)/168755200)/ClassicalSixthBranch.v ((572335391:ℝ)/168755200) = (502402413647:ℝ)/227082667064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4030
  · change lowerPayment 4031 ≤ lowerValue ((point 2 split 4096 4031+point 2 split 4096 4032)/2)
    have hp : lowerPayment 4031 = (417723170748:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4031+point 2 split 4096 4032)/2 = (572393653:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((572393653:ℝ)/168755200)/ClassicalSixthBranch.v ((572393653:ℝ)/168755200) = (502325099973:ℝ)/227034659176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4031
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_251
