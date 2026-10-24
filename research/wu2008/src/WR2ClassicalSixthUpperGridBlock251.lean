import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints251
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_251 (j : Fin 16) : upperPayment (16*251+j.val) ≤
    upperValue ((point split endpoint 4096 (16*251+j.val)+point split endpoint 4096 (16*251+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 4016 ≤ upperValue ((point split endpoint 4096 4016+point split endpoint 4096 4017)/2)
    have hp : upperPayment 4016 = (13288135230:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4016+point split endpoint 4096 4017)/2 = (677166527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677166527:ℝ)/168755200)*ClassicalSixthBranch.v ((677166527:ℝ)/168755200)/ClassicalSixthBranch.r = (74795723520785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4016
  · change upperPayment 4017 ≤ upperValue ((point split endpoint 4096 4017+point split endpoint 4096 4018)/2)
    have hp : upperPayment 4017 = (13122664217:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4017+point split endpoint 4096 4018)/2 = (677191677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677191677:ℝ)/168755200)*ClassicalSixthBranch.v ((677191677:ℝ)/168755200)/ClassicalSixthBranch.r = (74777836901145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4017
  · change upperPayment 4018 ≤ upperValue ((point split endpoint 4096 4018+point split endpoint 4096 4019)/2)
    have hp : upperPayment 4018 = (12957150828:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4018+point split endpoint 4096 4019)/2 = (677216827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677216827:ℝ)/168755200)*ClassicalSixthBranch.v ((677216827:ℝ)/168755200)/ClassicalSixthBranch.r = (74759952305577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4018
  · change upperPayment 4019 ≤ upperValue ((point split endpoint 4096 4019+point split endpoint 4096 4020)/2)
    have hp : upperPayment 4019 = (12791595052:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4019+point split endpoint 4096 4020)/2 = (677241977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677241977:ℝ)/168755200)*ClassicalSixthBranch.v ((677241977:ℝ)/168755200)/ClassicalSixthBranch.r = (74742069734081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4019
  · change upperPayment 4020 ≤ upperValue ((point split endpoint 4096 4020+point split endpoint 4096 4021)/2)
    have hp : upperPayment 4020 = (12625996876:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4020+point split endpoint 4096 4021)/2 = (6575409:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((6575409:ℝ)/1638400)*ClassicalSixthBranch.v ((6575409:ℝ)/1638400)/ClassicalSixthBranch.r = (725477564919:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4020
  · change upperPayment 4021 ≤ upperValue ((point split endpoint 4096 4021+point split endpoint 4096 4022)/2)
    have hp : upperPayment 4021 = (12460356290:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4021+point split endpoint 4096 4022)/2 = (677292277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677292277:ℝ)/168755200)*ClassicalSixthBranch.v ((677292277:ℝ)/168755200)/ClassicalSixthBranch.r = (74706310663305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4021
  · change upperPayment 4022 ≤ upperValue ((point split endpoint 4096 4022+point split endpoint 4096 4023)/2)
    have hp : upperPayment 4022 = (12294673281:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4022+point split endpoint 4096 4023)/2 = (677317427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677317427:ℝ)/168755200)*ClassicalSixthBranch.v ((677317427:ℝ)/168755200)/ClassicalSixthBranch.r = (74688434164025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4022
  · change upperPayment 4023 ≤ upperValue ((point split endpoint 4096 4023+point split endpoint 4096 4024)/2)
    have hp : upperPayment 4023 = (12128947836:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4023+point split endpoint 4096 4024)/2 = (677342577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677342577:ℝ)/168755200)*ClassicalSixthBranch.v ((677342577:ℝ)/168755200)/ClassicalSixthBranch.r = (74670559688817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4023
  · change upperPayment 4024 ≤ upperValue ((point split endpoint 4096 4024+point split endpoint 4096 4025)/2)
    have hp : upperPayment 4024 = (11963179946:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4024+point split endpoint 4096 4025)/2 = (677367727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677367727:ℝ)/168755200)*ClassicalSixthBranch.v ((677367727:ℝ)/168755200)/ClassicalSixthBranch.r = (74652687237681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4024
  · change upperPayment 4025 ≤ upperValue ((point split endpoint 4096 4025+point split endpoint 4096 4026)/2)
    have hp : upperPayment 4025 = (11797369597:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4025+point split endpoint 4096 4026)/2 = (677392877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677392877:ℝ)/168755200)*ClassicalSixthBranch.v ((677392877:ℝ)/168755200)/ClassicalSixthBranch.r = (74634816810617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4025
  · change upperPayment 4026 ≤ upperValue ((point split endpoint 4096 4026+point split endpoint 4096 4027)/2)
    have hp : upperPayment 4026 = (11631516777:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4026+point split endpoint 4096 4027)/2 = (677418027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677418027:ℝ)/168755200)*ClassicalSixthBranch.v ((677418027:ℝ)/168755200)/ClassicalSixthBranch.r = (74616948407625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4026
  · change upperPayment 4027 ≤ upperValue ((point split endpoint 4096 4027+point split endpoint 4096 4028)/2)
    have hp : upperPayment 4027 = (11465621475:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4027+point split endpoint 4096 4028)/2 = (677443177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677443177:ℝ)/168755200)*ClassicalSixthBranch.v ((677443177:ℝ)/168755200)/ClassicalSixthBranch.r = (74599082028705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4027
  · change upperPayment 4028 ≤ upperValue ((point split endpoint 4096 4028+point split endpoint 4096 4029)/2)
    have hp : upperPayment 4028 = (11299683679:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4028+point split endpoint 4096 4029)/2 = (677468327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677468327:ℝ)/168755200)*ClassicalSixthBranch.v ((677468327:ℝ)/168755200)/ClassicalSixthBranch.r = (74581217673857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4028
  · change upperPayment 4029 ≤ upperValue ((point split endpoint 4096 4029+point split endpoint 4096 4030)/2)
    have hp : upperPayment 4029 = (11133703378:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4029+point split endpoint 4096 4030)/2 = (677493477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677493477:ℝ)/168755200)*ClassicalSixthBranch.v ((677493477:ℝ)/168755200)/ClassicalSixthBranch.r = (74563355343081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4029
  · change upperPayment 4030 ≤ upperValue ((point split endpoint 4096 4030+point split endpoint 4096 4031)/2)
    have hp : upperPayment 4030 = (10967680558:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4030+point split endpoint 4096 4031)/2 = (677518627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677518627:ℝ)/168755200)*ClassicalSixthBranch.v ((677518627:ℝ)/168755200)/ClassicalSixthBranch.r = (74545495036377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4030
  · change upperPayment 4031 ≤ upperValue ((point split endpoint 4096 4031+point split endpoint 4096 4032)/2)
    have hp : upperPayment 4031 = (10801615208:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4031+point split endpoint 4096 4032)/2 = (677543777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677543777:ℝ)/168755200)*ClassicalSixthBranch.v ((677543777:ℝ)/168755200)/ClassicalSixthBranch.r = (74527636753745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4031
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_251
