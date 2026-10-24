import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints225
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_225 (j : Fin 16) : upperPayment (16*225+j.val) ≤
    upperValue ((point split endpoint 4096 (16*225+j.val)+point split endpoint 4096 (16*225+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3600 ≤ upperValue ((point split endpoint 4096 3600+point split endpoint 4096 3601)/2)
    have hp : upperPayment 3600 = (78585435871:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3600+point split endpoint 4096 3601)/2 = (666704127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666704127:ℝ)/168755200)*ClassicalSixthBranch.v ((666704127:ℝ)/168755200)/ClassicalSixthBranch.r = (82412117200017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3600
  · change upperPayment 3601 ≤ upperValue ((point split endpoint 4096 3601+point split endpoint 4096 3602)/2)
    have hp : upperPayment 3601 = (78436625087:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3601+point split endpoint 4096 3602)/2 = (666729277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666729277:ℝ)/168755200)*ClassicalSixthBranch.v ((666729277:ℝ)/168755200)/ClassicalSixthBranch.r = (82393388566425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3601
  · change upperPayment 3602 ≤ upperValue ((point split endpoint 4096 3602+point split endpoint 4096 3603)/2)
    have hp : upperPayment 3602 = (78287776438:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3602+point split endpoint 4096 3603)/2 = (666754427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666754427:ℝ)/168755200)*ClassicalSixthBranch.v ((666754427:ℝ)/168755200)/ClassicalSixthBranch.r = (82374661956905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3602
  · change upperPayment 3603 ≤ upperValue ((point split endpoint 4096 3603+point split endpoint 4096 3604)/2)
    have hp : upperPayment 3603 = (78138889913:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3603+point split endpoint 4096 3604)/2 = (666779577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666779577:ℝ)/168755200)*ClassicalSixthBranch.v ((666779577:ℝ)/168755200)/ClassicalSixthBranch.r = (82355937371457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3603
  · change upperPayment 3604 ≤ upperValue ((point split endpoint 4096 3604+point split endpoint 4096 3605)/2)
    have hp : upperPayment 3604 = (77989965503:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3604+point split endpoint 4096 3605)/2 = (666804727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666804727:ℝ)/168755200)*ClassicalSixthBranch.v ((666804727:ℝ)/168755200)/ClassicalSixthBranch.r = (82337214810081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3604
  · change upperPayment 3605 ≤ upperValue ((point split endpoint 4096 3605+point split endpoint 4096 3606)/2)
    have hp : upperPayment 3605 = (77841003197:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3605+point split endpoint 4096 3606)/2 = (666829877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666829877:ℝ)/168755200)*ClassicalSixthBranch.v ((666829877:ℝ)/168755200)/ClassicalSixthBranch.r = (82318494272777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3605
  · change upperPayment 3606 ≤ upperValue ((point split endpoint 4096 3606+point split endpoint 4096 3607)/2)
    have hp : upperPayment 3606 = (77692002986:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3606+point split endpoint 4096 3607)/2 = (666855027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666855027:ℝ)/168755200)*ClassicalSixthBranch.v ((666855027:ℝ)/168755200)/ClassicalSixthBranch.r = (82299775759545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3606
  · change upperPayment 3607 ≤ upperValue ((point split endpoint 4096 3607+point split endpoint 4096 3608)/2)
    have hp : upperPayment 3607 = (77542964859:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3607+point split endpoint 4096 3608)/2 = (666880177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666880177:ℝ)/168755200)*ClassicalSixthBranch.v ((666880177:ℝ)/168755200)/ClassicalSixthBranch.r = (82281059270385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3607
  · change upperPayment 3608 ≤ upperValue ((point split endpoint 4096 3608+point split endpoint 4096 3609)/2)
    have hp : upperPayment 3608 = (77393888808:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3608+point split endpoint 4096 3609)/2 = (6474809:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((6474809:ℝ)/1638400)*ClassicalSixthBranch.v ((6474809:ℝ)/1638400)/ClassicalSixthBranch.r = (798663541799:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3608
  · change upperPayment 3609 ≤ upperValue ((point split endpoint 4096 3609+point split endpoint 4096 3610)/2)
    have hp : upperPayment 3609 = (77244774821:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3609+point split endpoint 4096 3610)/2 = (666930477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666930477:ℝ)/168755200)*ClassicalSixthBranch.v ((666930477:ℝ)/168755200)/ClassicalSixthBranch.r = (82243632364281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3609
  · change upperPayment 3610 ≤ upperValue ((point split endpoint 4096 3610+point split endpoint 4096 3611)/2)
    have hp : upperPayment 3610 = (77095622889:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3610+point split endpoint 4096 3611)/2 = (666955627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666955627:ℝ)/168755200)*ClassicalSixthBranch.v ((666955627:ℝ)/168755200)/ClassicalSixthBranch.r = (82224921947337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3610
  · change upperPayment 3611 ≤ upperValue ((point split endpoint 4096 3611+point split endpoint 4096 3612)/2)
    have hp : upperPayment 3611 = (76946433002:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3611+point split endpoint 4096 3612)/2 = (666980777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666980777:ℝ)/168755200)*ClassicalSixthBranch.v ((666980777:ℝ)/168755200)/ClassicalSixthBranch.r = (82206213554465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3611
  · change upperPayment 3612 ≤ upperValue ((point split endpoint 4096 3612+point split endpoint 4096 3613)/2)
    have hp : upperPayment 3612 = (76797205150:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3612+point split endpoint 4096 3613)/2 = (667005927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667005927:ℝ)/168755200)*ClassicalSixthBranch.v ((667005927:ℝ)/168755200)/ClassicalSixthBranch.r = (82187507185665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3612
  · change upperPayment 3613 ≤ upperValue ((point split endpoint 4096 3613+point split endpoint 4096 3614)/2)
    have hp : upperPayment 3613 = (76647939322:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3613+point split endpoint 4096 3614)/2 = (667031077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667031077:ℝ)/168755200)*ClassicalSixthBranch.v ((667031077:ℝ)/168755200)/ClassicalSixthBranch.r = (82168802840937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3613
  · change upperPayment 3614 ≤ upperValue ((point split endpoint 4096 3614+point split endpoint 4096 3615)/2)
    have hp : upperPayment 3614 = (76498635510:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3614+point split endpoint 4096 3615)/2 = (667056227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667056227:ℝ)/168755200)*ClassicalSixthBranch.v ((667056227:ℝ)/168755200)/ClassicalSixthBranch.r = (82150100520281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3614
  · change upperPayment 3615 ≤ upperValue ((point split endpoint 4096 3615+point split endpoint 4096 3616)/2)
    have hp : upperPayment 3615 = (76349293703:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3615+point split endpoint 4096 3616)/2 = (667081377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667081377:ℝ)/168755200)*ClassicalSixthBranch.v ((667081377:ℝ)/168755200)/ClassicalSixthBranch.r = (82131400223697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3615
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_225
