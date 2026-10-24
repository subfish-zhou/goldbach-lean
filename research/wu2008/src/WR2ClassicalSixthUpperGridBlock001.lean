import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints001
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_001 (j : Fin 16) : upperPayment (16*1+j.val) ≤
    upperValue ((point split endpoint 4096 (16*1+j.val)+point split endpoint 4096 (16*1+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 16 ≤ upperValue ((point split endpoint 4096 16+point split endpoint 4096 17)/2)
    have hp : upperPayment 16 = (423410853600:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 16+point split endpoint 4096 17)/2 = (576566527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576566527:ℝ)/168755200)*ClassicalSixthBranch.v ((576566527:ℝ)/168755200)/ClassicalSixthBranch.r = (162538826224785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_16
  · change upperPayment 17 ≤ upperValue ((point split endpoint 4096 17+point split endpoint 4096 18)/2)
    have hp : upperPayment 17 = (423356461368:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 17+point split endpoint 4096 18)/2 = (576591677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576591677:ℝ)/168755200)*ClassicalSixthBranch.v ((576591677:ℝ)/168755200)/ClassicalSixthBranch.r = (162512843317145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_17
  · change upperPayment 18 ≤ upperValue ((point split endpoint 4096 18+point split endpoint 4096 19)/2)
    have hp : upperPayment 18 = (423302049854:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 18+point split endpoint 4096 19)/2 = (576616827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576616827:ℝ)/168755200)*ClassicalSixthBranch.v ((576616827:ℝ)/168755200)/ClassicalSixthBranch.r = (162486862433577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_18
  · change upperPayment 19 ≤ upperValue ((point split endpoint 4096 19+point split endpoint 4096 20)/2)
    have hp : upperPayment 19 = (423247619054:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 19+point split endpoint 4096 20)/2 = (576641977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576641977:ℝ)/168755200)*ClassicalSixthBranch.v ((576641977:ℝ)/168755200)/ClassicalSixthBranch.r = (162460883574081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_19
  · change upperPayment 20 ≤ upperValue ((point split endpoint 4096 20+point split endpoint 4096 21)/2)
    have hp : upperPayment 20 = (423193168967:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 20+point split endpoint 4096 21)/2 = (576667127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576667127:ℝ)/168755200)*ClassicalSixthBranch.v ((576667127:ℝ)/168755200)/ClassicalSixthBranch.r = (162434906738657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_20
  · change upperPayment 21 ≤ upperValue ((point split endpoint 4096 21+point split endpoint 4096 22)/2)
    have hp : upperPayment 21 = (423138699591:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 21+point split endpoint 4096 22)/2 = (576692277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576692277:ℝ)/168755200)*ClassicalSixthBranch.v ((576692277:ℝ)/168755200)/ClassicalSixthBranch.r = (162408931927305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_21
  · change upperPayment 22 ≤ upperValue ((point split endpoint 4096 22+point split endpoint 4096 23)/2)
    have hp : upperPayment 22 = (423084210923:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 22+point split endpoint 4096 23)/2 = (576717427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576717427:ℝ)/168755200)*ClassicalSixthBranch.v ((576717427:ℝ)/168755200)/ClassicalSixthBranch.r = (162382959140025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_22
  · change upperPayment 23 ≤ upperValue ((point split endpoint 4096 23+point split endpoint 4096 24)/2)
    have hp : upperPayment 23 = (423029702962:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 23+point split endpoint 4096 24)/2 = (576742577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576742577:ℝ)/168755200)*ClassicalSixthBranch.v ((576742577:ℝ)/168755200)/ClassicalSixthBranch.r = (162356988376817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_23
  · change upperPayment 24 ≤ upperValue ((point split endpoint 4096 24+point split endpoint 4096 25)/2)
    have hp : upperPayment 24 = (422975175705:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 24+point split endpoint 4096 25)/2 = (576767727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576767727:ℝ)/168755200)*ClassicalSixthBranch.v ((576767727:ℝ)/168755200)/ClassicalSixthBranch.r = (162331019637681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_24
  · change upperPayment 25 ≤ upperValue ((point split endpoint 4096 25+point split endpoint 4096 26)/2)
    have hp : upperPayment 25 = (422920629151:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 25+point split endpoint 4096 26)/2 = (576792877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576792877:ℝ)/168755200)*ClassicalSixthBranch.v ((576792877:ℝ)/168755200)/ClassicalSixthBranch.r = (162305052922617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_25
  · change upperPayment 26 ≤ upperValue ((point split endpoint 4096 26+point split endpoint 4096 27)/2)
    have hp : upperPayment 26 = (422866063296:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 26+point split endpoint 4096 27)/2 = (576818027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576818027:ℝ)/168755200)*ClassicalSixthBranch.v ((576818027:ℝ)/168755200)/ClassicalSixthBranch.r = (162279088231625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_26
  · change upperPayment 27 ≤ upperValue ((point split endpoint 4096 27+point split endpoint 4096 28)/2)
    have hp : upperPayment 27 = (422811478140:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 27+point split endpoint 4096 28)/2 = (576843177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576843177:ℝ)/168755200)*ClassicalSixthBranch.v ((576843177:ℝ)/168755200)/ClassicalSixthBranch.r = (1575273063735:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_27
  · change upperPayment 28 ≤ upperValue ((point split endpoint 4096 28+point split endpoint 4096 29)/2)
    have hp : upperPayment 28 = (422756873679:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 28+point split endpoint 4096 29)/2 = (576868327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576868327:ℝ)/168755200)*ClassicalSixthBranch.v ((576868327:ℝ)/168755200)/ClassicalSixthBranch.r = (162227164921857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_28
  · change upperPayment 29 ≤ upperValue ((point split endpoint 4096 29+point split endpoint 4096 30)/2)
    have hp : upperPayment 29 = (422702249912:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 29+point split endpoint 4096 30)/2 = (576893477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576893477:ℝ)/168755200)*ClassicalSixthBranch.v ((576893477:ℝ)/168755200)/ClassicalSixthBranch.r = (162201206303081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_29
  · change upperPayment 30 ≤ upperValue ((point split endpoint 4096 30+point split endpoint 4096 31)/2)
    have hp : upperPayment 30 = (422647606837:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 30+point split endpoint 4096 31)/2 = (576918627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576918627:ℝ)/168755200)*ClassicalSixthBranch.v ((576918627:ℝ)/168755200)/ClassicalSixthBranch.r = (162175249708377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_30
  · change upperPayment 31 ≤ upperValue ((point split endpoint 4096 31+point split endpoint 4096 32)/2)
    have hp : upperPayment 31 = (422592944451:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 31+point split endpoint 4096 32)/2 = (576943777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576943777:ℝ)/168755200)*ClassicalSixthBranch.v ((576943777:ℝ)/168755200)/ClassicalSixthBranch.r = (162149295137745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_31
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_001
