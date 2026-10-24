import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints252
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_252 (j : Fin 16) : upperPayment (16*252+j.val) ≤
    upperValue ((point split endpoint 4096 (16*252+j.val)+point split endpoint 4096 (16*252+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 4032 ≤ upperValue ((point split endpoint 4096 4032+point split endpoint 4096 4033)/2)
    have hp : upperPayment 4032 = (10635507317:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4032+point split endpoint 4096 4033)/2 = (677568927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677568927:ℝ)/168755200)*ClassicalSixthBranch.v ((677568927:ℝ)/168755200)/ClassicalSixthBranch.r = (74509780495185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4032
  · change upperPayment 4033 ≤ upperValue ((point split endpoint 4096 4033+point split endpoint 4096 4034)/2)
    have hp : upperPayment 4033 = (10469356872:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4033+point split endpoint 4096 4034)/2 = (677594077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677594077:ℝ)/168755200)*ClassicalSixthBranch.v ((677594077:ℝ)/168755200)/ClassicalSixthBranch.r = (74491926260697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4033
  · change upperPayment 4034 ≤ upperValue ((point split endpoint 4096 4034+point split endpoint 4096 4035)/2)
    have hp : upperPayment 4034 = (10303163862:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4034+point split endpoint 4096 4035)/2 = (677619227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677619227:ℝ)/168755200)*ClassicalSixthBranch.v ((677619227:ℝ)/168755200)/ClassicalSixthBranch.r = (74474074050281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4034
  · change upperPayment 4035 ≤ upperValue ((point split endpoint 4096 4035+point split endpoint 4096 4036)/2)
    have hp : upperPayment 4035 = (10136928274:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4035+point split endpoint 4096 4036)/2 = (677644377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677644377:ℝ)/168755200)*ClassicalSixthBranch.v ((677644377:ℝ)/168755200)/ClassicalSixthBranch.r = (74456223863937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4035
  · change upperPayment 4036 ≤ upperValue ((point split endpoint 4096 4036+point split endpoint 4096 4037)/2)
    have hp : upperPayment 4036 = (9970650097:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4036+point split endpoint 4096 4037)/2 = (677669527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677669527:ℝ)/168755200)*ClassicalSixthBranch.v ((677669527:ℝ)/168755200)/ClassicalSixthBranch.r = (74438375701665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4036
  · change upperPayment 4037 ≤ upperValue ((point split endpoint 4096 4037+point split endpoint 4096 4038)/2)
    have hp : upperPayment 4037 = (9804329318:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4037+point split endpoint 4096 4038)/2 = (677694677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677694677:ℝ)/168755200)*ClassicalSixthBranch.v ((677694677:ℝ)/168755200)/ClassicalSixthBranch.r = (74420529563465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4037
  · change upperPayment 4038 ≤ upperValue ((point split endpoint 4096 4038+point split endpoint 4096 4039)/2)
    have hp : upperPayment 4038 = (9637965927:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4038+point split endpoint 4096 4039)/2 = (677719827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677719827:ℝ)/168755200)*ClassicalSixthBranch.v ((677719827:ℝ)/168755200)/ClassicalSixthBranch.r = (74402685449337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4038
  · change upperPayment 4039 ≤ upperValue ((point split endpoint 4096 4039+point split endpoint 4096 4040)/2)
    have hp : upperPayment 4039 = (9471559910:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4039+point split endpoint 4096 4040)/2 = (677744977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677744977:ℝ)/168755200)*ClassicalSixthBranch.v ((677744977:ℝ)/168755200)/ClassicalSixthBranch.r = (74384843359281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4039
  · change upperPayment 4040 ≤ upperValue ((point split endpoint 4096 4040+point split endpoint 4096 4041)/2)
    have hp : upperPayment 4040 = (9305111256:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4040+point split endpoint 4096 4041)/2 = (677770127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677770127:ℝ)/168755200)*ClassicalSixthBranch.v ((677770127:ℝ)/168755200)/ClassicalSixthBranch.r = (74367003293297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4040
  · change upperPayment 4041 ≤ upperValue ((point split endpoint 4096 4041+point split endpoint 4096 4042)/2)
    have hp : upperPayment 4041 = (9138619953:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4041+point split endpoint 4096 4042)/2 = (677795277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677795277:ℝ)/168755200)*ClassicalSixthBranch.v ((677795277:ℝ)/168755200)/ClassicalSixthBranch.r = (74349165251385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4041
  · change upperPayment 4042 ≤ upperValue ((point split endpoint 4096 4042+point split endpoint 4096 4043)/2)
    have hp : upperPayment 4042 = (8972085989:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4042+point split endpoint 4096 4043)/2 = (677820427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677820427:ℝ)/168755200)*ClassicalSixthBranch.v ((677820427:ℝ)/168755200)/ClassicalSixthBranch.r = (74331329233545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4042
  · change upperPayment 4043 ≤ upperValue ((point split endpoint 4096 4043+point split endpoint 4096 4044)/2)
    have hp : upperPayment 4043 = (8805509352:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4043+point split endpoint 4096 4044)/2 = (677845577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677845577:ℝ)/168755200)*ClassicalSixthBranch.v ((677845577:ℝ)/168755200)/ClassicalSixthBranch.r = (74313495239777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4043
  · change upperPayment 4044 ≤ upperValue ((point split endpoint 4096 4044+point split endpoint 4096 4045)/2)
    have hp : upperPayment 4044 = (8638890030:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4044+point split endpoint 4096 4045)/2 = (677870727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677870727:ℝ)/168755200)*ClassicalSixthBranch.v ((677870727:ℝ)/168755200)/ClassicalSixthBranch.r = (721317119127:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4044
  · change upperPayment 4045 ≤ upperValue ((point split endpoint 4096 4045+point split endpoint 4096 4046)/2)
    have hp : upperPayment 4045 = (8472228011:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4045+point split endpoint 4096 4046)/2 = (677895877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677895877:ℝ)/168755200)*ClassicalSixthBranch.v ((677895877:ℝ)/168755200)/ClassicalSixthBranch.r = (74277833324457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4045
  · change upperPayment 4046 ≤ upperValue ((point split endpoint 4096 4046+point split endpoint 4096 4047)/2)
    have hp : upperPayment 4046 = (8305523283:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4046+point split endpoint 4096 4047)/2 = (677921027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677921027:ℝ)/168755200)*ClassicalSixthBranch.v ((677921027:ℝ)/168755200)/ClassicalSixthBranch.r = (74260005402905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4046
  · change upperPayment 4047 ≤ upperValue ((point split endpoint 4096 4047+point split endpoint 4096 4048)/2)
    have hp : upperPayment 4047 = (8138775834:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4047+point split endpoint 4096 4048)/2 = (677946177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((677946177:ℝ)/168755200)*ClassicalSixthBranch.v ((677946177:ℝ)/168755200)/ClassicalSixthBranch.r = (74242179505425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4047
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_252
