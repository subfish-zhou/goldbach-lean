import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints067
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_067 (j : Fin 16) : upperPayment (16*67+j.val) ≤
    upperValue ((point split endpoint 4096 (16*67+j.val)+point split endpoint 4096 (16*67+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1072 ≤ upperValue ((point split endpoint 4096 1072+point split endpoint 4096 1073)/2)
    have hp : upperPayment 1072 = (354752841595:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1072+point split endpoint 4096 1073)/2 = (603124927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603124927:ℝ)/168755200)*ClassicalSixthBranch.v ((603124927:ℝ)/168755200)/ClassicalSixthBranch.r = (136228364823825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1072
  · change upperPayment 1073 ≤ upperValue ((point split endpoint 4096 1073+point split endpoint 4096 1074)/2)
    have hp : upperPayment 1073 = (354676661743:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1073+point split endpoint 4096 1074)/2 = (603150077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603150077:ℝ)/168755200)*ClassicalSixthBranch.v ((603150077:ℝ)/168755200)/ClassicalSixthBranch.r = (136204519336217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1073
  · change upperPayment 1074 ≤ upperValue ((point split endpoint 4096 1074+point split endpoint 4096 1075)/2)
    have hp : upperPayment 1074 = (354600459661:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1074+point split endpoint 4096 1075)/2 = (603175227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603175227:ℝ)/168755200)*ClassicalSixthBranch.v ((603175227:ℝ)/168755200)/ClassicalSixthBranch.r = (136180675872681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1074
  · change upperPayment 1075 ≤ upperValue ((point split endpoint 4096 1075+point split endpoint 4096 1076)/2)
    have hp : upperPayment 1075 = (354524235345:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1075+point split endpoint 4096 1076)/2 = (603200377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603200377:ℝ)/168755200)*ClassicalSixthBranch.v ((603200377:ℝ)/168755200)/ClassicalSixthBranch.r = (136156834433217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1075
  · change upperPayment 1076 ≤ upperValue ((point split endpoint 4096 1076+point split endpoint 4096 1077)/2)
    have hp : upperPayment 1076 = (354447988793:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1076+point split endpoint 4096 1077)/2 = (603225527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603225527:ℝ)/168755200)*ClassicalSixthBranch.v ((603225527:ℝ)/168755200)/ClassicalSixthBranch.r = (136132995017825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1076
  · change upperPayment 1077 ≤ upperValue ((point split endpoint 4096 1077+point split endpoint 4096 1078)/2)
    have hp : upperPayment 1077 = (354371720001:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1077+point split endpoint 4096 1078)/2 = (603250677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603250677:ℝ)/168755200)*ClassicalSixthBranch.v ((603250677:ℝ)/168755200)/ClassicalSixthBranch.r = (136109157626505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1077
  · change upperPayment 1078 ≤ upperValue ((point split endpoint 4096 1078+point split endpoint 4096 1079)/2)
    have hp : upperPayment 1078 = (354295428964:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1078+point split endpoint 4096 1079)/2 = (603275827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603275827:ℝ)/168755200)*ClassicalSixthBranch.v ((603275827:ℝ)/168755200)/ClassicalSixthBranch.r = (136085322259257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1078
  · change upperPayment 1079 ≤ upperValue ((point split endpoint 4096 1079+point split endpoint 4096 1080)/2)
    have hp : upperPayment 1079 = (354219115681:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1079+point split endpoint 4096 1080)/2 = (603300977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603300977:ℝ)/168755200)*ClassicalSixthBranch.v ((603300977:ℝ)/168755200)/ClassicalSixthBranch.r = (136061488916081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1079
  · change upperPayment 1080 ≤ upperValue ((point split endpoint 4096 1080+point split endpoint 4096 1081)/2)
    have hp : upperPayment 1080 = (354142780146:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1080+point split endpoint 4096 1081)/2 = (603326127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603326127:ℝ)/168755200)*ClassicalSixthBranch.v ((603326127:ℝ)/168755200)/ClassicalSixthBranch.r = (136037657596977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1080
  · change upperPayment 1081 ≤ upperValue ((point split endpoint 4096 1081+point split endpoint 4096 1082)/2)
    have hp : upperPayment 1081 = (354066422357:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1081+point split endpoint 4096 1082)/2 = (603351277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603351277:ℝ)/168755200)*ClassicalSixthBranch.v ((603351277:ℝ)/168755200)/ClassicalSixthBranch.r = (136013828301945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1081
  · change upperPayment 1082 ≤ upperValue ((point split endpoint 4096 1082+point split endpoint 4096 1083)/2)
    have hp : upperPayment 1082 = (353990042310:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1082+point split endpoint 4096 1083)/2 = (603376427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603376427:ℝ)/168755200)*ClassicalSixthBranch.v ((603376427:ℝ)/168755200)/ClassicalSixthBranch.r = (135990001030985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1082
  · change upperPayment 1083 ≤ upperValue ((point split endpoint 4096 1083+point split endpoint 4096 1084)/2)
    have hp : upperPayment 1083 = (353913640001:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1083+point split endpoint 4096 1084)/2 = (603401577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603401577:ℝ)/168755200)*ClassicalSixthBranch.v ((603401577:ℝ)/168755200)/ClassicalSixthBranch.r = (135966175784097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1083
  · change upperPayment 1084 ≤ upperValue ((point split endpoint 4096 1084+point split endpoint 4096 1085)/2)
    have hp : upperPayment 1084 = (353837215427:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1084+point split endpoint 4096 1085)/2 = (603426727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603426727:ℝ)/168755200)*ClassicalSixthBranch.v ((603426727:ℝ)/168755200)/ClassicalSixthBranch.r = (135942352561281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1084
  · change upperPayment 1085 ≤ upperValue ((point split endpoint 4096 1085+point split endpoint 4096 1086)/2)
    have hp : upperPayment 1085 = (353760768585:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1085+point split endpoint 4096 1086)/2 = (603451877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603451877:ℝ)/168755200)*ClassicalSixthBranch.v ((603451877:ℝ)/168755200)/ClassicalSixthBranch.r = (135918531362537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1085
  · change upperPayment 1086 ≤ upperValue ((point split endpoint 4096 1086+point split endpoint 4096 1087)/2)
    have hp : upperPayment 1086 = (353684299470:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1086+point split endpoint 4096 1087)/2 = (603477027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603477027:ℝ)/168755200)*ClassicalSixthBranch.v ((603477027:ℝ)/168755200)/ClassicalSixthBranch.r = (135894712187865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1086
  · change upperPayment 1087 ≤ upperValue ((point split endpoint 4096 1087+point split endpoint 4096 1088)/2)
    have hp : upperPayment 1087 = (353607808080:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1087+point split endpoint 4096 1088)/2 = (603502177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603502177:ℝ)/168755200)*ClassicalSixthBranch.v ((603502177:ℝ)/168755200)/ClassicalSixthBranch.r = (135870895037265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1087
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_067
