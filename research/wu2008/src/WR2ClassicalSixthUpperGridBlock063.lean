import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints063
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_063 (j : Fin 16) : upperPayment (16*63+j.val) ≤
    upperValue ((point split endpoint 4096 (16*63+j.val)+point split endpoint 4096 (16*63+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1008 ≤ upperValue ((point split endpoint 4096 1008+point split endpoint 4096 1009)/2)
    have hp : upperPayment 1008 = (359582274258:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1008+point split endpoint 4096 1009)/2 = (601515327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601515327:ℝ)/168755200)*ClassicalSixthBranch.v ((601515327:ℝ)/168755200)/ClassicalSixthBranch.r = (137758686100497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1008
  · change upperPayment 1009 ≤ upperValue ((point split endpoint 4096 1009+point split endpoint 4096 1010)/2)
    have hp : upperPayment 1009 = (359507509853:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1009+point split endpoint 4096 1010)/2 = (601540477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601540477:ℝ)/168755200)*ClassicalSixthBranch.v ((601540477:ℝ)/168755200)/ClassicalSixthBranch.r = (137734711072281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1009
  · change upperPayment 1010 ≤ upperValue ((point split endpoint 4096 1010+point split endpoint 4096 1011)/2)
    have hp : upperPayment 1010 = (359432723441:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1010+point split endpoint 4096 1011)/2 = (601565627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601565627:ℝ)/168755200)*ClassicalSixthBranch.v ((601565627:ℝ)/168755200)/ClassicalSixthBranch.r = (137710738068137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1010
  · change upperPayment 1011 ≤ upperValue ((point split endpoint 4096 1011+point split endpoint 4096 1012)/2)
    have hp : upperPayment 1011 = (359357915018:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1011+point split endpoint 4096 1012)/2 = (601590777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601590777:ℝ)/168755200)*ClassicalSixthBranch.v ((601590777:ℝ)/168755200)/ClassicalSixthBranch.r = (137686767088065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1011
  · change upperPayment 1012 ≤ upperValue ((point split endpoint 4096 1012+point split endpoint 4096 1013)/2)
    have hp : upperPayment 1012 = (359283084580:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1012+point split endpoint 4096 1013)/2 = (601615927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601615927:ℝ)/168755200)*ClassicalSixthBranch.v ((601615927:ℝ)/168755200)/ClassicalSixthBranch.r = (137662798132065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1012
  · change upperPayment 1013 ≤ upperValue ((point split endpoint 4096 1013+point split endpoint 4096 1014)/2)
    have hp : upperPayment 1013 = (359208232125:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1013+point split endpoint 4096 1014)/2 = (601641077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601641077:ℝ)/168755200)*ClassicalSixthBranch.v ((601641077:ℝ)/168755200)/ClassicalSixthBranch.r = (137638831200137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1013
  · change upperPayment 1014 ≤ upperValue ((point split endpoint 4096 1014+point split endpoint 4096 1015)/2)
    have hp : upperPayment 1014 = (359133357649:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1014+point split endpoint 4096 1015)/2 = (601666227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601666227:ℝ)/168755200)*ClassicalSixthBranch.v ((601666227:ℝ)/168755200)/ClassicalSixthBranch.r = (137614866292281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1014
  · change upperPayment 1015 ≤ upperValue ((point split endpoint 4096 1015+point split endpoint 4096 1016)/2)
    have hp : upperPayment 1015 = (359058461147:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1015+point split endpoint 4096 1016)/2 = (601691377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601691377:ℝ)/168755200)*ClassicalSixthBranch.v ((601691377:ℝ)/168755200)/ClassicalSixthBranch.r = (137590903408497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1015
  · change upperPayment 1016 ≤ upperValue ((point split endpoint 4096 1016+point split endpoint 4096 1017)/2)
    have hp : upperPayment 1016 = (358983542618:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1016+point split endpoint 4096 1017)/2 = (601716527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601716527:ℝ)/168755200)*ClassicalSixthBranch.v ((601716527:ℝ)/168755200)/ClassicalSixthBranch.r = (137566942548785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1016
  · change upperPayment 1017 ≤ upperValue ((point split endpoint 4096 1017+point split endpoint 4096 1018)/2)
    have hp : upperPayment 1017 = (358908602058:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1017+point split endpoint 4096 1018)/2 = (601741677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601741677:ℝ)/168755200)*ClassicalSixthBranch.v ((601741677:ℝ)/168755200)/ClassicalSixthBranch.r = (137542983713145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1017
  · change upperPayment 1018 ≤ upperValue ((point split endpoint 4096 1018+point split endpoint 4096 1019)/2)
    have hp : upperPayment 1018 = (358833639462:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1018+point split endpoint 4096 1019)/2 = (601766827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601766827:ℝ)/168755200)*ClassicalSixthBranch.v ((601766827:ℝ)/168755200)/ClassicalSixthBranch.r = (137519026901577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1018
  · change upperPayment 1019 ≤ upperValue ((point split endpoint 4096 1019+point split endpoint 4096 1020)/2)
    have hp : upperPayment 1019 = (358758654828:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1019+point split endpoint 4096 1020)/2 = (601791977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601791977:ℝ)/168755200)*ClassicalSixthBranch.v ((601791977:ℝ)/168755200)/ClassicalSixthBranch.r = (137495072114081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1019
  · change upperPayment 1020 ≤ upperValue ((point split endpoint 4096 1020+point split endpoint 4096 1021)/2)
    have hp : upperPayment 1020 = (358683648153:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1020+point split endpoint 4096 1021)/2 = (601817127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601817127:ℝ)/168755200)*ClassicalSixthBranch.v ((601817127:ℝ)/168755200)/ClassicalSixthBranch.r = (137471119350657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1020
  · change upperPayment 1021 ≤ upperValue ((point split endpoint 4096 1021+point split endpoint 4096 1022)/2)
    have hp : upperPayment 1021 = (358608619432:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1021+point split endpoint 4096 1022)/2 = (601842277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601842277:ℝ)/168755200)*ClassicalSixthBranch.v ((601842277:ℝ)/168755200)/ClassicalSixthBranch.r = (137447168611305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1021
  · change upperPayment 1022 ≤ upperValue ((point split endpoint 4096 1022+point split endpoint 4096 1023)/2)
    have hp : upperPayment 1022 = (358533568662:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1022+point split endpoint 4096 1023)/2 = (601867427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601867427:ℝ)/168755200)*ClassicalSixthBranch.v ((601867427:ℝ)/168755200)/ClassicalSixthBranch.r = (137423219896025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1022
  · change upperPayment 1023 ≤ upperValue ((point split endpoint 4096 1023+point split endpoint 4096 1024)/2)
    have hp : upperPayment 1023 = (358458495840:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1023+point split endpoint 4096 1024)/2 = (601892577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601892577:ℝ)/168755200)*ClassicalSixthBranch.v ((601892577:ℝ)/168755200)/ClassicalSixthBranch.r = (137399273204817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1023
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_063
