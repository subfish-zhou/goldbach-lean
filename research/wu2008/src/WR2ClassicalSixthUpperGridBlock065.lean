import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints065
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_065 (j : Fin 16) : upperPayment (16*65+j.val) ≤
    upperValue ((point split endpoint 4096 (16*65+j.val)+point split endpoint 4096 (16*65+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1040 ≤ upperValue ((point split endpoint 4096 1040+point split endpoint 4096 1041)/2)
    have hp : upperPayment 1040 = (357178880551:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1040+point split endpoint 4096 1041)/2 = (602320127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602320127:ℝ)/168755200)*ClassicalSixthBranch.v ((602320127:ℝ)/168755200)/ClassicalSixthBranch.r = (136992489137297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1040
  · change upperPayment 1041 ≤ upperValue ((point split endpoint 4096 1041+point split endpoint 4096 1042)/2)
    have hp : upperPayment 1041 = (357103410201:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1041+point split endpoint 4096 1042)/2 = (602345277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602345277:ℝ)/168755200)*ClassicalSixthBranch.v ((602345277:ℝ)/168755200)/ClassicalSixthBranch.r = (136968578879385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1041
  · change upperPayment 1042 ≤ upperValue ((point split endpoint 4096 1042+point split endpoint 4096 1043)/2)
    have hp : upperPayment 1042 = (357027917732:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1042+point split endpoint 4096 1043)/2 = (602370427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602370427:ℝ)/168755200)*ClassicalSixthBranch.v ((602370427:ℝ)/168755200)/ClassicalSixthBranch.r = (136944670645545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1042
  · change upperPayment 1043 ≤ upperValue ((point split endpoint 4096 1043+point split endpoint 4096 1044)/2)
    have hp : upperPayment 1043 = (356952403142:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1043+point split endpoint 4096 1044)/2 = (602395577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602395577:ℝ)/168755200)*ClassicalSixthBranch.v ((602395577:ℝ)/168755200)/ClassicalSixthBranch.r = (136920764435777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1043
  · change upperPayment 1044 ≤ upperValue ((point split endpoint 4096 1044+point split endpoint 4096 1045)/2)
    have hp : upperPayment 1044 = (356876866428:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1044+point split endpoint 4096 1045)/2 = (602420727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602420727:ℝ)/168755200)*ClassicalSixthBranch.v ((602420727:ℝ)/168755200)/ClassicalSixthBranch.r = (136896860250081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1044
  · change upperPayment 1045 ≤ upperValue ((point split endpoint 4096 1045+point split endpoint 4096 1046)/2)
    have hp : upperPayment 1045 = (356801307585:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1045+point split endpoint 4096 1046)/2 = (602445877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602445877:ℝ)/168755200)*ClassicalSixthBranch.v ((602445877:ℝ)/168755200)/ClassicalSixthBranch.r = (136872958088457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1045
  · change upperPayment 1046 ≤ upperValue ((point split endpoint 4096 1046+point split endpoint 4096 1047)/2)
    have hp : upperPayment 1046 = (356725726610:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1046+point split endpoint 4096 1047)/2 = (602471027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602471027:ℝ)/168755200)*ClassicalSixthBranch.v ((602471027:ℝ)/168755200)/ClassicalSixthBranch.r = (136849057950905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1046
  · change upperPayment 1047 ≤ upperValue ((point split endpoint 4096 1047+point split endpoint 4096 1048)/2)
    have hp : upperPayment 1047 = (356650123501:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1047+point split endpoint 4096 1048)/2 = (602496177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602496177:ℝ)/168755200)*ClassicalSixthBranch.v ((602496177:ℝ)/168755200)/ClassicalSixthBranch.r = (136825159837425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1047
  · change upperPayment 1048 ≤ upperValue ((point split endpoint 4096 1048+point split endpoint 4096 1049)/2)
    have hp : upperPayment 1048 = (356574498252:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1048+point split endpoint 4096 1049)/2 = (602521327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602521327:ℝ)/168755200)*ClassicalSixthBranch.v ((602521327:ℝ)/168755200)/ClassicalSixthBranch.r = (136801263748017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1048
  · change upperPayment 1049 ≤ upperValue ((point split endpoint 4096 1049+point split endpoint 4096 1050)/2)
    have hp : upperPayment 1049 = (356498850861:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1049+point split endpoint 4096 1050)/2 = (602546477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602546477:ℝ)/168755200)*ClassicalSixthBranch.v ((602546477:ℝ)/168755200)/ClassicalSixthBranch.r = (136777369682681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1049
  · change upperPayment 1050 ≤ upperValue ((point split endpoint 4096 1050+point split endpoint 4096 1051)/2)
    have hp : upperPayment 1050 = (356423181325:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1050+point split endpoint 4096 1051)/2 = (602571627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602571627:ℝ)/168755200)*ClassicalSixthBranch.v ((602571627:ℝ)/168755200)/ClassicalSixthBranch.r = (136753477641417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1050
  · change upperPayment 1051 ≤ upperValue ((point split endpoint 4096 1051+point split endpoint 4096 1052)/2)
    have hp : upperPayment 1051 = (356347489639:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1051+point split endpoint 4096 1052)/2 = (602596777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602596777:ℝ)/168755200)*ClassicalSixthBranch.v ((602596777:ℝ)/168755200)/ClassicalSixthBranch.r = (136729587624225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1051
  · change upperPayment 1052 ≤ upperValue ((point split endpoint 4096 1052+point split endpoint 4096 1053)/2)
    have hp : upperPayment 1052 = (356271775801:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1052+point split endpoint 4096 1053)/2 = (602621927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602621927:ℝ)/168755200)*ClassicalSixthBranch.v ((602621927:ℝ)/168755200)/ClassicalSixthBranch.r = (136705699631105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1052
  · change upperPayment 1053 ≤ upperValue ((point split endpoint 4096 1053+point split endpoint 4096 1054)/2)
    have hp : upperPayment 1053 = (356196039807:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1053+point split endpoint 4096 1054)/2 = (602647077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602647077:ℝ)/168755200)*ClassicalSixthBranch.v ((602647077:ℝ)/168755200)/ClassicalSixthBranch.r = (136681813662057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1053
  · change upperPayment 1054 ≤ upperValue ((point split endpoint 4096 1054+point split endpoint 4096 1055)/2)
    have hp : upperPayment 1054 = (356120281653:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1054+point split endpoint 4096 1055)/2 = (602672227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602672227:ℝ)/168755200)*ClassicalSixthBranch.v ((602672227:ℝ)/168755200)/ClassicalSixthBranch.r = (136657929717081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1054
  · change upperPayment 1055 ≤ upperValue ((point split endpoint 4096 1055+point split endpoint 4096 1056)/2)
    have hp : upperPayment 1055 = (356044501336:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1055+point split endpoint 4096 1056)/2 = (602697377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602697377:ℝ)/168755200)*ClassicalSixthBranch.v ((602697377:ℝ)/168755200)/ClassicalSixthBranch.r = (136634047796177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1055
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_065
