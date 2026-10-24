import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints170
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_170 (j : Fin 16) : upperPayment (16*170+j.val) ≤
    upperValue ((point split endpoint 4096 (16*170+j.val)+point split endpoint 4096 (16*170+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2720 ≤ upperValue ((point split endpoint 4096 2720+point split endpoint 4096 2721)/2)
    have hp : upperPayment 2720 = (195894388072:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2720+point split endpoint 4096 2721)/2 = (644572127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644572127:ℝ)/168755200)*ClassicalSixthBranch.v ((644572127:ℝ)/168755200)/ClassicalSixthBranch.r = (99677926031057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2720
  · change upperPayment 2721 ≤ upperValue ((point split endpoint 4096 2721+point split endpoint 4096 2722)/2)
    have hp : upperPayment 2721 = (195775483321:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2721+point split endpoint 4096 2722)/2 = (644597277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644597277:ℝ)/168755200)*ClassicalSixthBranch.v ((644597277:ℝ)/168755200)/ClassicalSixthBranch.r = (99657416214105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2721
  · change upperPayment 2722 ≤ upperValue ((point split endpoint 4096 2722+point split endpoint 4096 2723)/2)
    have hp : upperPayment 2722 = (195656548021:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2722+point split endpoint 4096 2723)/2 = (644622427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644622427:ℝ)/168755200)*ClassicalSixthBranch.v ((644622427:ℝ)/168755200)/ClassicalSixthBranch.r = (99636908421225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2722
  · change upperPayment 2723 ≤ upperValue ((point split endpoint 4096 2723+point split endpoint 4096 2724)/2)
    have hp : upperPayment 2723 = (195537582164:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2723+point split endpoint 4096 2724)/2 = (644647577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644647577:ℝ)/168755200)*ClassicalSixthBranch.v ((644647577:ℝ)/168755200)/ClassicalSixthBranch.r = (99616402652417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2723
  · change upperPayment 2724 ≤ upperValue ((point split endpoint 4096 2724+point split endpoint 4096 2725)/2)
    have hp : upperPayment 2724 = (195418585745:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2724+point split endpoint 4096 2725)/2 = (644672727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644672727:ℝ)/168755200)*ClassicalSixthBranch.v ((644672727:ℝ)/168755200)/ClassicalSixthBranch.r = (99595898907681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2724
  · change upperPayment 2725 ≤ upperValue ((point split endpoint 4096 2725+point split endpoint 4096 2726)/2)
    have hp : upperPayment 2725 = (195299558755:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2725+point split endpoint 4096 2726)/2 = (644697877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644697877:ℝ)/168755200)*ClassicalSixthBranch.v ((644697877:ℝ)/168755200)/ClassicalSixthBranch.r = (99575397187017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2725
  · change upperPayment 2726 ≤ upperValue ((point split endpoint 4096 2726+point split endpoint 4096 2727)/2)
    have hp : upperPayment 2726 = (195180501189:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2726+point split endpoint 4096 2727)/2 = (644723027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644723027:ℝ)/168755200)*ClassicalSixthBranch.v ((644723027:ℝ)/168755200)/ClassicalSixthBranch.r = (99554897490425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2726
  · change upperPayment 2727 ≤ upperValue ((point split endpoint 4096 2727+point split endpoint 4096 2728)/2)
    have hp : upperPayment 2727 = (195061413039:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2727+point split endpoint 4096 2728)/2 = (644748177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644748177:ℝ)/168755200)*ClassicalSixthBranch.v ((644748177:ℝ)/168755200)/ClassicalSixthBranch.r = (99534399817905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2727
  · change upperPayment 2728 ≤ upperValue ((point split endpoint 4096 2728+point split endpoint 4096 2729)/2)
    have hp : upperPayment 2728 = (194942294299:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2728+point split endpoint 4096 2729)/2 = (644773327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644773327:ℝ)/168755200)*ClassicalSixthBranch.v ((644773327:ℝ)/168755200)/ClassicalSixthBranch.r = (99513904169457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2728
  · change upperPayment 2729 ≤ upperValue ((point split endpoint 4096 2729+point split endpoint 4096 2730)/2)
    have hp : upperPayment 2729 = (194823144960:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2729+point split endpoint 4096 2730)/2 = (644798477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644798477:ℝ)/168755200)*ClassicalSixthBranch.v ((644798477:ℝ)/168755200)/ClassicalSixthBranch.r = (99493410545081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2729
  · change upperPayment 2730 ≤ upperValue ((point split endpoint 4096 2730+point split endpoint 4096 2731)/2)
    have hp : upperPayment 2730 = (194703965017:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2730+point split endpoint 4096 2731)/2 = (644823627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644823627:ℝ)/168755200)*ClassicalSixthBranch.v ((644823627:ℝ)/168755200)/ClassicalSixthBranch.r = (99472918944777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2730
  · change upperPayment 2731 ≤ upperValue ((point split endpoint 4096 2731+point split endpoint 4096 2732)/2)
    have hp : upperPayment 2731 = (194584754463:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2731+point split endpoint 4096 2732)/2 = (644848777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644848777:ℝ)/168755200)*ClassicalSixthBranch.v ((644848777:ℝ)/168755200)/ClassicalSixthBranch.r = (99452429368545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2731
  · change upperPayment 2732 ≤ upperValue ((point split endpoint 4096 2732+point split endpoint 4096 2733)/2)
    have hp : upperPayment 2732 = (194465513290:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2732+point split endpoint 4096 2733)/2 = (644873927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644873927:ℝ)/168755200)*ClassicalSixthBranch.v ((644873927:ℝ)/168755200)/ClassicalSixthBranch.r = (99431941816385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2732
  · change upperPayment 2733 ≤ upperValue ((point split endpoint 4096 2733+point split endpoint 4096 2734)/2)
    have hp : upperPayment 2733 = (194346241492:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2733+point split endpoint 4096 2734)/2 = (644899077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644899077:ℝ)/168755200)*ClassicalSixthBranch.v ((644899077:ℝ)/168755200)/ClassicalSixthBranch.r = (99411456288297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2733
  · change upperPayment 2734 ≤ upperValue ((point split endpoint 4096 2734+point split endpoint 4096 2735)/2)
    have hp : upperPayment 2734 = (194226939062:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2734+point split endpoint 4096 2735)/2 = (644924227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644924227:ℝ)/168755200)*ClassicalSixthBranch.v ((644924227:ℝ)/168755200)/ClassicalSixthBranch.r = (99390972784281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2734
  · change upperPayment 2735 ≤ upperValue ((point split endpoint 4096 2735+point split endpoint 4096 2736)/2)
    have hp : upperPayment 2735 = (194107605992:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2735+point split endpoint 4096 2736)/2 = (644949377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644949377:ℝ)/168755200)*ClassicalSixthBranch.v ((644949377:ℝ)/168755200)/ClassicalSixthBranch.r = (99370491304337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2735
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_170
