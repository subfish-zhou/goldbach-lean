import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints069
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_069 (j : Fin 16) : upperPayment (16*69+j.val) ≤
    upperValue ((point split endpoint 4096 (16*69+j.val)+point split endpoint 4096 (16*69+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1104 ≤ upperValue ((point split endpoint 4096 1104+point split endpoint 4096 1105)/2)
    have hp : upperPayment 1104 = (352304042831:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1104+point split endpoint 4096 1105)/2 = (603929727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603929727:ℝ)/168755200)*ClassicalSixthBranch.v ((603929727:ℝ)/168755200)/ClassicalSixthBranch.r = (135466313160081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1104
  · change upperPayment 1105 ≤ upperValue ((point split endpoint 4096 1105+point split endpoint 4096 1106)/2)
    have hp : upperPayment 1105 = (352227149871:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1105+point split endpoint 4096 1106)/2 = (603954877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603954877:ℝ)/168755200)*ClassicalSixthBranch.v ((603954877:ℝ)/168755200)/ClassicalSixthBranch.r = (135442532442777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1105
  · change upperPayment 1106 ≤ upperValue ((point split endpoint 4096 1106+point split endpoint 4096 1107)/2)
    have hp : upperPayment 1106 = (352150234568:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1106+point split endpoint 4096 1107)/2 = (603980027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603980027:ℝ)/168755200)*ClassicalSixthBranch.v ((603980027:ℝ)/168755200)/ClassicalSixthBranch.r = (135418753749545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1106
  · change upperPayment 1107 ≤ upperValue ((point split endpoint 4096 1107+point split endpoint 4096 1108)/2)
    have hp : upperPayment 1107 = (352073296918:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1107+point split endpoint 4096 1108)/2 = (604005177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604005177:ℝ)/168755200)*ClassicalSixthBranch.v ((604005177:ℝ)/168755200)/ClassicalSixthBranch.r = (135394977080385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1107
  · change upperPayment 1108 ≤ upperValue ((point split endpoint 4096 1108+point split endpoint 4096 1109)/2)
    have hp : upperPayment 1108 = (351996336918:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1108+point split endpoint 4096 1109)/2 = (604030327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604030327:ℝ)/168755200)*ClassicalSixthBranch.v ((604030327:ℝ)/168755200)/ClassicalSixthBranch.r = (135371202435297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1108
  · change upperPayment 1109 ≤ upperValue ((point split endpoint 4096 1109+point split endpoint 4096 1110)/2)
    have hp : upperPayment 1109 = (351919354564:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1109+point split endpoint 4096 1110)/2 = (604055477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604055477:ℝ)/168755200)*ClassicalSixthBranch.v ((604055477:ℝ)/168755200)/ClassicalSixthBranch.r = (135347429814281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1109
  · change upperPayment 1110 ≤ upperValue ((point split endpoint 4096 1110+point split endpoint 4096 1111)/2)
    have hp : upperPayment 1110 = (351842349853:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1110+point split endpoint 4096 1111)/2 = (604080627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604080627:ℝ)/168755200)*ClassicalSixthBranch.v ((604080627:ℝ)/168755200)/ClassicalSixthBranch.r = (135323659217337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1110
  · change upperPayment 1111 ≤ upperValue ((point split endpoint 4096 1111+point split endpoint 4096 1112)/2)
    have hp : upperPayment 1111 = (351765322780:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1111+point split endpoint 4096 1112)/2 = (604105777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604105777:ℝ)/168755200)*ClassicalSixthBranch.v ((604105777:ℝ)/168755200)/ClassicalSixthBranch.r = (135299890644465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1111
  · change upperPayment 1112 ≤ upperValue ((point split endpoint 4096 1112+point split endpoint 4096 1113)/2)
    have hp : upperPayment 1112 = (351688273342:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1112+point split endpoint 4096 1113)/2 = (604130927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604130927:ℝ)/168755200)*ClassicalSixthBranch.v ((604130927:ℝ)/168755200)/ClassicalSixthBranch.r = (135276124095665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1112
  · change upperPayment 1113 ≤ upperValue ((point split endpoint 4096 1113+point split endpoint 4096 1114)/2)
    have hp : upperPayment 1113 = (351611201537:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1113+point split endpoint 4096 1114)/2 = (604156077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604156077:ℝ)/168755200)*ClassicalSixthBranch.v ((604156077:ℝ)/168755200)/ClassicalSixthBranch.r = (135252359570937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1113
  · change upperPayment 1114 ≤ upperValue ((point split endpoint 4096 1114+point split endpoint 4096 1115)/2)
    have hp : upperPayment 1114 = (351534107359:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1114+point split endpoint 4096 1115)/2 = (604181227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604181227:ℝ)/168755200)*ClassicalSixthBranch.v ((604181227:ℝ)/168755200)/ClassicalSixthBranch.r = (135228597070281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1114
  · change upperPayment 1115 ≤ upperValue ((point split endpoint 4096 1115+point split endpoint 4096 1116)/2)
    have hp : upperPayment 1115 = (351456990806:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1115+point split endpoint 4096 1116)/2 = (604206377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604206377:ℝ)/168755200)*ClassicalSixthBranch.v ((604206377:ℝ)/168755200)/ClassicalSixthBranch.r = (135204836593697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1115
  · change upperPayment 1116 ≤ upperValue ((point split endpoint 4096 1116+point split endpoint 4096 1117)/2)
    have hp : upperPayment 1116 = (351379851874:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1116+point split endpoint 4096 1117)/2 = (604231527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604231527:ℝ)/168755200)*ClassicalSixthBranch.v ((604231527:ℝ)/168755200)/ClassicalSixthBranch.r = (135181078141185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1116
  · change upperPayment 1117 ≤ upperValue ((point split endpoint 4096 1117+point split endpoint 4096 1118)/2)
    have hp : upperPayment 1117 = (351302690559:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1117+point split endpoint 4096 1118)/2 = (604256677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604256677:ℝ)/168755200)*ClassicalSixthBranch.v ((604256677:ℝ)/168755200)/ClassicalSixthBranch.r = (135157321712745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1117
  · change upperPayment 1118 ≤ upperValue ((point split endpoint 4096 1118+point split endpoint 4096 1119)/2)
    have hp : upperPayment 1118 = (351225506858:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1118+point split endpoint 4096 1119)/2 = (604281827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604281827:ℝ)/168755200)*ClassicalSixthBranch.v ((604281827:ℝ)/168755200)/ClassicalSixthBranch.r = (135133567308377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1118
  · change upperPayment 1119 ≤ upperValue ((point split endpoint 4096 1119+point split endpoint 4096 1120)/2)
    have hp : upperPayment 1119 = (351148300768:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1119+point split endpoint 4096 1120)/2 = (604306977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604306977:ℝ)/168755200)*ClassicalSixthBranch.v ((604306977:ℝ)/168755200)/ClassicalSixthBranch.r = (135109814928081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1119
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_069
