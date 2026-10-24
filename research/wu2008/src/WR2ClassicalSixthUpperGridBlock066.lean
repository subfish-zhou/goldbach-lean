import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints066
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_066 (j : Fin 16) : upperPayment (16*66+j.val) ≤
    upperValue ((point split endpoint 4096 (16*66+j.val)+point split endpoint 4096 (16*66+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1056 ≤ upperValue ((point split endpoint 4096 1056+point split endpoint 4096 1057)/2)
    have hp : upperPayment 1056 = (355968698852:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1056+point split endpoint 4096 1057)/2 = (602722527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602722527:ℝ)/168755200)*ClassicalSixthBranch.v ((602722527:ℝ)/168755200)/ClassicalSixthBranch.r = (136610167899345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1056
  · change upperPayment 1057 ≤ upperValue ((point split endpoint 4096 1057+point split endpoint 4096 1058)/2)
    have hp : upperPayment 1057 = (355892874198:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1057+point split endpoint 4096 1058)/2 = (602747677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602747677:ℝ)/168755200)*ClassicalSixthBranch.v ((602747677:ℝ)/168755200)/ClassicalSixthBranch.r = (1326080485695:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1057
  · change upperPayment 1058 ≤ upperValue ((point split endpoint 4096 1058+point split endpoint 4096 1059)/2)
    have hp : upperPayment 1058 = (355817027371:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1058+point split endpoint 4096 1059)/2 = (602772827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602772827:ℝ)/168755200)*ClassicalSixthBranch.v ((602772827:ℝ)/168755200)/ClassicalSixthBranch.r = (136562414177897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1058
  · change upperPayment 1059 ≤ upperValue ((point split endpoint 4096 1059+point split endpoint 4096 1060)/2)
    have hp : upperPayment 1059 = (355741158366:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1059+point split endpoint 4096 1060)/2 = (602797977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602797977:ℝ)/168755200)*ClassicalSixthBranch.v ((602797977:ℝ)/168755200)/ClassicalSixthBranch.r = (136538540353281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1059
  · change upperPayment 1060 ≤ upperValue ((point split endpoint 4096 1060+point split endpoint 4096 1061)/2)
    have hp : upperPayment 1060 = (355665267181:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1060+point split endpoint 4096 1061)/2 = (602823127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602823127:ℝ)/168755200)*ClassicalSixthBranch.v ((602823127:ℝ)/168755200)/ClassicalSixthBranch.r = (136514668552737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1060
  · change upperPayment 1061 ≤ upperValue ((point split endpoint 4096 1061+point split endpoint 4096 1062)/2)
    have hp : upperPayment 1061 = (355589353811:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1061+point split endpoint 4096 1062)/2 = (602848277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602848277:ℝ)/168755200)*ClassicalSixthBranch.v ((602848277:ℝ)/168755200)/ClassicalSixthBranch.r = (136490798776265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1061
  · change upperPayment 1062 ≤ upperValue ((point split endpoint 4096 1062+point split endpoint 4096 1063)/2)
    have hp : upperPayment 1062 = (355513418255:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1062+point split endpoint 4096 1063)/2 = (602873427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602873427:ℝ)/168755200)*ClassicalSixthBranch.v ((602873427:ℝ)/168755200)/ClassicalSixthBranch.r = (136466931023865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1062
  · change upperPayment 1063 ≤ upperValue ((point split endpoint 4096 1063+point split endpoint 4096 1064)/2)
    have hp : upperPayment 1063 = (355437460506:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1063+point split endpoint 4096 1064)/2 = (602898577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602898577:ℝ)/168755200)*ClassicalSixthBranch.v ((602898577:ℝ)/168755200)/ClassicalSixthBranch.r = (136443065295537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1063
  · change upperPayment 1064 ≤ upperValue ((point split endpoint 4096 1064+point split endpoint 4096 1065)/2)
    have hp : upperPayment 1064 = (355361480564:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1064+point split endpoint 4096 1065)/2 = (602923727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602923727:ℝ)/168755200)*ClassicalSixthBranch.v ((602923727:ℝ)/168755200)/ClassicalSixthBranch.r = (136419201591281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1064
  · change upperPayment 1065 ≤ upperValue ((point split endpoint 4096 1065+point split endpoint 4096 1066)/2)
    have hp : upperPayment 1065 = (355285478423:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1065+point split endpoint 4096 1066)/2 = (602948877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602948877:ℝ)/168755200)*ClassicalSixthBranch.v ((602948877:ℝ)/168755200)/ClassicalSixthBranch.r = (136395339911097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1065
  · change upperPayment 1066 ≤ upperValue ((point split endpoint 4096 1066+point split endpoint 4096 1067)/2)
    have hp : upperPayment 1066 = (355209454081:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1066+point split endpoint 4096 1067)/2 = (602974027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602974027:ℝ)/168755200)*ClassicalSixthBranch.v ((602974027:ℝ)/168755200)/ClassicalSixthBranch.r = (136371480254985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1066
  · change upperPayment 1067 ≤ upperValue ((point split endpoint 4096 1067+point split endpoint 4096 1068)/2)
    have hp : upperPayment 1067 = (355133407533:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1067+point split endpoint 4096 1068)/2 = (602999177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602999177:ℝ)/168755200)*ClassicalSixthBranch.v ((602999177:ℝ)/168755200)/ClassicalSixthBranch.r = (136347622622945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1067
  · change upperPayment 1068 ≤ upperValue ((point split endpoint 4096 1068+point split endpoint 4096 1069)/2)
    have hp : upperPayment 1068 = (355057338777:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1068+point split endpoint 4096 1069)/2 = (603024327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603024327:ℝ)/168755200)*ClassicalSixthBranch.v ((603024327:ℝ)/168755200)/ClassicalSixthBranch.r = (136323767014977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1068
  · change upperPayment 1069 ≤ upperValue ((point split endpoint 4096 1069+point split endpoint 4096 1070)/2)
    have hp : upperPayment 1069 = (354981247808:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1069+point split endpoint 4096 1070)/2 = (603049477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603049477:ℝ)/168755200)*ClassicalSixthBranch.v ((603049477:ℝ)/168755200)/ClassicalSixthBranch.r = (136299913431081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1069
  · change upperPayment 1070 ≤ upperValue ((point split endpoint 4096 1070+point split endpoint 4096 1071)/2)
    have hp : upperPayment 1070 = (354905134624:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1070+point split endpoint 4096 1071)/2 = (603074627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603074627:ℝ)/168755200)*ClassicalSixthBranch.v ((603074627:ℝ)/168755200)/ClassicalSixthBranch.r = (136276061871257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1070
  · change upperPayment 1071 ≤ upperValue ((point split endpoint 4096 1071+point split endpoint 4096 1072)/2)
    have hp : upperPayment 1071 = (354828999221:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1071+point split endpoint 4096 1072)/2 = (603099777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((603099777:ℝ)/168755200)*ClassicalSixthBranch.v ((603099777:ℝ)/168755200)/ClassicalSixthBranch.r = (136252212335505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1071
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_066
