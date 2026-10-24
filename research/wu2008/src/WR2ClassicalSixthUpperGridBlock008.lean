import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints008
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_008 (j : Fin 16) : upperPayment (16*8+j.val) ≤
    upperValue ((point split endpoint 4096 (16*8+j.val)+point split endpoint 4096 (16*8+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 128 ≤ upperValue ((point split endpoint 4096 128+point split endpoint 4096 129)/2)
    have hp : upperPayment 128 = (417198569811:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 128+point split endpoint 4096 129)/2 = (579383327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579383327:ℝ)/168755200)*ClassicalSixthBranch.v ((579383327:ℝ)/168755200)/ClassicalSixthBranch.r = (159641322200657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_128
  · change upperPayment 129 ≤ upperValue ((point split endpoint 4096 129+point split endpoint 4096 130)/2)
    have hp : upperPayment 129 = (417142004426:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 129+point split endpoint 4096 130)/2 = (579408477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579408477:ℝ)/168755200)*ClassicalSixthBranch.v ((579408477:ℝ)/168755200)/ClassicalSixthBranch.r = (159615565989081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_129
  · change upperPayment 130 ≤ upperValue ((point split endpoint 4096 130+point split endpoint 4096 131)/2)
    have hp : upperPayment 130 = (417085419513:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 130+point split endpoint 4096 131)/2 = (579433627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579433627:ℝ)/168755200)*ClassicalSixthBranch.v ((579433627:ℝ)/168755200)/ClassicalSixthBranch.r = (1549415648559:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_130
  · change upperPayment 131 ≤ upperValue ((point split endpoint 4096 131+point split endpoint 4096 132)/2)
    have hp : upperPayment 131 = (417028815070:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 131+point split endpoint 4096 132)/2 = (579458777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579458777:ℝ)/168755200)*ClassicalSixthBranch.v ((579458777:ℝ)/168755200)/ClassicalSixthBranch.r = (159564059638145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_131
  · change upperPayment 132 ≤ upperValue ((point split endpoint 4096 132+point split endpoint 4096 133)/2)
    have hp : upperPayment 132 = (416972191094:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 132+point split endpoint 4096 133)/2 = (579483927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579483927:ℝ)/168755200)*ClassicalSixthBranch.v ((579483927:ℝ)/168755200)/ClassicalSixthBranch.r = (159538309498785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_132
  · change upperPayment 133 ≤ upperValue ((point split endpoint 4096 133+point split endpoint 4096 134)/2)
    have hp : upperPayment 133 = (416915547584:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 133+point split endpoint 4096 134)/2 = (579509077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579509077:ℝ)/168755200)*ClassicalSixthBranch.v ((579509077:ℝ)/168755200)/ClassicalSixthBranch.r = (159512561383497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_133
  · change upperPayment 134 ≤ upperValue ((point split endpoint 4096 134+point split endpoint 4096 135)/2)
    have hp : upperPayment 134 = (416858884536:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 134+point split endpoint 4096 135)/2 = (579534227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579534227:ℝ)/168755200)*ClassicalSixthBranch.v ((579534227:ℝ)/168755200)/ClassicalSixthBranch.r = (159486815292281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_134
  · change upperPayment 135 ≤ upperValue ((point split endpoint 4096 135+point split endpoint 4096 136)/2)
    have hp : upperPayment 135 = (416802201949:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 135+point split endpoint 4096 136)/2 = (579559377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579559377:ℝ)/168755200)*ClassicalSixthBranch.v ((579559377:ℝ)/168755200)/ClassicalSixthBranch.r = (159461071225137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_135
  · change upperPayment 136 ≤ upperValue ((point split endpoint 4096 136+point split endpoint 4096 137)/2)
    have hp : upperPayment 136 = (416745499821:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 136+point split endpoint 4096 137)/2 = (579584527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579584527:ℝ)/168755200)*ClassicalSixthBranch.v ((579584527:ℝ)/168755200)/ClassicalSixthBranch.r = (159435329182065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_136
  · change upperPayment 137 ≤ upperValue ((point split endpoint 4096 137+point split endpoint 4096 138)/2)
    have hp : upperPayment 137 = (416688778148:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 137+point split endpoint 4096 138)/2 = (579609677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579609677:ℝ)/168755200)*ClassicalSixthBranch.v ((579609677:ℝ)/168755200)/ClassicalSixthBranch.r = (159409589163065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_137
  · change upperPayment 138 ≤ upperValue ((point split endpoint 4096 138+point split endpoint 4096 139)/2)
    have hp : upperPayment 138 = (416632036930:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 138+point split endpoint 4096 139)/2 = (579634827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579634827:ℝ)/168755200)*ClassicalSixthBranch.v ((579634827:ℝ)/168755200)/ClassicalSixthBranch.r = (159383851168137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_138
  · change upperPayment 139 ≤ upperValue ((point split endpoint 4096 139+point split endpoint 4096 140)/2)
    have hp : upperPayment 139 = (416575276163:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 139+point split endpoint 4096 140)/2 = (579659977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579659977:ℝ)/168755200)*ClassicalSixthBranch.v ((579659977:ℝ)/168755200)/ClassicalSixthBranch.r = (159358115197281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_139
  · change upperPayment 140 ≤ upperValue ((point split endpoint 4096 140+point split endpoint 4096 141)/2)
    have hp : upperPayment 140 = (416518495845:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 140+point split endpoint 4096 141)/2 = (579685127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579685127:ℝ)/168755200)*ClassicalSixthBranch.v ((579685127:ℝ)/168755200)/ClassicalSixthBranch.r = (159332381250497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_140
  · change upperPayment 141 ≤ upperValue ((point split endpoint 4096 141+point split endpoint 4096 142)/2)
    have hp : upperPayment 141 = (416461695974:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 141+point split endpoint 4096 142)/2 = (579710277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579710277:ℝ)/168755200)*ClassicalSixthBranch.v ((579710277:ℝ)/168755200)/ClassicalSixthBranch.r = (159306649327785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_141
  · change upperPayment 142 ≤ upperValue ((point split endpoint 4096 142+point split endpoint 4096 143)/2)
    have hp : upperPayment 142 = (416404876549:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 142+point split endpoint 4096 143)/2 = (579735427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579735427:ℝ)/168755200)*ClassicalSixthBranch.v ((579735427:ℝ)/168755200)/ClassicalSixthBranch.r = (159280919429145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_142
  · change upperPayment 143 ≤ upperValue ((point split endpoint 4096 143+point split endpoint 4096 144)/2)
    have hp : upperPayment 143 = (416348037566:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 143+point split endpoint 4096 144)/2 = (579760577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579760577:ℝ)/168755200)*ClassicalSixthBranch.v ((579760577:ℝ)/168755200)/ClassicalSixthBranch.r = (159255191554577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_143
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_008
