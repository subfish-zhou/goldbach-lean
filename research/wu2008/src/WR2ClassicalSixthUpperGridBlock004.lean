import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints004
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_004 (j : Fin 16) : upperPayment (16*4+j.val) ≤
    upperValue ((point split endpoint 4096 (16*4+j.val)+point split endpoint 4096 (16*4+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 64 ≤ upperValue ((point split endpoint 4096 64+point split endpoint 4096 65)/2)
    have hp : upperPayment 64 = (420778238401:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 64+point split endpoint 4096 65)/2 = (577773727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577773727:ℝ)/168755200)*ClassicalSixthBranch.v ((577773727:ℝ)/168755200)/ClassicalSixthBranch.r = (161293929811281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_64
  · change upperPayment 65 ≤ upperValue ((point split endpoint 4096 65+point split endpoint 4096 66)/2)
    have hp : upperPayment 65 = (420722918174:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 65+point split endpoint 4096 66)/2 = (577798877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577798877:ℝ)/168755200)*ClassicalSixthBranch.v ((577798877:ℝ)/168755200)/ClassicalSixthBranch.r = (161268044059097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_65
  · change upperPayment 66 ≤ upperValue ((point split endpoint 4096 66+point split endpoint 4096 67)/2)
    have hp : upperPayment 66 = (420667578561:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 66+point split endpoint 4096 67)/2 = (577824027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577824027:ℝ)/168755200)*ClassicalSixthBranch.v ((577824027:ℝ)/168755200)/ClassicalSixthBranch.r = (161242160330985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_66
  · change upperPayment 67 ≤ upperValue ((point split endpoint 4096 67+point split endpoint 4096 68)/2)
    have hp : upperPayment 67 = (420612219560:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 67+point split endpoint 4096 68)/2 = (577849177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577849177:ℝ)/168755200)*ClassicalSixthBranch.v ((577849177:ℝ)/168755200)/ClassicalSixthBranch.r = (161216278626945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_67
  · change upperPayment 68 ≤ upperValue ((point split endpoint 4096 68+point split endpoint 4096 69)/2)
    have hp : upperPayment 68 = (420556841168:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 68+point split endpoint 4096 69)/2 = (577874327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577874327:ℝ)/168755200)*ClassicalSixthBranch.v ((577874327:ℝ)/168755200)/ClassicalSixthBranch.r = (161190398946977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_68
  · change upperPayment 69 ≤ upperValue ((point split endpoint 4096 69+point split endpoint 4096 70)/2)
    have hp : upperPayment 69 = (420501443383:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 69+point split endpoint 4096 70)/2 = (577899477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577899477:ℝ)/168755200)*ClassicalSixthBranch.v ((577899477:ℝ)/168755200)/ClassicalSixthBranch.r = (161164521291081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_69
  · change upperPayment 70 ≤ upperValue ((point split endpoint 4096 70+point split endpoint 4096 71)/2)
    have hp : upperPayment 70 = (420446026204:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 70+point split endpoint 4096 71)/2 = (577924627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577924627:ℝ)/168755200)*ClassicalSixthBranch.v ((577924627:ℝ)/168755200)/ClassicalSixthBranch.r = (161138645659257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_70
  · change upperPayment 71 ≤ upperValue ((point split endpoint 4096 71+point split endpoint 4096 72)/2)
    have hp : upperPayment 71 = (420390589627:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 71+point split endpoint 4096 72)/2 = (577949777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577949777:ℝ)/168755200)*ClassicalSixthBranch.v ((577949777:ℝ)/168755200)/ClassicalSixthBranch.r = (161112772051505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_71
  · change upperPayment 72 ≤ upperValue ((point split endpoint 4096 72+point split endpoint 4096 73)/2)
    have hp : upperPayment 72 = (420335133651:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 72+point split endpoint 4096 73)/2 = (577974927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577974927:ℝ)/168755200)*ClassicalSixthBranch.v ((577974927:ℝ)/168755200)/ClassicalSixthBranch.r = (161086900467825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_72
  · change upperPayment 73 ≤ upperValue ((point split endpoint 4096 73+point split endpoint 4096 74)/2)
    have hp : upperPayment 73 = (420279658274:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 73+point split endpoint 4096 74)/2 = (578000077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578000077:ℝ)/168755200)*ClassicalSixthBranch.v ((578000077:ℝ)/168755200)/ClassicalSixthBranch.r = (161061030908217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_73
  · change upperPayment 74 ≤ upperValue ((point split endpoint 4096 74+point split endpoint 4096 75)/2)
    have hp : upperPayment 74 = (420224163493:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 74+point split endpoint 4096 75)/2 = (578025227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578025227:ℝ)/168755200)*ClassicalSixthBranch.v ((578025227:ℝ)/168755200)/ClassicalSixthBranch.r = (161035163372681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_74
  · change upperPayment 75 ≤ upperValue ((point split endpoint 4096 75+point split endpoint 4096 76)/2)
    have hp : upperPayment 75 = (420168649306:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 75+point split endpoint 4096 76)/2 = (578050377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578050377:ℝ)/168755200)*ClassicalSixthBranch.v ((578050377:ℝ)/168755200)/ClassicalSixthBranch.r = (161009297861217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_75
  · change upperPayment 76 ≤ upperValue ((point split endpoint 4096 76+point split endpoint 4096 77)/2)
    have hp : upperPayment 76 = (420113115712:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 76+point split endpoint 4096 77)/2 = (578075527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578075527:ℝ)/168755200)*ClassicalSixthBranch.v ((578075527:ℝ)/168755200)/ClassicalSixthBranch.r = (160983434373825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_76
  · change upperPayment 77 ≤ upperValue ((point split endpoint 4096 77+point split endpoint 4096 78)/2)
    have hp : upperPayment 77 = (420057562707:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 77+point split endpoint 4096 78)/2 = (578100677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578100677:ℝ)/168755200)*ClassicalSixthBranch.v ((578100677:ℝ)/168755200)/ClassicalSixthBranch.r = (160957572910505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_77
  · change upperPayment 78 ≤ upperValue ((point split endpoint 4096 78+point split endpoint 4096 79)/2)
    have hp : upperPayment 78 = (420001990289:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 78+point split endpoint 4096 79)/2 = (578125827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578125827:ℝ)/168755200)*ClassicalSixthBranch.v ((578125827:ℝ)/168755200)/ClassicalSixthBranch.r = (160931713471257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_78
  · change upperPayment 79 ≤ upperValue ((point split endpoint 4096 79+point split endpoint 4096 80)/2)
    have hp : upperPayment 79 = (419946398457:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 79+point split endpoint 4096 80)/2 = (578150977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578150977:ℝ)/168755200)*ClassicalSixthBranch.v ((578150977:ℝ)/168755200)/ClassicalSixthBranch.r = (160905856056081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_79
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_004
