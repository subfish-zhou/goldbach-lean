import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints003
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_003 (j : Fin 16) : upperPayment (16*3+j.val) ≤
    upperValue ((point split endpoint 4096 (16*3+j.val)+point split endpoint 4096 (16*3+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 48 ≤ upperValue ((point split endpoint 4096 48+point split endpoint 4096 49)/2)
    have hp : upperPayment 48 = (421660727287:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 48+point split endpoint 4096 49)/2 = (577371327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577371327:ℝ)/168755200)*ClassicalSixthBranch.v ((577371327:ℝ)/168755200)/ClassicalSixthBranch.r = (161708377120017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_48
  · change upperPayment 49 ≤ upperValue ((point split endpoint 4096 49+point split endpoint 4096 50)/2)
    have hp : upperPayment 49 = (421605716944:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 49+point split endpoint 4096 50)/2 = (577396477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577396477:ℝ)/168755200)*ClassicalSixthBranch.v ((577396477:ℝ)/168755200)/ClassicalSixthBranch.r = (161682458982681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_49
  · change upperPayment 50 ≤ upperValue ((point split endpoint 4096 50+point split endpoint 4096 51)/2)
    have hp : upperPayment 50 = (421550687248:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 50+point split endpoint 4096 51)/2 = (577421627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577421627:ℝ)/168755200)*ClassicalSixthBranch.v ((577421627:ℝ)/168755200)/ClassicalSixthBranch.r = (161656542869417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_50
  · change upperPayment 51 ≤ upperValue ((point split endpoint 4096 51+point split endpoint 4096 52)/2)
    have hp : upperPayment 51 = (421495638199:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 51+point split endpoint 4096 52)/2 = (577446777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577446777:ℝ)/168755200)*ClassicalSixthBranch.v ((577446777:ℝ)/168755200)/ClassicalSixthBranch.r = (161630628780225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_51
  · change upperPayment 52 ≤ upperValue ((point split endpoint 4096 52+point split endpoint 4096 53)/2)
    have hp : upperPayment 52 = (421440569795:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 52+point split endpoint 4096 53)/2 = (577471927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577471927:ℝ)/168755200)*ClassicalSixthBranch.v ((577471927:ℝ)/168755200)/ClassicalSixthBranch.r = (161604716715105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_52
  · change upperPayment 53 ≤ upperValue ((point split endpoint 4096 53+point split endpoint 4096 54)/2)
    have hp : upperPayment 53 = (421385482032:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 53+point split endpoint 4096 54)/2 = (577497077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577497077:ℝ)/168755200)*ClassicalSixthBranch.v ((577497077:ℝ)/168755200)/ClassicalSixthBranch.r = (161578806674057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_53
  · change upperPayment 54 ≤ upperValue ((point split endpoint 4096 54+point split endpoint 4096 55)/2)
    have hp : upperPayment 54 = (421330374910:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 54+point split endpoint 4096 55)/2 = (577522227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577522227:ℝ)/168755200)*ClassicalSixthBranch.v ((577522227:ℝ)/168755200)/ClassicalSixthBranch.r = (161552898657081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_54
  · change upperPayment 55 ≤ upperValue ((point split endpoint 4096 55+point split endpoint 4096 56)/2)
    have hp : upperPayment 55 = (421275248425:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 55+point split endpoint 4096 56)/2 = (577547377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577547377:ℝ)/168755200)*ClassicalSixthBranch.v ((577547377:ℝ)/168755200)/ClassicalSixthBranch.r = (161526992664177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_55
  · change upperPayment 56 ≤ upperValue ((point split endpoint 4096 56+point split endpoint 4096 57)/2)
    have hp : upperPayment 56 = (421220102575:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 56+point split endpoint 4096 57)/2 = (577572527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577572527:ℝ)/168755200)*ClassicalSixthBranch.v ((577572527:ℝ)/168755200)/ClassicalSixthBranch.r = (161501088695345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_56
  · change upperPayment 57 ≤ upperValue ((point split endpoint 4096 57+point split endpoint 4096 58)/2)
    have hp : upperPayment 57 = (421164937359:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 57+point split endpoint 4096 58)/2 = (577597677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577597677:ℝ)/168755200)*ClassicalSixthBranch.v ((577597677:ℝ)/168755200)/ClassicalSixthBranch.r = (161475186750585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_57
  · change upperPayment 58 ≤ upperValue ((point split endpoint 4096 58+point split endpoint 4096 59)/2)
    have hp : upperPayment 58 = (421109752775:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 58+point split endpoint 4096 59)/2 = (577622827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577622827:ℝ)/168755200)*ClassicalSixthBranch.v ((577622827:ℝ)/168755200)/ClassicalSixthBranch.r = (161449286829897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_58
  · change upperPayment 59 ≤ upperValue ((point split endpoint 4096 59+point split endpoint 4096 60)/2)
    have hp : upperPayment 59 = (421054548819:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 59+point split endpoint 4096 60)/2 = (577647977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577647977:ℝ)/168755200)*ClassicalSixthBranch.v ((577647977:ℝ)/168755200)/ClassicalSixthBranch.r = (161423388933281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_59
  · change upperPayment 60 ≤ upperValue ((point split endpoint 4096 60+point split endpoint 4096 61)/2)
    have hp : upperPayment 60 = (420999325490:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 60+point split endpoint 4096 61)/2 = (577673127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577673127:ℝ)/168755200)*ClassicalSixthBranch.v ((577673127:ℝ)/168755200)/ClassicalSixthBranch.r = (161397493060737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_60
  · change upperPayment 61 ≤ upperValue ((point split endpoint 4096 61+point split endpoint 4096 62)/2)
    have hp : upperPayment 61 = (420944082786:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 61+point split endpoint 4096 62)/2 = (577698277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577698277:ℝ)/168755200)*ClassicalSixthBranch.v ((577698277:ℝ)/168755200)/ClassicalSixthBranch.r = (161371599212265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_61
  · change upperPayment 62 ≤ upperValue ((point split endpoint 4096 62+point split endpoint 4096 63)/2)
    have hp : upperPayment 62 = (420888820705:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 62+point split endpoint 4096 63)/2 = (577723427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577723427:ℝ)/168755200)*ClassicalSixthBranch.v ((577723427:ℝ)/168755200)/ClassicalSixthBranch.r = (161345707387865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_62
  · change upperPayment 63 ≤ upperValue ((point split endpoint 4096 63+point split endpoint 4096 64)/2)
    have hp : upperPayment 63 = (420833539244:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 63+point split endpoint 4096 64)/2 = (577748577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577748577:ℝ)/168755200)*ClassicalSixthBranch.v ((577748577:ℝ)/168755200)/ClassicalSixthBranch.r = (161319817587537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_63
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_003
