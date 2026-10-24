import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints002
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_002 (j : Fin 16) : upperPayment (16*2+j.val) ≤
    upperValue ((point split endpoint 4096 (16*2+j.val)+point split endpoint 4096 (16*2+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 32 ≤ upperValue ((point split endpoint 4096 32+point split endpoint 4096 33)/2)
    have hp : upperPayment 32 = (422538262752:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 32+point split endpoint 4096 33)/2 = (576968927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576968927:ℝ)/168755200)*ClassicalSixthBranch.v ((576968927:ℝ)/168755200)/ClassicalSixthBranch.r = (162123342591185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_32
  · change upperPayment 33 ≤ upperValue ((point split endpoint 4096 33+point split endpoint 4096 34)/2)
    have hp : upperPayment 33 = (422483561738:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 33+point split endpoint 4096 34)/2 = (576994077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576994077:ℝ)/168755200)*ClassicalSixthBranch.v ((576994077:ℝ)/168755200)/ClassicalSixthBranch.r = (162097392068697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_33
  · change upperPayment 34 ≤ upperValue ((point split endpoint 4096 34+point split endpoint 4096 35)/2)
    have hp : upperPayment 34 = (422428841407:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 34+point split endpoint 4096 35)/2 = (577019227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577019227:ℝ)/168755200)*ClassicalSixthBranch.v ((577019227:ℝ)/168755200)/ClassicalSixthBranch.r = (162071443570281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_34
  · change upperPayment 35 ≤ upperValue ((point split endpoint 4096 35+point split endpoint 4096 36)/2)
    have hp : upperPayment 35 = (422374101757:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 35+point split endpoint 4096 36)/2 = (577044377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577044377:ℝ)/168755200)*ClassicalSixthBranch.v ((577044377:ℝ)/168755200)/ClassicalSixthBranch.r = (162045497095937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_35
  · change upperPayment 36 ≤ upperValue ((point split endpoint 4096 36+point split endpoint 4096 37)/2)
    have hp : upperPayment 36 = (422319342786:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 36+point split endpoint 4096 37)/2 = (577069527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577069527:ℝ)/168755200)*ClassicalSixthBranch.v ((577069527:ℝ)/168755200)/ClassicalSixthBranch.r = (162019552645665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_36
  · change upperPayment 37 ≤ upperValue ((point split endpoint 4096 37+point split endpoint 4096 38)/2)
    have hp : upperPayment 37 = (422264564491:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 37+point split endpoint 4096 38)/2 = (577094677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577094677:ℝ)/168755200)*ClassicalSixthBranch.v ((577094677:ℝ)/168755200)/ClassicalSixthBranch.r = (161993610219465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_37
  · change upperPayment 38 ≤ upperValue ((point split endpoint 4096 38+point split endpoint 4096 39)/2)
    have hp : upperPayment 38 = (422209766871:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 38+point split endpoint 4096 39)/2 = (577119827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577119827:ℝ)/168755200)*ClassicalSixthBranch.v ((577119827:ℝ)/168755200)/ClassicalSixthBranch.r = (161967669817337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_38
  · change upperPayment 39 ≤ upperValue ((point split endpoint 4096 39+point split endpoint 4096 40)/2)
    have hp : upperPayment 39 = (422154949923:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 39+point split endpoint 4096 40)/2 = (577144977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577144977:ℝ)/168755200)*ClassicalSixthBranch.v ((577144977:ℝ)/168755200)/ClassicalSixthBranch.r = (161941731439281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_39
  · change upperPayment 40 ≤ upperValue ((point split endpoint 4096 40+point split endpoint 4096 41)/2)
    have hp : upperPayment 40 = (422100113645:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 40+point split endpoint 4096 41)/2 = (577170127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577170127:ℝ)/168755200)*ClassicalSixthBranch.v ((577170127:ℝ)/168755200)/ClassicalSixthBranch.r = (161915795085297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_40
  · change upperPayment 41 ≤ upperValue ((point split endpoint 4096 41+point split endpoint 4096 42)/2)
    have hp : upperPayment 41 = (422045258035:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 41+point split endpoint 4096 42)/2 = (577195277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577195277:ℝ)/168755200)*ClassicalSixthBranch.v ((577195277:ℝ)/168755200)/ClassicalSixthBranch.r = (161889860755385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_41
  · change upperPayment 42 ≤ upperValue ((point split endpoint 4096 42+point split endpoint 4096 43)/2)
    have hp : upperPayment 42 = (421990383091:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 42+point split endpoint 4096 43)/2 = (577220427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577220427:ℝ)/168755200)*ClassicalSixthBranch.v ((577220427:ℝ)/168755200)/ClassicalSixthBranch.r = (161863928449545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_42
  · change upperPayment 43 ≤ upperValue ((point split endpoint 4096 43+point split endpoint 4096 44)/2)
    have hp : upperPayment 43 = (421935488811:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 43+point split endpoint 4096 44)/2 = (577245577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577245577:ℝ)/168755200)*ClassicalSixthBranch.v ((577245577:ℝ)/168755200)/ClassicalSixthBranch.r = (161837998167777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_43
  · change upperPayment 44 ≤ upperValue ((point split endpoint 4096 44+point split endpoint 4096 45)/2)
    have hp : upperPayment 44 = (421880575192:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 44+point split endpoint 4096 45)/2 = (577270727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577270727:ℝ)/168755200)*ClassicalSixthBranch.v ((577270727:ℝ)/168755200)/ClassicalSixthBranch.r = (161812069910081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_44
  · change upperPayment 45 ≤ upperValue ((point split endpoint 4096 45+point split endpoint 4096 46)/2)
    have hp : upperPayment 45 = (421825642232:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 45+point split endpoint 4096 46)/2 = (577295877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577295877:ℝ)/168755200)*ClassicalSixthBranch.v ((577295877:ℝ)/168755200)/ClassicalSixthBranch.r = (161786143676457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_45
  · change upperPayment 46 ≤ upperValue ((point split endpoint 4096 46+point split endpoint 4096 47)/2)
    have hp : upperPayment 46 = (421770689929:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 46+point split endpoint 4096 47)/2 = (577321027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577321027:ℝ)/168755200)*ClassicalSixthBranch.v ((577321027:ℝ)/168755200)/ClassicalSixthBranch.r = (161760219466905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_46
  · change upperPayment 47 ≤ upperValue ((point split endpoint 4096 47+point split endpoint 4096 48)/2)
    have hp : upperPayment 47 = (421715718282:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 47+point split endpoint 4096 48)/2 = (577346177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((577346177:ℝ)/168755200)*ClassicalSixthBranch.v ((577346177:ℝ)/168755200)/ClassicalSixthBranch.r = (161734297281425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_47
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_002
