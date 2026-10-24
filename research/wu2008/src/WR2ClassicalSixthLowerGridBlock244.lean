import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints244
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_244 (j : Fin 16) : lowerPayment (16*244+j.val) ≤
    lowerValue ((point 2 split 4096 (16*244+j.val)+point 2 split 4096 (16*244+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3904 ≤ lowerValue ((point 2 split 4096 3904+point 2 split 4096 3905)/2)
    have hp : lowerPayment 3904 = (405014339415:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3904+point 2 split 4096 3905)/2 = (564994379:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((564994379:ℝ)/168755200)/ClassicalSixthBranch.v ((564994379:ℝ)/168755200) = (512143936571:ℝ)/233131660952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3904
  · change lowerPayment 3905 ≤ lowerValue ((point 2 split 4096 3905+point 2 split 4096 3906)/2)
    have hp : lowerPayment 3905 = (405113179439:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3905+point 2 split 4096 3906)/2 = (565052641:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((565052641:ℝ)/168755200)/ClassicalSixthBranch.v ((565052641:ℝ)/168755200) = (512066622897:ℝ)/233083653064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3905
  · change lowerPayment 3906 ≤ lowerValue ((point 2 split 4096 3906+point 2 split 4096 3907)/2)
    have hp : lowerPayment 3906 = (405212038216:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3906+point 2 split 4096 3907)/2 = (565110903:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((565110903:ℝ)/168755200)/ClassicalSixthBranch.v ((565110903:ℝ)/168755200) = (511989309223:ℝ)/233035645176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3906
  · change lowerPayment 3907 ≤ lowerValue ((point 2 split 4096 3907+point 2 split 4096 3908)/2)
    have hp : lowerPayment 3907 = (405310915762:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3907+point 2 split 4096 3908)/2 = (113033833:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((113033833:ℝ)/33751040)/ClassicalSixthBranch.v ((113033833:ℝ)/33751040) = (511911995549:ℝ)/232987637288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3907
  · change lowerPayment 3908 ≤ lowerValue ((point 2 split 4096 3908+point 2 split 4096 3909)/2)
    have hp : lowerPayment 3908 = (405409812097:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3908+point 2 split 4096 3909)/2 = (565227427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((565227427:ℝ)/168755200)/ClassicalSixthBranch.v ((565227427:ℝ)/168755200) = (20473387275:ℝ)/9317585176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3908
  · change lowerPayment 3909 ≤ lowerValue ((point 2 split 4096 3909+point 2 split 4096 3910)/2)
    have hp : lowerPayment 3909 = (405508727238:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3909+point 2 split 4096 3910)/2 = (565285689:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((565285689:ℝ)/168755200)/ClassicalSixthBranch.v ((565285689:ℝ)/168755200) = (511757368201:ℝ)/232891621512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3909
  · change lowerPayment 3910 ≤ lowerValue ((point 2 split 4096 3910+point 2 split 4096 3911)/2)
    have hp : lowerPayment 3910 = (405607661203:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3910+point 2 split 4096 3911)/2 = (565343951:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((565343951:ℝ)/168755200)/ClassicalSixthBranch.v ((565343951:ℝ)/168755200) = (511680054527:ℝ)/232843613624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3910
  · change lowerPayment 3911 ≤ lowerValue ((point 2 split 4096 3911+point 2 split 4096 3912)/2)
    have hp : lowerPayment 3911 = (405706614011:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3911+point 2 split 4096 3912)/2 = (565402213:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((565402213:ℝ)/168755200)/ClassicalSixthBranch.v ((565402213:ℝ)/168755200) = (511602740853:ℝ)/232795605736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3911
  · change lowerPayment 3912 ≤ lowerValue ((point 2 split 4096 3912+point 2 split 4096 3913)/2)
    have hp : lowerPayment 3912 = (405805585679:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3912+point 2 split 4096 3913)/2 = (22618419:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((22618419:ℝ)/6750208)/ClassicalSixthBranch.v ((22618419:ℝ)/6750208) = (511525427179:ℝ)/232747597848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3912
  · change lowerPayment 3913 ≤ lowerValue ((point 2 split 4096 3913+point 2 split 4096 3914)/2)
    have hp : lowerPayment 3913 = (405904576226:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3913+point 2 split 4096 3914)/2 = (565518737:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((565518737:ℝ)/168755200)/ClassicalSixthBranch.v ((565518737:ℝ)/168755200) = (102289622701:ℝ)/46539917992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3913
  · change lowerPayment 3914 ≤ lowerValue ((point 2 split 4096 3914+point 2 split 4096 3915)/2)
    have hp : lowerPayment 3914 = (406003585669:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3914+point 2 split 4096 3915)/2 = (565576999:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((565576999:ℝ)/168755200)/ClassicalSixthBranch.v ((565576999:ℝ)/168755200) = (511370799831:ℝ)/232651582072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3914
  · change lowerPayment 3915 ≤ lowerValue ((point 2 split 4096 3915+point 2 split 4096 3916)/2)
    have hp : lowerPayment 3915 = (406102614028:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3915+point 2 split 4096 3916)/2 = (565635261:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((565635261:ℝ)/168755200)/ClassicalSixthBranch.v ((565635261:ℝ)/168755200) = (511293486157:ℝ)/232603574184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3915
  · change lowerPayment 3916 ≤ lowerValue ((point 2 split 4096 3916+point 2 split 4096 3917)/2)
    have hp : lowerPayment 3916 = (406201661320:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3916+point 2 split 4096 3917)/2 = (565693523:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((565693523:ℝ)/168755200)/ClassicalSixthBranch.v ((565693523:ℝ)/168755200) = (511216172483:ℝ)/232555566296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3916
  · change lowerPayment 3917 ≤ lowerValue ((point 2 split 4096 3917+point 2 split 4096 3918)/2)
    have hp : lowerPayment 3917 = (406300727563:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3917+point 2 split 4096 3918)/2 = (113150357:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((113150357:ℝ)/33751040)/ClassicalSixthBranch.v ((113150357:ℝ)/33751040) = (511138858809:ℝ)/232507558408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3917
  · change lowerPayment 3918 ≤ lowerValue ((point 2 split 4096 3918+point 2 split 4096 3919)/2)
    have hp : lowerPayment 3918 = (406399812775:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3918+point 2 split 4096 3919)/2 = (565810047:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((565810047:ℝ)/168755200)/ClassicalSixthBranch.v ((565810047:ℝ)/168755200) = (102212309027:ℝ)/46491910104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3918
  · change lowerPayment 3919 ≤ lowerValue ((point 2 split 4096 3919+point 2 split 4096 3920)/2)
    have hp : lowerPayment 3919 = (406498916975:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3919+point 2 split 4096 3920)/2 = (565868309:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((565868309:ℝ)/168755200)/ClassicalSixthBranch.v ((565868309:ℝ)/168755200) = (510984231461:ℝ)/232411542632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3919
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_244
