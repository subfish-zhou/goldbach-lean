import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints062
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_062 (j : Fin 16) : upperPayment (16*62+j.val) ≤
    upperValue ((point split endpoint 4096 (16*62+j.val)+point split endpoint 4096 (16*62+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 992 ≤ upperValue ((point split endpoint 4096 992+point split endpoint 4096 993)/2)
    have hp : upperPayment 992 = (360775514509:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 992+point split endpoint 4096 993)/2 = (601112927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601112927:ℝ)/168755200)*ClassicalSixthBranch.v ((601112927:ℝ)/168755200)/ClassicalSixthBranch.r = (138142561825745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_992
  · change upperPayment 993 ≤ upperValue ((point split endpoint 4096 993+point split endpoint 4096 994)/2)
    have hp : upperPayment 993 = (360701101759:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 993+point split endpoint 4096 994)/2 = (601138077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601138077:ℝ)/168755200)*ClassicalSixthBranch.v ((601138077:ℝ)/168755200)/ClassicalSixthBranch.r = (138118554412377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_993
  · change upperPayment 994 ≤ upperValue ((point split endpoint 4096 994+point split endpoint 4096 995)/2)
    have hp : upperPayment 994 = (360626667056:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 994+point split endpoint 4096 995)/2 = (601163227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601163227:ℝ)/168755200)*ClassicalSixthBranch.v ((601163227:ℝ)/168755200)/ClassicalSixthBranch.r = (138094549023081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_994
  · change upperPayment 995 ≤ upperValue ((point split endpoint 4096 995+point split endpoint 4096 996)/2)
    have hp : upperPayment 995 = (360552210397:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 995+point split endpoint 4096 996)/2 = (601188377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601188377:ℝ)/168755200)*ClassicalSixthBranch.v ((601188377:ℝ)/168755200)/ClassicalSixthBranch.r = (138070545657857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_995
  · change upperPayment 996 ≤ upperValue ((point split endpoint 4096 996+point split endpoint 4096 997)/2)
    have hp : upperPayment 996 = (360477731779:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 996+point split endpoint 4096 997)/2 = (601213527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601213527:ℝ)/168755200)*ClassicalSixthBranch.v ((601213527:ℝ)/168755200)/ClassicalSixthBranch.r = (138046544316705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_996
  · change upperPayment 997 ≤ upperValue ((point split endpoint 4096 997+point split endpoint 4096 998)/2)
    have hp : upperPayment 997 = (360403231197:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 997+point split endpoint 4096 998)/2 = (601238677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601238677:ℝ)/168755200)*ClassicalSixthBranch.v ((601238677:ℝ)/168755200)/ClassicalSixthBranch.r = (138022544999625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_997
  · change upperPayment 998 ≤ upperValue ((point split endpoint 4096 998+point split endpoint 4096 999)/2)
    have hp : upperPayment 998 = (360328708648:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 998+point split endpoint 4096 999)/2 = (601263827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601263827:ℝ)/168755200)*ClassicalSixthBranch.v ((601263827:ℝ)/168755200)/ClassicalSixthBranch.r = (137998547706617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_998
  · change upperPayment 999 ≤ upperValue ((point split endpoint 4096 999+point split endpoint 4096 1000)/2)
    have hp : upperPayment 999 = (360254164130:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 999+point split endpoint 4096 1000)/2 = (601288977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601288977:ℝ)/168755200)*ClassicalSixthBranch.v ((601288977:ℝ)/168755200)/ClassicalSixthBranch.r = (137974552437681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_999
  · change upperPayment 1000 ≤ upperValue ((point split endpoint 4096 1000+point split endpoint 4096 1001)/2)
    have hp : upperPayment 1000 = (360179597639:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1000+point split endpoint 4096 1001)/2 = (601314127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601314127:ℝ)/168755200)*ClassicalSixthBranch.v ((601314127:ℝ)/168755200)/ClassicalSixthBranch.r = (137950559192817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1000
  · change upperPayment 1001 ≤ upperValue ((point split endpoint 4096 1001+point split endpoint 4096 1002)/2)
    have hp : upperPayment 1001 = (360105009170:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1001+point split endpoint 4096 1002)/2 = (601339277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601339277:ℝ)/168755200)*ClassicalSixthBranch.v ((601339277:ℝ)/168755200)/ClassicalSixthBranch.r = (137926567972025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1001
  · change upperPayment 1002 ≤ upperValue ((point split endpoint 4096 1002+point split endpoint 4096 1003)/2)
    have hp : upperPayment 1002 = (360030398722:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1002+point split endpoint 4096 1003)/2 = (601364427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601364427:ℝ)/168755200)*ClassicalSixthBranch.v ((601364427:ℝ)/168755200)/ClassicalSixthBranch.r = (137902578775305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1002
  · change upperPayment 1003 ≤ upperValue ((point split endpoint 4096 1003+point split endpoint 4096 1004)/2)
    have hp : upperPayment 1003 = (359955766290:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1003+point split endpoint 4096 1004)/2 = (601389577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601389577:ℝ)/168755200)*ClassicalSixthBranch.v ((601389577:ℝ)/168755200)/ClassicalSixthBranch.r = (137878591602657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1003
  · change upperPayment 1004 ≤ upperValue ((point split endpoint 4096 1004+point split endpoint 4096 1005)/2)
    have hp : upperPayment 1004 = (359881111871:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1004+point split endpoint 4096 1005)/2 = (601414727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601414727:ℝ)/168755200)*ClassicalSixthBranch.v ((601414727:ℝ)/168755200)/ClassicalSixthBranch.r = (137854606454081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1004
  · change upperPayment 1005 ≤ upperValue ((point split endpoint 4096 1005+point split endpoint 4096 1006)/2)
    have hp : upperPayment 1005 = (359806435462:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1005+point split endpoint 4096 1006)/2 = (601439877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601439877:ℝ)/168755200)*ClassicalSixthBranch.v ((601439877:ℝ)/168755200)/ClassicalSixthBranch.r = (137830623329577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1005
  · change upperPayment 1006 ≤ upperValue ((point split endpoint 4096 1006+point split endpoint 4096 1007)/2)
    have hp : upperPayment 1006 = (359731737059:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1006+point split endpoint 4096 1007)/2 = (601465027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601465027:ℝ)/168755200)*ClassicalSixthBranch.v ((601465027:ℝ)/168755200)/ClassicalSixthBranch.r = (137806642229145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1006
  · change upperPayment 1007 ≤ upperValue ((point split endpoint 4096 1007+point split endpoint 4096 1008)/2)
    have hp : upperPayment 1007 = (359657016659:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1007+point split endpoint 4096 1008)/2 = (601490177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601490177:ℝ)/168755200)*ClassicalSixthBranch.v ((601490177:ℝ)/168755200)/ClassicalSixthBranch.r = (137782663152785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1007
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_062
