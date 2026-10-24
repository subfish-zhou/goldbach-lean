import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints242
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_242 (j : Fin 16) : upperPayment (16*242+j.val) ≤
    upperValue ((point split endpoint 4096 (16*242+j.val)+point split endpoint 4096 (16*242+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3872 ≤ upperValue ((point split endpoint 4096 3872+point split endpoint 4096 3873)/2)
    have hp : upperPayment 3872 = (36679481151:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3872+point split endpoint 4096 3873)/2 = (673544927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673544927:ℝ)/168755200)*ClassicalSixthBranch.v ((673544927:ℝ)/168755200)/ClassicalSixthBranch.r = (77392528060625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3872
  · change upperPayment 3873 ≤ upperValue ((point split endpoint 4096 3873+point split endpoint 4096 3874)/2)
    have hp : upperPayment 3873 = (36519991180:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3873+point split endpoint 4096 3874)/2 = (673570077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673570077:ℝ)/168755200)*ClassicalSixthBranch.v ((673570077:ℝ)/168755200)/ClassicalSixthBranch.r = (77374349974617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3873
  · change upperPayment 3874 ≤ upperValue ((point split endpoint 4096 3874+point split endpoint 4096 3875)/2)
    have hp : upperPayment 3874 = (36360460487:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3874+point split endpoint 4096 3875)/2 = (673595227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673595227:ℝ)/168755200)*ClassicalSixthBranch.v ((673595227:ℝ)/168755200)/ClassicalSixthBranch.r = (77356173912681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3874
  · change upperPayment 3875 ≤ upperValue ((point split endpoint 4096 3875+point split endpoint 4096 3876)/2)
    have hp : upperPayment 3875 = (36200889059:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3875+point split endpoint 4096 3876)/2 = (673620377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673620377:ℝ)/168755200)*ClassicalSixthBranch.v ((673620377:ℝ)/168755200)/ClassicalSixthBranch.r = (77337999874817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3875
  · change upperPayment 3876 ≤ upperValue ((point split endpoint 4096 3876+point split endpoint 4096 3877)/2)
    have hp : upperPayment 3876 = (36041276886:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3876+point split endpoint 4096 3877)/2 = (673645527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673645527:ℝ)/168755200)*ClassicalSixthBranch.v ((673645527:ℝ)/168755200)/ClassicalSixthBranch.r = (77319827861025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3876
  · change upperPayment 3877 ≤ upperValue ((point split endpoint 4096 3877+point split endpoint 4096 3878)/2)
    have hp : upperPayment 3877 = (35881623956:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3877+point split endpoint 4096 3878)/2 = (673670677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673670677:ℝ)/168755200)*ClassicalSixthBranch.v ((673670677:ℝ)/168755200)/ClassicalSixthBranch.r = (77301657871305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3877
  · change upperPayment 3878 ≤ upperValue ((point split endpoint 4096 3878+point split endpoint 4096 3879)/2)
    have hp : upperPayment 3878 = (35721930259:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3878+point split endpoint 4096 3879)/2 = (673695827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673695827:ℝ)/168755200)*ClassicalSixthBranch.v ((673695827:ℝ)/168755200)/ClassicalSixthBranch.r = (77283489905657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3878
  · change upperPayment 3879 ≤ upperValue ((point split endpoint 4096 3879+point split endpoint 4096 3880)/2)
    have hp : upperPayment 3879 = (35562195783:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3879+point split endpoint 4096 3880)/2 = (673720977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673720977:ℝ)/168755200)*ClassicalSixthBranch.v ((673720977:ℝ)/168755200)/ClassicalSixthBranch.r = (77265323964081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3879
  · change upperPayment 3880 ≤ upperValue ((point split endpoint 4096 3880+point split endpoint 4096 3881)/2)
    have hp : upperPayment 3880 = (35402420517:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3880+point split endpoint 4096 3881)/2 = (673746127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673746127:ℝ)/168755200)*ClassicalSixthBranch.v ((673746127:ℝ)/168755200)/ClassicalSixthBranch.r = (77247160046577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3880
  · change upperPayment 3881 ≤ upperValue ((point split endpoint 4096 3881+point split endpoint 4096 3882)/2)
    have hp : upperPayment 3881 = (35242604449:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3881+point split endpoint 4096 3882)/2 = (673771277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673771277:ℝ)/168755200)*ClassicalSixthBranch.v ((673771277:ℝ)/168755200)/ClassicalSixthBranch.r = (77228998153145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3881
  · change upperPayment 3882 ≤ upperValue ((point split endpoint 4096 3882+point split endpoint 4096 3883)/2)
    have hp : upperPayment 3882 = (35082747570:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3882+point split endpoint 4096 3883)/2 = (673796427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673796427:ℝ)/168755200)*ClassicalSixthBranch.v ((673796427:ℝ)/168755200)/ClassicalSixthBranch.r = (77210838283785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3882
  · change upperPayment 3883 ≤ upperValue ((point split endpoint 4096 3883+point split endpoint 4096 3884)/2)
    have hp : upperPayment 3883 = (34922849868:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3883+point split endpoint 4096 3884)/2 = (673821577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673821577:ℝ)/168755200)*ClassicalSixthBranch.v ((673821577:ℝ)/168755200)/ClassicalSixthBranch.r = (77192680438497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3883
  · change upperPayment 3884 ≤ upperValue ((point split endpoint 4096 3884+point split endpoint 4096 3885)/2)
    have hp : upperPayment 3884 = (34762911330:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3884+point split endpoint 4096 3885)/2 = (673846727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673846727:ℝ)/168755200)*ClassicalSixthBranch.v ((673846727:ℝ)/168755200)/ClassicalSixthBranch.r = (77174524617281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3884
  · change upperPayment 3885 ≤ upperValue ((point split endpoint 4096 3885+point split endpoint 4096 3886)/2)
    have hp : upperPayment 3885 = (34602931947:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3885+point split endpoint 4096 3886)/2 = (673871877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673871877:ℝ)/168755200)*ClassicalSixthBranch.v ((673871877:ℝ)/168755200)/ClassicalSixthBranch.r = (77156370820137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3885
  · change upperPayment 3886 ≤ upperValue ((point split endpoint 4096 3886+point split endpoint 4096 3887)/2)
    have hp : upperPayment 3886 = (34442911707:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3886+point split endpoint 4096 3887)/2 = (673897027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673897027:ℝ)/168755200)*ClassicalSixthBranch.v ((673897027:ℝ)/168755200)/ClassicalSixthBranch.r = (77138219047065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3886
  · change upperPayment 3887 ≤ upperValue ((point split endpoint 4096 3887+point split endpoint 4096 3888)/2)
    have hp : upperPayment 3887 = (34282850599:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3887+point split endpoint 4096 3888)/2 = (673922177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673922177:ℝ)/168755200)*ClassicalSixthBranch.v ((673922177:ℝ)/168755200)/ClassicalSixthBranch.r = (77120069298065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3887
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_242
