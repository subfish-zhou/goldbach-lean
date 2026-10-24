import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints057
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_057 (j : Fin 16) : upperPayment (16*57+j.val) ≤
    upperValue ((point split endpoint 4096 (16*57+j.val)+point split endpoint 4096 (16*57+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 912 ≤ upperValue ((point split endpoint 4096 912+point split endpoint 4096 913)/2)
    have hp : upperPayment 912 = (366657705797:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 912+point split endpoint 4096 913)/2 = (599100927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599100927:ℝ)/168755200)*ClassicalSixthBranch.v ((599100927:ℝ)/168755200)/ClassicalSixthBranch.r = (140069712888465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_912
  · change upperPayment 913 ≤ upperValue ((point split endpoint 4096 913+point split endpoint 4096 914)/2)
    have hp : upperPayment 913 = (366585038385:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 913+point split endpoint 4096 914)/2 = (599126077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599126077:ℝ)/168755200)*ClassicalSixthBranch.v ((599126077:ℝ)/168755200)/ClassicalSixthBranch.r = (140045543549337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_913
  · change upperPayment 914 ≤ upperValue ((point split endpoint 4096 914+point split endpoint 4096 915)/2)
    have hp : upperPayment 914 = (366512349287:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 914+point split endpoint 4096 915)/2 = (599151227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599151227:ℝ)/168755200)*ClassicalSixthBranch.v ((599151227:ℝ)/168755200)/ClassicalSixthBranch.r = (140021376234281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_914
  · change upperPayment 915 ≤ upperValue ((point split endpoint 4096 915+point split endpoint 4096 916)/2)
    have hp : upperPayment 915 = (366439638500:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 915+point split endpoint 4096 916)/2 = (599176377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599176377:ℝ)/168755200)*ClassicalSixthBranch.v ((599176377:ℝ)/168755200)/ClassicalSixthBranch.r = (139997210943297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_915
  · change upperPayment 916 ≤ upperValue ((point split endpoint 4096 916+point split endpoint 4096 917)/2)
    have hp : upperPayment 916 = (366366906022:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 916+point split endpoint 4096 917)/2 = (599201527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599201527:ℝ)/168755200)*ClassicalSixthBranch.v ((599201527:ℝ)/168755200)/ClassicalSixthBranch.r = (139973047676385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_916
  · change upperPayment 917 ≤ upperValue ((point split endpoint 4096 917+point split endpoint 4096 918)/2)
    have hp : upperPayment 917 = (366294151847:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 917+point split endpoint 4096 918)/2 = (599226677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599226677:ℝ)/168755200)*ClassicalSixthBranch.v ((599226677:ℝ)/168755200)/ClassicalSixthBranch.r = (139948886433545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_917
  · change upperPayment 918 ≤ upperValue ((point split endpoint 4096 918+point split endpoint 4096 919)/2)
    have hp : upperPayment 918 = (366221375975:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 918+point split endpoint 4096 919)/2 = (599251827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599251827:ℝ)/168755200)*ClassicalSixthBranch.v ((599251827:ℝ)/168755200)/ClassicalSixthBranch.r = (139924727214777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_918
  · change upperPayment 919 ≤ upperValue ((point split endpoint 4096 919+point split endpoint 4096 920)/2)
    have hp : upperPayment 919 = (366148578400:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 919+point split endpoint 4096 920)/2 = (599276977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599276977:ℝ)/168755200)*ClassicalSixthBranch.v ((599276977:ℝ)/168755200)/ClassicalSixthBranch.r = (139900570020081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_919
  · change upperPayment 920 ≤ upperValue ((point split endpoint 4096 920+point split endpoint 4096 921)/2)
    have hp : upperPayment 920 = (366075759120:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 920+point split endpoint 4096 921)/2 = (599302127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599302127:ℝ)/168755200)*ClassicalSixthBranch.v ((599302127:ℝ)/168755200)/ClassicalSixthBranch.r = (139876414849457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_920
  · change upperPayment 921 ≤ upperValue ((point split endpoint 4096 921+point split endpoint 4096 922)/2)
    have hp : upperPayment 921 = (366002918132:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 921+point split endpoint 4096 922)/2 = (599327277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599327277:ℝ)/168755200)*ClassicalSixthBranch.v ((599327277:ℝ)/168755200)/ClassicalSixthBranch.r = (139852261702905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_921
  · change upperPayment 922 ≤ upperValue ((point split endpoint 4096 922+point split endpoint 4096 923)/2)
    have hp : upperPayment 922 = (365930055431:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 922+point split endpoint 4096 923)/2 = (599352427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599352427:ℝ)/168755200)*ClassicalSixthBranch.v ((599352427:ℝ)/168755200)/ClassicalSixthBranch.r = (139828110580425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_922
  · change upperPayment 923 ≤ upperValue ((point split endpoint 4096 923+point split endpoint 4096 924)/2)
    have hp : upperPayment 923 = (365857171016:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 923+point split endpoint 4096 924)/2 = (599377577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599377577:ℝ)/168755200)*ClassicalSixthBranch.v ((599377577:ℝ)/168755200)/ClassicalSixthBranch.r = (139803961482017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_923
  · change upperPayment 924 ≤ upperValue ((point split endpoint 4096 924+point split endpoint 4096 925)/2)
    have hp : upperPayment 924 = (365784264882:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 924+point split endpoint 4096 925)/2 = (599402727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599402727:ℝ)/168755200)*ClassicalSixthBranch.v ((599402727:ℝ)/168755200)/ClassicalSixthBranch.r = (139779814407681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_924
  · change upperPayment 925 ≤ upperValue ((point split endpoint 4096 925+point split endpoint 4096 926)/2)
    have hp : upperPayment 925 = (365711337027:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 925+point split endpoint 4096 926)/2 = (599427877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599427877:ℝ)/168755200)*ClassicalSixthBranch.v ((599427877:ℝ)/168755200)/ClassicalSixthBranch.r = (139755669357417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_925
  · change upperPayment 926 ≤ upperValue ((point split endpoint 4096 926+point split endpoint 4096 927)/2)
    have hp : upperPayment 926 = (365638387446:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 926+point split endpoint 4096 927)/2 = (599453027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599453027:ℝ)/168755200)*ClassicalSixthBranch.v ((599453027:ℝ)/168755200)/ClassicalSixthBranch.r = (139731526331225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_926
  · change upperPayment 927 ≤ upperValue ((point split endpoint 4096 927+point split endpoint 4096 928)/2)
    have hp : upperPayment 927 = (365565416138:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 927+point split endpoint 4096 928)/2 = (599478177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599478177:ℝ)/168755200)*ClassicalSixthBranch.v ((599478177:ℝ)/168755200)/ClassicalSixthBranch.r = (139707385329105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_927
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_057
