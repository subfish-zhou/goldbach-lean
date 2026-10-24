import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints167
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_167 (j : Fin 16) : upperPayment (16*167+j.val) ≤
    upperValue ((point split endpoint 4096 (16*167+j.val)+point split endpoint 4096 (16*167+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2672 ≤ upperValue ((point split endpoint 4096 2672+point split endpoint 4096 2673)/2)
    have hp : upperPayment 2672 = (201566025193:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2672+point split endpoint 4096 2673)/2 = (643364927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643364927:ℝ)/168755200)*ClassicalSixthBranch.v ((643364927:ℝ)/168755200)/ClassicalSixthBranch.r = (100664777553425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2672
  · change upperPayment 2673 ≤ upperValue ((point split endpoint 4096 2673+point split endpoint 4096 2674)/2)
    have hp : upperPayment 2673 = (201448578722:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2673+point split endpoint 4096 2674)/2 = (643390077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643390077:ℝ)/168755200)*ClassicalSixthBranch.v ((643390077:ℝ)/168755200)/ClassicalSixthBranch.r = (100644170581017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2673
  · change upperPayment 2674 ≤ upperValue ((point split endpoint 4096 2674+point split endpoint 4096 2675)/2)
    have hp : upperPayment 2674 = (201331102030:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2674+point split endpoint 4096 2675)/2 = (643415227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643415227:ℝ)/168755200)*ClassicalSixthBranch.v ((643415227:ℝ)/168755200)/ClassicalSixthBranch.r = (100623565632681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2674
  · change upperPayment 2675 ≤ upperValue ((point split endpoint 4096 2675+point split endpoint 4096 2676)/2)
    have hp : upperPayment 2675 = (201213595112:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2675+point split endpoint 4096 2676)/2 = (643440377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643440377:ℝ)/168755200)*ClassicalSixthBranch.v ((643440377:ℝ)/168755200)/ClassicalSixthBranch.r = (100602962708417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2675
  · change upperPayment 2676 ≤ upperValue ((point split endpoint 4096 2676+point split endpoint 4096 2677)/2)
    have hp : upperPayment 2676 = (201096057959:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2676+point split endpoint 4096 2677)/2 = (643465527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643465527:ℝ)/168755200)*ClassicalSixthBranch.v ((643465527:ℝ)/168755200)/ClassicalSixthBranch.r = (100582361808225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2676
  · change upperPayment 2677 ≤ upperValue ((point split endpoint 4096 2677+point split endpoint 4096 2678)/2)
    have hp : upperPayment 2677 = (200978490566:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2677+point split endpoint 4096 2678)/2 = (643490677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643490677:ℝ)/168755200)*ClassicalSixthBranch.v ((643490677:ℝ)/168755200)/ClassicalSixthBranch.r = (100561762932105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2677
  · change upperPayment 2678 ≤ upperValue ((point split endpoint 4096 2678+point split endpoint 4096 2679)/2)
    have hp : upperPayment 2678 = (200860892925:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2678+point split endpoint 4096 2679)/2 = (643515827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643515827:ℝ)/168755200)*ClassicalSixthBranch.v ((643515827:ℝ)/168755200)/ClassicalSixthBranch.r = (100541166080057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2678
  · change upperPayment 2679 ≤ upperValue ((point split endpoint 4096 2679+point split endpoint 4096 2680)/2)
    have hp : upperPayment 2679 = (200743265029:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2679+point split endpoint 4096 2680)/2 = (643540977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643540977:ℝ)/168755200)*ClassicalSixthBranch.v ((643540977:ℝ)/168755200)/ClassicalSixthBranch.r = (100520571252081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2679
  · change upperPayment 2680 ≤ upperValue ((point split endpoint 4096 2680+point split endpoint 4096 2681)/2)
    have hp : upperPayment 2680 = (200625606873:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2680+point split endpoint 4096 2681)/2 = (643566127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643566127:ℝ)/168755200)*ClassicalSixthBranch.v ((643566127:ℝ)/168755200)/ClassicalSixthBranch.r = (100499978448177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2680
  · change upperPayment 2681 ≤ upperValue ((point split endpoint 4096 2681+point split endpoint 4096 2682)/2)
    have hp : upperPayment 2681 = (200507918448:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2681+point split endpoint 4096 2682)/2 = (6248459:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((6248459:ℝ)/1638400)*ClassicalSixthBranch.v ((6248459:ℝ)/1638400)/ClassicalSixthBranch.r = (975528035615:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2681
  · change upperPayment 2682 ≤ upperValue ((point split endpoint 4096 2682+point split endpoint 4096 2683)/2)
    have hp : upperPayment 2682 = (200390199749:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2682+point split endpoint 4096 2683)/2 = (643616427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643616427:ℝ)/168755200)*ClassicalSixthBranch.v ((643616427:ℝ)/168755200)/ClassicalSixthBranch.r = (100458798912585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2682
  · change upperPayment 2683 ≤ upperValue ((point split endpoint 4096 2683+point split endpoint 4096 2684)/2)
    have hp : upperPayment 2683 = (200272450768:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2683+point split endpoint 4096 2684)/2 = (643641577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643641577:ℝ)/168755200)*ClassicalSixthBranch.v ((643641577:ℝ)/168755200)/ClassicalSixthBranch.r = (100438212180897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2683
  · change upperPayment 2684 ≤ upperValue ((point split endpoint 4096 2684+point split endpoint 4096 2685)/2)
    have hp : upperPayment 2684 = (200154671498:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2684+point split endpoint 4096 2685)/2 = (643666727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643666727:ℝ)/168755200)*ClassicalSixthBranch.v ((643666727:ℝ)/168755200)/ClassicalSixthBranch.r = (100417627473281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2684
  · change upperPayment 2685 ≤ upperValue ((point split endpoint 4096 2685+point split endpoint 4096 2686)/2)
    have hp : upperPayment 2685 = (200036861934:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2685+point split endpoint 4096 2686)/2 = (643691877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643691877:ℝ)/168755200)*ClassicalSixthBranch.v ((643691877:ℝ)/168755200)/ClassicalSixthBranch.r = (100397044789737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2685
  · change upperPayment 2686 ≤ upperValue ((point split endpoint 4096 2686+point split endpoint 4096 2687)/2)
    have hp : upperPayment 2686 = (199919022067:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2686+point split endpoint 4096 2687)/2 = (643717027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643717027:ℝ)/168755200)*ClassicalSixthBranch.v ((643717027:ℝ)/168755200)/ClassicalSixthBranch.r = (100376464130265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2686
  · change upperPayment 2687 ≤ upperValue ((point split endpoint 4096 2687+point split endpoint 4096 2688)/2)
    have hp : upperPayment 2687 = (199801151892:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2687+point split endpoint 4096 2688)/2 = (643742177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643742177:ℝ)/168755200)*ClassicalSixthBranch.v ((643742177:ℝ)/168755200)/ClassicalSixthBranch.r = (100355885494865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2687
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_167
