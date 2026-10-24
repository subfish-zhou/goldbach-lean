import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints042
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_042 (j : Fin 16) : upperPayment (16*42+j.val) ≤
    upperValue ((point split endpoint 4096 (16*42+j.val)+point split endpoint 4096 (16*42+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 672 ≤ upperValue ((point split endpoint 4096 672+point split endpoint 4096 673)/2)
    have hp : upperPayment 672 = (383478198548:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 672+point split endpoint 4096 673)/2 = (593064927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593064927:ℝ)/168755200)*ClassicalSixthBranch.v ((593064927:ℝ)/168755200)/ClassicalSixthBranch.r = (145928890441425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_672
  · change upperPayment 673 ≤ upperValue ((point split endpoint 4096 673+point split endpoint 4096 674)/2)
    have hp : upperPayment 673 = (383410644012:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 673+point split endpoint 4096 674)/2 = (593090077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593090077:ℝ)/168755200)*ClassicalSixthBranch.v ((593090077:ℝ)/168755200)/ClassicalSixthBranch.r = (145904235325017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_673
  · change upperPayment 674 ≤ upperValue ((point split endpoint 4096 674+point split endpoint 4096 675)/2)
    have hp : upperPayment 674 = (383343068538:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 674+point split endpoint 4096 675)/2 = (593115227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593115227:ℝ)/168755200)*ClassicalSixthBranch.v ((593115227:ℝ)/168755200)/ClassicalSixthBranch.r = (145879582232681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_674
  · change upperPayment 675 ≤ upperValue ((point split endpoint 4096 675+point split endpoint 4096 676)/2)
    have hp : upperPayment 675 = (383275472123:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 675+point split endpoint 4096 676)/2 = (593140377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593140377:ℝ)/168755200)*ClassicalSixthBranch.v ((593140377:ℝ)/168755200)/ClassicalSixthBranch.r = (145854931164417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_675
  · change upperPayment 676 ≤ upperValue ((point split endpoint 4096 676+point split endpoint 4096 677)/2)
    have hp : upperPayment 676 = (383207854763:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 676+point split endpoint 4096 677)/2 = (593165527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593165527:ℝ)/168755200)*ClassicalSixthBranch.v ((593165527:ℝ)/168755200)/ClassicalSixthBranch.r = (145830282120225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_676
  · change upperPayment 677 ≤ upperValue ((point split endpoint 4096 677+point split endpoint 4096 678)/2)
    have hp : upperPayment 677 = (383140216456:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 677+point split endpoint 4096 678)/2 = (593190677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593190677:ℝ)/168755200)*ClassicalSixthBranch.v ((593190677:ℝ)/168755200)/ClassicalSixthBranch.r = (145805635100105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_677
  · change upperPayment 678 ≤ upperValue ((point split endpoint 4096 678+point split endpoint 4096 679)/2)
    have hp : upperPayment 678 = (383072557199:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 678+point split endpoint 4096 679)/2 = (593215827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593215827:ℝ)/168755200)*ClassicalSixthBranch.v ((593215827:ℝ)/168755200)/ClassicalSixthBranch.r = (145780990104057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_678
  · change upperPayment 679 ≤ upperValue ((point split endpoint 4096 679+point split endpoint 4096 680)/2)
    have hp : upperPayment 679 = (383004876988:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 679+point split endpoint 4096 680)/2 = (593240977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593240977:ℝ)/168755200)*ClassicalSixthBranch.v ((593240977:ℝ)/168755200)/ClassicalSixthBranch.r = (145756347132081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_679
  · change upperPayment 680 ≤ upperValue ((point split endpoint 4096 680+point split endpoint 4096 681)/2)
    have hp : upperPayment 680 = (382937175822:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 680+point split endpoint 4096 681)/2 = (593266127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593266127:ℝ)/168755200)*ClassicalSixthBranch.v ((593266127:ℝ)/168755200)/ClassicalSixthBranch.r = (145731706184177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_680
  · change upperPayment 681 ≤ upperValue ((point split endpoint 4096 681+point split endpoint 4096 682)/2)
    have hp : upperPayment 681 = (382869453696:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 681+point split endpoint 4096 682)/2 = (593291277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593291277:ℝ)/168755200)*ClassicalSixthBranch.v ((593291277:ℝ)/168755200)/ClassicalSixthBranch.r = (145707067260345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_681
  · change upperPayment 682 ≤ upperValue ((point split endpoint 4096 682+point split endpoint 4096 683)/2)
    have hp : upperPayment 682 = (382801710609:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 682+point split endpoint 4096 683)/2 = (593316427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593316427:ℝ)/168755200)*ClassicalSixthBranch.v ((593316427:ℝ)/168755200)/ClassicalSixthBranch.r = (145682430360585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_682
  · change upperPayment 683 ≤ upperValue ((point split endpoint 4096 683+point split endpoint 4096 684)/2)
    have hp : upperPayment 683 = (382733946556:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 683+point split endpoint 4096 684)/2 = (593341577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593341577:ℝ)/168755200)*ClassicalSixthBranch.v ((593341577:ℝ)/168755200)/ClassicalSixthBranch.r = (145657795484897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_683
  · change upperPayment 684 ≤ upperValue ((point split endpoint 4096 684+point split endpoint 4096 685)/2)
    have hp : upperPayment 684 = (382666161536:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 684+point split endpoint 4096 685)/2 = (593366727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593366727:ℝ)/168755200)*ClassicalSixthBranch.v ((593366727:ℝ)/168755200)/ClassicalSixthBranch.r = (145633162633281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_684
  · change upperPayment 685 ≤ upperValue ((point split endpoint 4096 685+point split endpoint 4096 686)/2)
    have hp : upperPayment 685 = (382598355544:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 685+point split endpoint 4096 686)/2 = (593391877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593391877:ℝ)/168755200)*ClassicalSixthBranch.v ((593391877:ℝ)/168755200)/ClassicalSixthBranch.r = (145608531805737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_685
  · change upperPayment 686 ≤ upperValue ((point split endpoint 4096 686+point split endpoint 4096 687)/2)
    have hp : upperPayment 686 = (382530528579:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 686+point split endpoint 4096 687)/2 = (593417027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593417027:ℝ)/168755200)*ClassicalSixthBranch.v ((593417027:ℝ)/168755200)/ClassicalSixthBranch.r = (145583903002265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_686
  · change upperPayment 687 ≤ upperValue ((point split endpoint 4096 687+point split endpoint 4096 688)/2)
    have hp : upperPayment 687 = (382462680636:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 687+point split endpoint 4096 688)/2 = (593442177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593442177:ℝ)/168755200)*ClassicalSixthBranch.v ((593442177:ℝ)/168755200)/ClassicalSixthBranch.r = (145559276222865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_687
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_042
