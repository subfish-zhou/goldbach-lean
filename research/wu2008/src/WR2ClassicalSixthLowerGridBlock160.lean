import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints160
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_160 (j : Fin 16) : lowerPayment (16*160+j.val) ≤
    lowerValue ((point 2 split 4096 (16*160+j.val)+point 2 split 4096 (16*160+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2560 ≤ lowerValue ((point 2 split 4096 2560+point 2 split 4096 2561)/2)
    have hp : lowerPayment 2560 = (282585092416:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2560+point 2 split 4096 2561)/2 = (486690251:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((486690251:ℝ)/168755200)/ClassicalSixthBranch.v ((486690251:ℝ)/168755200) = (616053514427:ℝ)/297654262424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2560
  · change lowerPayment 2561 ≤ lowerValue ((point 2 split 4096 2561+point 2 split 4096 2562)/2)
    have hp : lowerPayment 2561 = (282672932150:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2561+point 2 split 4096 2562)/2 = (486748513:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((486748513:ℝ)/168755200)/ClassicalSixthBranch.v ((486748513:ℝ)/168755200) = (615976200753:ℝ)/297606254536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2561
  · change lowerPayment 2562 ≤ lowerValue ((point 2 split 4096 2562+point 2 split 4096 2563)/2)
    have hp : lowerPayment 2562 = (282760770314:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2562+point 2 split 4096 2563)/2 = (19472271:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((19472271:ℝ)/6750208)/ClassicalSixthBranch.v ((19472271:ℝ)/6750208) = (615898887079:ℝ)/297558246648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2562
  · change lowerPayment 2563 ≤ lowerValue ((point 2 split 4096 2563+point 2 split 4096 2564)/2)
    have hp : lowerPayment 2563 = (282848606923:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2563+point 2 split 4096 2564)/2 = (486865037:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((486865037:ℝ)/168755200)/ClassicalSixthBranch.v ((486865037:ℝ)/168755200) = (123164314681:ℝ)/59502047752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2563
  · change lowerPayment 2564 ≤ lowerValue ((point 2 split 4096 2564+point 2 split 4096 2565)/2)
    have hp : lowerPayment 2564 = (282936441993:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2564+point 2 split 4096 2565)/2 = (486923299:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((486923299:ℝ)/168755200)/ClassicalSixthBranch.v ((486923299:ℝ)/168755200) = (615744259731:ℝ)/297462230872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2564
  · change lowerPayment 2565 ≤ lowerValue ((point 2 split 4096 2565+point 2 split 4096 2566)/2)
    have hp : lowerPayment 2565 = (283024275537:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2565+point 2 split 4096 2566)/2 = (486981561:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((486981561:ℝ)/168755200)/ClassicalSixthBranch.v ((486981561:ℝ)/168755200) = (615666946057:ℝ)/297414222984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2565
  · change lowerPayment 2566 ≤ lowerValue ((point 2 split 4096 2566+point 2 split 4096 2567)/2)
    have hp : lowerPayment 2566 = (283112107569:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2566+point 2 split 4096 2567)/2 = (487039823:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((487039823:ℝ)/168755200)/ClassicalSixthBranch.v ((487039823:ℝ)/168755200) = (615589632383:ℝ)/297366215096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2566
  · change lowerPayment 2567 ≤ lowerValue ((point 2 split 4096 2567+point 2 split 4096 2568)/2)
    have hp : lowerPayment 2567 = (283199938105:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2567+point 2 split 4096 2568)/2 = (97419617:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((97419617:ℝ)/33751040)/ClassicalSixthBranch.v ((97419617:ℝ)/33751040) = (615512318709:ℝ)/297318207208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2567
  · change lowerPayment 2568 ≤ lowerValue ((point 2 split 4096 2568+point 2 split 4096 2569)/2)
    have hp : lowerPayment 2568 = (283287767157:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2568+point 2 split 4096 2569)/2 = (487156347:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((487156347:ℝ)/168755200)/ClassicalSixthBranch.v ((487156347:ℝ)/168755200) = (123087001007:ℝ)/59454039864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2568
  · change lowerPayment 2569 ≤ lowerValue ((point 2 split 4096 2569+point 2 split 4096 2570)/2)
    have hp : lowerPayment 2569 = (283375594742:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2569+point 2 split 4096 2570)/2 = (487214609:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((487214609:ℝ)/168755200)/ClassicalSixthBranch.v ((487214609:ℝ)/168755200) = (615357691361:ℝ)/297222191432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2569
  · change lowerPayment 2570 ≤ lowerValue ((point 2 split 4096 2570+point 2 split 4096 2571)/2)
    have hp : lowerPayment 2570 = (283463420873:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2570+point 2 split 4096 2571)/2 = (487272871:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((487272871:ℝ)/168755200)/ClassicalSixthBranch.v ((487272871:ℝ)/168755200) = (615280377687:ℝ)/297174183544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2570
  · change lowerPayment 2571 ≤ lowerValue ((point 2 split 4096 2571+point 2 split 4096 2572)/2)
    have hp : lowerPayment 2571 = (283551245564:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2571+point 2 split 4096 2572)/2 = (487331133:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((487331133:ℝ)/168755200)/ClassicalSixthBranch.v ((487331133:ℝ)/168755200) = (615203064013:ℝ)/297126175656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2571
  · change lowerPayment 2572 ≤ lowerValue ((point 2 split 4096 2572+point 2 split 4096 2573)/2)
    have hp : lowerPayment 2572 = (283639068831:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2572+point 2 split 4096 2573)/2 = (97477879:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((97477879:ℝ)/33751040)/ClassicalSixthBranch.v ((97477879:ℝ)/33751040) = (615125750339:ℝ)/297078167768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2572
  · change lowerPayment 2573 ≤ lowerValue ((point 2 split 4096 2573+point 2 split 4096 2574)/2)
    have hp : lowerPayment 2573 = (283726890686:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2573+point 2 split 4096 2574)/2 = (487447657:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((487447657:ℝ)/168755200)/ClassicalSixthBranch.v ((487447657:ℝ)/168755200) = (123009687333:ℝ)/59406031976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2573
  · change lowerPayment 2574 ≤ lowerValue ((point 2 split 4096 2574+point 2 split 4096 2575)/2)
    have hp : lowerPayment 2574 = (283814711146:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2574+point 2 split 4096 2575)/2 = (487505919:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((487505919:ℝ)/168755200)/ClassicalSixthBranch.v ((487505919:ℝ)/168755200) = (614971122991:ℝ)/296982151992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2574
  · change lowerPayment 2575 ≤ lowerValue ((point 2 split 4096 2575+point 2 split 4096 2576)/2)
    have hp : lowerPayment 2575 = (283902530223:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2575+point 2 split 4096 2576)/2 = (487564181:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((487564181:ℝ)/168755200)/ClassicalSixthBranch.v ((487564181:ℝ)/168755200) = (614893809317:ℝ)/296934144104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2575
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_160
