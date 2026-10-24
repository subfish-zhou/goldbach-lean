import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints167
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_167 (j : Fin 16) : lowerPayment (16*167+j.val) ≤
    lowerValue ((point 2 split 4096 (16*167+j.val)+point 2 split 4096 (16*167+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2672 ≤ lowerValue ((point 2 split 4096 2672+point 2 split 4096 2673)/2)
    have hp : lowerPayment 2672 = (292416660439:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2672+point 2 split 4096 2673)/2 = (98643119:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((98643119:ℝ)/33751040)/ClassicalSixthBranch.v ((98643119:ℝ)/33751040) = (607394382939:ℝ)/292277378968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2672
  · change lowerPayment 2673 ≤ lowerValue ((point 2 split 4096 2673+point 2 split 4096 2674)/2)
    have hp : lowerPayment 2673 = (292504413546:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2673+point 2 split 4096 2674)/2 = (493273857:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((493273857:ℝ)/168755200)/ClassicalSixthBranch.v ((493273857:ℝ)/168755200) = (121463413853:ℝ)/58445874216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2673
  · change lowerPayment 2674 ≤ lowerValue ((point 2 split 4096 2674+point 2 split 4096 2675)/2)
    have hp : lowerPayment 2674 = (292592166686:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2674+point 2 split 4096 2675)/2 = (493332119:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((493332119:ℝ)/168755200)/ClassicalSixthBranch.v ((493332119:ℝ)/168755200) = (607239755591:ℝ)/292181363192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2674
  · change lowerPayment 2675 ≤ lowerValue ((point 2 split 4096 2675+point 2 split 4096 2676)/2)
    have hp : lowerPayment 2675 = (292679919873:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2675+point 2 split 4096 2676)/2 = (493390381:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((493390381:ℝ)/168755200)/ClassicalSixthBranch.v ((493390381:ℝ)/168755200) = (607162441917:ℝ)/292133355304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2675
  · change lowerPayment 2676 ≤ lowerValue ((point 2 split 4096 2676+point 2 split 4096 2677)/2)
    have hp : lowerPayment 2676 = (292767673122:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2676+point 2 split 4096 2677)/2 = (493448643:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((493448643:ℝ)/168755200)/ClassicalSixthBranch.v ((493448643:ℝ)/168755200) = (607085128243:ℝ)/292085347416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2676
  · change lowerPayment 2677 ≤ lowerValue ((point 2 split 4096 2677+point 2 split 4096 2678)/2)
    have hp : lowerPayment 2677 = (292855426446:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2677+point 2 split 4096 2678)/2 = (98701381:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((98701381:ℝ)/33751040)/ClassicalSixthBranch.v ((98701381:ℝ)/33751040) = (607007814569:ℝ)/292037339528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2677
  · change lowerPayment 2678 ≤ lowerValue ((point 2 split 4096 2678+point 2 split 4096 2679)/2)
    have hp : lowerPayment 2678 = (292943179860:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2678+point 2 split 4096 2679)/2 = (493565167:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((493565167:ℝ)/168755200)/ClassicalSixthBranch.v ((493565167:ℝ)/168755200) = (121386100179:ℝ)/58397866328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2678
  · change lowerPayment 2679 ≤ lowerValue ((point 2 split 4096 2679+point 2 split 4096 2680)/2)
    have hp : lowerPayment 2679 = (293030933378:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2679+point 2 split 4096 2680)/2 = (493623429:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((493623429:ℝ)/168755200)/ClassicalSixthBranch.v ((493623429:ℝ)/168755200) = (606853187221:ℝ)/291941323752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2679
  · change lowerPayment 2680 ≤ lowerValue ((point 2 split 4096 2680+point 2 split 4096 2681)/2)
    have hp : lowerPayment 2680 = (293118687015:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2680+point 2 split 4096 2681)/2 = (493681691:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((493681691:ℝ)/168755200)/ClassicalSixthBranch.v ((493681691:ℝ)/168755200) = (606775873547:ℝ)/291893315864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2680
  · change lowerPayment 2681 ≤ lowerValue ((point 2 split 4096 2681+point 2 split 4096 2682)/2)
    have hp : lowerPayment 2681 = (293206440784:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2681+point 2 split 4096 2682)/2 = (493739953:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((493739953:ℝ)/168755200)/ClassicalSixthBranch.v ((493739953:ℝ)/168755200) = (606698559873:ℝ)/291845307976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2681
  · change lowerPayment 2682 ≤ lowerValue ((point 2 split 4096 2682+point 2 split 4096 2683)/2)
    have hp : lowerPayment 2682 = (293294194699:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2682+point 2 split 4096 2683)/2 = (98759643:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((98759643:ℝ)/33751040)/ClassicalSixthBranch.v ((98759643:ℝ)/33751040) = (606621246199:ℝ)/291797300088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2682
  · change lowerPayment 2683 ≤ lowerValue ((point 2 split 4096 2683+point 2 split 4096 2684)/2)
    have hp : lowerPayment 2683 = (293381948776:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2683+point 2 split 4096 2684)/2 = (493856477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((493856477:ℝ)/168755200)/ClassicalSixthBranch.v ((493856477:ℝ)/168755200) = (24261757301:ℝ)/11669971688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2683
  · change lowerPayment 2684 ≤ lowerValue ((point 2 split 4096 2684+point 2 split 4096 2685)/2)
    have hp : lowerPayment 2684 = (293469703028:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2684+point 2 split 4096 2685)/2 = (493914739:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((493914739:ℝ)/168755200)/ClassicalSixthBranch.v ((493914739:ℝ)/168755200) = (606466618851:ℝ)/291701284312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2684
  · change lowerPayment 2685 ≤ lowerValue ((point 2 split 4096 2685+point 2 split 4096 2686)/2)
    have hp : lowerPayment 2685 = (293557457469:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2685+point 2 split 4096 2686)/2 = (493973001:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((493973001:ℝ)/168755200)/ClassicalSixthBranch.v ((493973001:ℝ)/168755200) = (606389305177:ℝ)/291653276424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2685
  · change lowerPayment 2686 ≤ lowerValue ((point 2 split 4096 2686+point 2 split 4096 2687)/2)
    have hp : lowerPayment 2686 = (293645212113:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2686+point 2 split 4096 2687)/2 = (494031263:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((494031263:ℝ)/168755200)/ClassicalSixthBranch.v ((494031263:ℝ)/168755200) = (606311991503:ℝ)/291605268536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2686
  · change lowerPayment 2687 ≤ lowerValue ((point 2 split 4096 2687+point 2 split 4096 2688)/2)
    have hp : lowerPayment 2687 = (293732966975:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2687+point 2 split 4096 2688)/2 = (19763581:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((19763581:ℝ)/6750208)/ClassicalSixthBranch.v ((19763581:ℝ)/6750208) = (606234677829:ℝ)/291557260648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2687
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_167
