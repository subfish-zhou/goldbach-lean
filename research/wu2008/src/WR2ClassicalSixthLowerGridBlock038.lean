import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints038
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_038 (j : Fin 16) : lowerPayment (16*38+j.val) ≤
    lowerValue ((point 2 split 4096 (16*38+j.val)+point 2 split 4096 (16*38+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 608 ≤ lowerValue ((point 2 split 4096 608+point 2 split 4096 609)/2)
    have hp : lowerPayment 608 = (87044276544:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 608+point 2 split 4096 609)/2 = (372962827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((372962827:ℝ)/168755200)/ClassicalSixthBranch.v ((372962827:ℝ)/168755200) = (30678792243:ℝ)/15654626392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_608
  · change lowerPayment 609 ≤ lowerValue ((point 2 split 4096 609+point 2 split 4096 610)/2)
    have hp : lowerPayment 609 = (87170511933:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 609+point 2 split 4096 610)/2 = (373021089:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((373021089:ℝ)/168755200)/ClassicalSixthBranch.v ((373021089:ℝ)/168755200) = (766892492401:ℝ)/391317651912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_609
  · change lowerPayment 610 ≤ lowerValue ((point 2 split 4096 610+point 2 split 4096 611)/2)
    have hp : lowerPayment 610 = (87296701680:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 610+point 2 split 4096 611)/2 = (373079351:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((373079351:ℝ)/168755200)/ClassicalSixthBranch.v ((373079351:ℝ)/168755200) = (766815178727:ℝ)/391269644024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_610
  · change lowerPayment 611 ≤ lowerValue ((point 2 split 4096 611+point 2 split 4096 612)/2)
    have hp : lowerPayment 611 = (87422845824:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 611+point 2 split 4096 612)/2 = (373137613:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((373137613:ℝ)/168755200)/ClassicalSixthBranch.v ((373137613:ℝ)/168755200) = (766737865053:ℝ)/391221636136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_611
  · change lowerPayment 612 ≤ lowerValue ((point 2 split 4096 612+point 2 split 4096 613)/2)
    have hp : lowerPayment 612 = (87548944406:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 612+point 2 split 4096 613)/2 = (14927835:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((14927835:ℝ)/6750208)/ClassicalSixthBranch.v ((14927835:ℝ)/6750208) = (766660551379:ℝ)/391173628248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_612
  · change lowerPayment 613 ≤ lowerValue ((point 2 split 4096 613+point 2 split 4096 614)/2)
    have hp : lowerPayment 613 = (87674997467:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 613+point 2 split 4096 614)/2 = (373254137:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((373254137:ℝ)/168755200)/ClassicalSixthBranch.v ((373254137:ℝ)/168755200) = (153316647541:ℝ)/78225124072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_613
  · change lowerPayment 614 ≤ lowerValue ((point 2 split 4096 614+point 2 split 4096 615)/2)
    have hp : lowerPayment 614 = (87801005046:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 614+point 2 split 4096 615)/2 = (373312399:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((373312399:ℝ)/168755200)/ClassicalSixthBranch.v ((373312399:ℝ)/168755200) = (766505924031:ℝ)/391077612472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_614
  · change lowerPayment 615 ≤ lowerValue ((point 2 split 4096 615+point 2 split 4096 616)/2)
    have hp : lowerPayment 615 = (87926967185:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 615+point 2 split 4096 616)/2 = (373370661:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((373370661:ℝ)/168755200)/ClassicalSixthBranch.v ((373370661:ℝ)/168755200) = (766428610357:ℝ)/391029604584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_615
  · change lowerPayment 616 ≤ lowerValue ((point 2 split 4096 616+point 2 split 4096 617)/2)
    have hp : lowerPayment 616 = (88052883924:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 616+point 2 split 4096 617)/2 = (373428923:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((373428923:ℝ)/168755200)/ClassicalSixthBranch.v ((373428923:ℝ)/168755200) = (766351296683:ℝ)/390981596696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_616
  · change lowerPayment 617 ≤ lowerValue ((point 2 split 4096 617+point 2 split 4096 618)/2)
    have hp : lowerPayment 617 = (88178755303:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 617+point 2 split 4096 618)/2 = (74697437:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((74697437:ℝ)/33751040)/ClassicalSixthBranch.v ((74697437:ℝ)/33751040) = (766273983009:ℝ)/390933588808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_617
  · change lowerPayment 618 ≤ lowerValue ((point 2 split 4096 618+point 2 split 4096 619)/2)
    have hp : lowerPayment 618 = (88304581362:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 618+point 2 split 4096 619)/2 = (373545447:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((373545447:ℝ)/168755200)/ClassicalSixthBranch.v ((373545447:ℝ)/168755200) = (153239333867:ℝ)/78177116184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_618
  · change lowerPayment 619 ≤ lowerValue ((point 2 split 4096 619+point 2 split 4096 620)/2)
    have hp : lowerPayment 619 = (88430362142:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 619+point 2 split 4096 620)/2 = (373603709:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((373603709:ℝ)/168755200)/ClassicalSixthBranch.v ((373603709:ℝ)/168755200) = (766119355661:ℝ)/390837573032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_619
  · change lowerPayment 620 ≤ lowerValue ((point 2 split 4096 620+point 2 split 4096 621)/2)
    have hp : lowerPayment 620 = (88556097682:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 620+point 2 split 4096 621)/2 = (373661971:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((373661971:ℝ)/168755200)/ClassicalSixthBranch.v ((373661971:ℝ)/168755200) = (766042041987:ℝ)/390789565144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_620
  · change lowerPayment 621 ≤ lowerValue ((point 2 split 4096 621+point 2 split 4096 622)/2)
    have hp : lowerPayment 621 = (88681788024:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 621+point 2 split 4096 622)/2 = (373720233:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((373720233:ℝ)/168755200)/ClassicalSixthBranch.v ((373720233:ℝ)/168755200) = (765964728313:ℝ)/390741557256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_621
  · change lowerPayment 622 ≤ lowerValue ((point 2 split 4096 622+point 2 split 4096 623)/2)
    have hp : lowerPayment 622 = (88807433206:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 622+point 2 split 4096 623)/2 = (74755699:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((74755699:ℝ)/33751040)/ClassicalSixthBranch.v ((74755699:ℝ)/33751040) = (765887414639:ℝ)/390693549368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_622
  · change lowerPayment 623 ≤ lowerValue ((point 2 split 4096 623+point 2 split 4096 624)/2)
    have hp : lowerPayment 623 = (88933033270:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 623+point 2 split 4096 624)/2 = (373836757:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((373836757:ℝ)/168755200)/ClassicalSixthBranch.v ((373836757:ℝ)/168755200) = (153162020193:ℝ)/78129108296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_623
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_038
