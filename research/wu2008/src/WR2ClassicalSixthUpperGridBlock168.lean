import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints168
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_168 (j : Fin 16) : upperPayment (16*168+j.val) ≤
    upperValue ((point split endpoint 4096 (16*168+j.val)+point split endpoint 4096 (16*168+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2688 ≤ upperValue ((point split endpoint 4096 2688+point split endpoint 4096 2689)/2)
    have hp : upperPayment 2688 = (199683251401:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2688+point split endpoint 4096 2689)/2 = (643767327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643767327:ℝ)/168755200)*ClassicalSixthBranch.v ((643767327:ℝ)/168755200)/ClassicalSixthBranch.r = (100335308883537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2688
  · change upperPayment 2689 ≤ upperValue ((point split endpoint 4096 2689+point split endpoint 4096 2690)/2)
    have hp : upperPayment 2689 = (199565320588:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2689+point split endpoint 4096 2690)/2 = (643792477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643792477:ℝ)/168755200)*ClassicalSixthBranch.v ((643792477:ℝ)/168755200)/ClassicalSixthBranch.r = (100314734296281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2689
  · change upperPayment 2690 ≤ upperValue ((point split endpoint 4096 2690+point split endpoint 4096 2691)/2)
    have hp : upperPayment 2690 = (199447359445:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2690+point split endpoint 4096 2691)/2 = (643817627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643817627:ℝ)/168755200)*ClassicalSixthBranch.v ((643817627:ℝ)/168755200)/ClassicalSixthBranch.r = (100294161733097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2690
  · change upperPayment 2691 ≤ upperValue ((point split endpoint 4096 2691+point split endpoint 4096 2692)/2)
    have hp : upperPayment 2691 = (199329367966:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2691+point split endpoint 4096 2692)/2 = (643842777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643842777:ℝ)/168755200)*ClassicalSixthBranch.v ((643842777:ℝ)/168755200)/ClassicalSixthBranch.r = (100273591193985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2691
  · change upperPayment 2692 ≤ upperValue ((point split endpoint 4096 2692+point split endpoint 4096 2693)/2)
    have hp : upperPayment 2692 = (199211346144:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2692+point split endpoint 4096 2693)/2 = (643867927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643867927:ℝ)/168755200)*ClassicalSixthBranch.v ((643867927:ℝ)/168755200)/ClassicalSixthBranch.r = (100253022678945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2692
  · change upperPayment 2693 ≤ upperValue ((point split endpoint 4096 2693+point split endpoint 4096 2694)/2)
    have hp : upperPayment 2693 = (199093293972:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2693+point split endpoint 4096 2694)/2 = (643893077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643893077:ℝ)/168755200)*ClassicalSixthBranch.v ((643893077:ℝ)/168755200)/ClassicalSixthBranch.r = (100232456187977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2693
  · change upperPayment 2694 ≤ upperValue ((point split endpoint 4096 2694+point split endpoint 4096 2695)/2)
    have hp : upperPayment 2694 = (198975211444:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2694+point split endpoint 4096 2695)/2 = (643918227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643918227:ℝ)/168755200)*ClassicalSixthBranch.v ((643918227:ℝ)/168755200)/ClassicalSixthBranch.r = (100211891721081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2694
  · change upperPayment 2695 ≤ upperValue ((point split endpoint 4096 2695+point split endpoint 4096 2696)/2)
    have hp : upperPayment 2695 = (198857098552:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2695+point split endpoint 4096 2696)/2 = (643943377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643943377:ℝ)/168755200)*ClassicalSixthBranch.v ((643943377:ℝ)/168755200)/ClassicalSixthBranch.r = (100191329278257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2695
  · change upperPayment 2696 ≤ upperValue ((point split endpoint 4096 2696+point split endpoint 4096 2697)/2)
    have hp : upperPayment 2696 = (198738955290:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2696+point split endpoint 4096 2697)/2 = (643968527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643968527:ℝ)/168755200)*ClassicalSixthBranch.v ((643968527:ℝ)/168755200)/ClassicalSixthBranch.r = (100170768859505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2696
  · change upperPayment 2697 ≤ upperValue ((point split endpoint 4096 2697+point split endpoint 4096 2698)/2)
    have hp : upperPayment 2697 = (198620781651:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2697+point split endpoint 4096 2698)/2 = (643993677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643993677:ℝ)/168755200)*ClassicalSixthBranch.v ((643993677:ℝ)/168755200)/ClassicalSixthBranch.r = (100150210464825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2697
  · change upperPayment 2698 ≤ upperValue ((point split endpoint 4096 2698+point split endpoint 4096 2699)/2)
    have hp : upperPayment 2698 = (198502577628:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2698+point split endpoint 4096 2699)/2 = (644018827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644018827:ℝ)/168755200)*ClassicalSixthBranch.v ((644018827:ℝ)/168755200)/ClassicalSixthBranch.r = (100129654094217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2698
  · change upperPayment 2699 ≤ upperValue ((point split endpoint 4096 2699+point split endpoint 4096 2700)/2)
    have hp : upperPayment 2699 = (198384343214:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2699+point split endpoint 4096 2700)/2 = (644043977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644043977:ℝ)/168755200)*ClassicalSixthBranch.v ((644043977:ℝ)/168755200)/ClassicalSixthBranch.r = (100109099747681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2699
  · change upperPayment 2700 ≤ upperValue ((point split endpoint 4096 2700+point split endpoint 4096 2701)/2)
    have hp : upperPayment 2700 = (198266078402:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2700+point split endpoint 4096 2701)/2 = (644069127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644069127:ℝ)/168755200)*ClassicalSixthBranch.v ((644069127:ℝ)/168755200)/ClassicalSixthBranch.r = (100088547425217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2700
  · change upperPayment 2701 ≤ upperValue ((point split endpoint 4096 2701+point split endpoint 4096 2702)/2)
    have hp : upperPayment 2701 = (198147783186:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2701+point split endpoint 4096 2702)/2 = (644094277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644094277:ℝ)/168755200)*ClassicalSixthBranch.v ((644094277:ℝ)/168755200)/ClassicalSixthBranch.r = (100067997126825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2701
  · change upperPayment 2702 ≤ upperValue ((point split endpoint 4096 2702+point split endpoint 4096 2703)/2)
    have hp : upperPayment 2702 = (198029457558:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2702+point split endpoint 4096 2703)/2 = (644119427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644119427:ℝ)/168755200)*ClassicalSixthBranch.v ((644119427:ℝ)/168755200)/ClassicalSixthBranch.r = (100047448852505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2702
  · change upperPayment 2703 ≤ upperValue ((point split endpoint 4096 2703+point split endpoint 4096 2704)/2)
    have hp : upperPayment 2703 = (197911101512:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2703+point split endpoint 4096 2704)/2 = (644144577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644144577:ℝ)/168755200)*ClassicalSixthBranch.v ((644144577:ℝ)/168755200)/ClassicalSixthBranch.r = (100026902602257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2703
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_168
