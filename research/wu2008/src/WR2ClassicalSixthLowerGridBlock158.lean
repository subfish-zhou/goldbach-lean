import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints158
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_158 (j : Fin 16) : lowerPayment (16*158+j.val) ≤
    lowerValue ((point 2 split 4096 (16*158+j.val)+point 2 split 4096 (16*158+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2528 ≤ lowerValue ((point 2 split 4096 2528+point 2 split 4096 2529)/2)
    have hp : lowerPayment 2528 = (279773306267:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2528+point 2 split 4096 2529)/2 = (484825867:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((484825867:ℝ)/168755200)/ClassicalSixthBranch.v ((484825867:ℝ)/168755200) = (123705510399:ℝ)/59838102968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2528
  · change lowerPayment 2529 ≤ lowerValue ((point 2 split 4096 2529+point 2 split 4096 2530)/2)
    have hp : lowerPayment 2529 = (279861203823:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2529+point 2 split 4096 2530)/2 = (484884129:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((484884129:ℝ)/168755200)/ClassicalSixthBranch.v ((484884129:ℝ)/168755200) = (618450238321:ℝ)/299142506952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2529
  · change lowerPayment 2530 ≤ lowerValue ((point 2 split 4096 2530+point 2 split 4096 2531)/2)
    have hp : lowerPayment 2530 = (279949099347:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2530+point 2 split 4096 2531)/2 = (484942391:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((484942391:ℝ)/168755200)/ClassicalSixthBranch.v ((484942391:ℝ)/168755200) = (618372924647:ℝ)/299094499064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2530
  · change lowerPayment 2531 ≤ lowerValue ((point 2 split 4096 2531+point 2 split 4096 2532)/2)
    have hp : lowerPayment 2531 = (280036992855:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2531+point 2 split 4096 2532)/2 = (485000653:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((485000653:ℝ)/168755200)/ClassicalSixthBranch.v ((485000653:ℝ)/168755200) = (618295610973:ℝ)/299046491176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2531
  · change lowerPayment 2532 ≤ lowerValue ((point 2 split 4096 2532+point 2 split 4096 2533)/2)
    have hp : lowerPayment 2532 = (280124884362:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2532+point 2 split 4096 2533)/2 = (97011783:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((97011783:ℝ)/33751040)/ClassicalSixthBranch.v ((97011783:ℝ)/33751040) = (618218297299:ℝ)/298998483288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2532
  · change lowerPayment 2533 ≤ lowerValue ((point 2 split 4096 2533+point 2 split 4096 2534)/2)
    have hp : lowerPayment 2533 = (280212773880:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2533+point 2 split 4096 2534)/2 = (485117177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((485117177:ℝ)/168755200)/ClassicalSixthBranch.v ((485117177:ℝ)/168755200) = (24725639345:ℝ)/11958019016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2533
  · change lowerPayment 2534 ≤ lowerValue ((point 2 split 4096 2534+point 2 split 4096 2535)/2)
    have hp : lowerPayment 2534 = (280300661426:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2534+point 2 split 4096 2535)/2 = (485175439:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((485175439:ℝ)/168755200)/ClassicalSixthBranch.v ((485175439:ℝ)/168755200) = (618063669951:ℝ)/298902467512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2534
  · change lowerPayment 2535 ≤ lowerValue ((point 2 split 4096 2535+point 2 split 4096 2536)/2)
    have hp : lowerPayment 2535 = (280388547013:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2535+point 2 split 4096 2536)/2 = (485233701:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((485233701:ℝ)/168755200)/ClassicalSixthBranch.v ((485233701:ℝ)/168755200) = (617986356277:ℝ)/298854459624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2535
  · change lowerPayment 2536 ≤ lowerValue ((point 2 split 4096 2536+point 2 split 4096 2537)/2)
    have hp : lowerPayment 2536 = (280476430656:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2536+point 2 split 4096 2537)/2 = (485291963:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((485291963:ℝ)/168755200)/ClassicalSixthBranch.v ((485291963:ℝ)/168755200) = (617909042603:ℝ)/298806451736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2536
  · change lowerPayment 2537 ≤ lowerValue ((point 2 split 4096 2537+point 2 split 4096 2538)/2)
    have hp : lowerPayment 2537 = (280564312370:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2537+point 2 split 4096 2538)/2 = (19414009:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((19414009:ℝ)/6750208)/ClassicalSixthBranch.v ((19414009:ℝ)/6750208) = (617831728929:ℝ)/298758443848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2537
  · change lowerPayment 2538 ≤ lowerValue ((point 2 split 4096 2538+point 2 split 4096 2539)/2)
    have hp : lowerPayment 2538 = (280652192168:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2538+point 2 split 4096 2539)/2 = (485408487:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((485408487:ℝ)/168755200)/ClassicalSixthBranch.v ((485408487:ℝ)/168755200) = (123550883051:ℝ)/59742087192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2538
  · change lowerPayment 2539 ≤ lowerValue ((point 2 split 4096 2539+point 2 split 4096 2540)/2)
    have hp : lowerPayment 2539 = (280740070066:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2539+point 2 split 4096 2540)/2 = (485466749:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((485466749:ℝ)/168755200)/ClassicalSixthBranch.v ((485466749:ℝ)/168755200) = (617677101581:ℝ)/298662428072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2539
  · change lowerPayment 2540 ≤ lowerValue ((point 2 split 4096 2540+point 2 split 4096 2541)/2)
    have hp : lowerPayment 2540 = (280827946077:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2540+point 2 split 4096 2541)/2 = (485525011:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((485525011:ℝ)/168755200)/ClassicalSixthBranch.v ((485525011:ℝ)/168755200) = (617599787907:ℝ)/298614420184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2540
  · change lowerPayment 2541 ≤ lowerValue ((point 2 split 4096 2541+point 2 split 4096 2542)/2)
    have hp : lowerPayment 2541 = (280915820217:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2541+point 2 split 4096 2542)/2 = (485583273:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((485583273:ℝ)/168755200)/ClassicalSixthBranch.v ((485583273:ℝ)/168755200) = (617522474233:ℝ)/298566412296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2541
  · change lowerPayment 2542 ≤ lowerValue ((point 2 split 4096 2542+point 2 split 4096 2543)/2)
    have hp : lowerPayment 2542 = (281003692499:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2542+point 2 split 4096 2543)/2 = (97128307:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((97128307:ℝ)/33751040)/ClassicalSixthBranch.v ((97128307:ℝ)/33751040) = (617445160559:ℝ)/298518404408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2542
  · change lowerPayment 2543 ≤ lowerValue ((point 2 split 4096 2543+point 2 split 4096 2544)/2)
    have hp : lowerPayment 2543 = (281091562938:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2543+point 2 split 4096 2544)/2 = (485699797:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((485699797:ℝ)/168755200)/ClassicalSixthBranch.v ((485699797:ℝ)/168755200) = (123473569377:ℝ)/59694079304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2543
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_158
