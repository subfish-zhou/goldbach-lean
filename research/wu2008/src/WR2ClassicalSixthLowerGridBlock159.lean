import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints159
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_159 (j : Fin 16) : lowerPayment (16*159+j.val) ≤
    lowerValue ((point 2 split 4096 (16*159+j.val)+point 2 split 4096 (16*159+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2544 ≤ lowerValue ((point 2 split 4096 2544+point 2 split 4096 2545)/2)
    have hp : lowerPayment 2544 = (281179431549:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2544+point 2 split 4096 2545)/2 = (485758059:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((485758059:ℝ)/168755200)/ClassicalSixthBranch.v ((485758059:ℝ)/168755200) = (617290533211:ℝ)/298422388632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2544
  · change lowerPayment 2545 ≤ lowerValue ((point 2 split 4096 2545+point 2 split 4096 2546)/2)
    have hp : lowerPayment 2545 = (281267298345:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2545+point 2 split 4096 2546)/2 = (485816321:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((485816321:ℝ)/168755200)/ClassicalSixthBranch.v ((485816321:ℝ)/168755200) = (617213219537:ℝ)/298374380744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2545
  · change lowerPayment 2546 ≤ lowerValue ((point 2 split 4096 2546+point 2 split 4096 2547)/2)
    have hp : lowerPayment 2546 = (281355163342:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2546+point 2 split 4096 2547)/2 = (485874583:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((485874583:ℝ)/168755200)/ClassicalSixthBranch.v ((485874583:ℝ)/168755200) = (617135905863:ℝ)/298326372856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2546
  · change lowerPayment 2547 ≤ lowerValue ((point 2 split 4096 2547+point 2 split 4096 2548)/2)
    have hp : lowerPayment 2547 = (281443026554:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2547+point 2 split 4096 2548)/2 = (97186569:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((97186569:ℝ)/33751040)/ClassicalSixthBranch.v ((97186569:ℝ)/33751040) = (617058592189:ℝ)/298278364968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2547
  · change lowerPayment 2548 ≤ lowerValue ((point 2 split 4096 2548+point 2 split 4096 2549)/2)
    have hp : lowerPayment 2548 = (281530887995:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2548+point 2 split 4096 2549)/2 = (485991107:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((485991107:ℝ)/168755200)/ClassicalSixthBranch.v ((485991107:ℝ)/168755200) = (123396255703:ℝ)/59646071416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2548
  · change lowerPayment 2549 ≤ lowerValue ((point 2 split 4096 2549+point 2 split 4096 2550)/2)
    have hp : lowerPayment 2549 = (281618747680:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2549+point 2 split 4096 2550)/2 = (486049369:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((486049369:ℝ)/168755200)/ClassicalSixthBranch.v ((486049369:ℝ)/168755200) = (616903964841:ℝ)/298182349192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2549
  · change lowerPayment 2550 ≤ lowerValue ((point 2 split 4096 2550+point 2 split 4096 2551)/2)
    have hp : lowerPayment 2550 = (281706605622:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2550+point 2 split 4096 2551)/2 = (486107631:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((486107631:ℝ)/168755200)/ClassicalSixthBranch.v ((486107631:ℝ)/168755200) = (616826651167:ℝ)/298134341304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2550
  · change lowerPayment 2551 ≤ lowerValue ((point 2 split 4096 2551+point 2 split 4096 2552)/2)
    have hp : lowerPayment 2551 = (281794461838:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2551+point 2 split 4096 2552)/2 = (486165893:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((486165893:ℝ)/168755200)/ClassicalSixthBranch.v ((486165893:ℝ)/168755200) = (616749337493:ℝ)/298086333416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2551
  · change lowerPayment 2552 ≤ lowerValue ((point 2 split 4096 2552+point 2 split 4096 2553)/2)
    have hp : lowerPayment 2552 = (281882316340:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2552+point 2 split 4096 2553)/2 = (97244831:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((97244831:ℝ)/33751040)/ClassicalSixthBranch.v ((97244831:ℝ)/33751040) = (616672023819:ℝ)/298038325528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2552
  · change lowerPayment 2553 ≤ lowerValue ((point 2 split 4096 2553+point 2 split 4096 2554)/2)
    have hp : lowerPayment 2553 = (281970169143:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2553+point 2 split 4096 2554)/2 = (486282417:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((486282417:ℝ)/168755200)/ClassicalSixthBranch.v ((486282417:ℝ)/168755200) = (123318942029:ℝ)/59598063528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2553
  · change lowerPayment 2554 ≤ lowerValue ((point 2 split 4096 2554+point 2 split 4096 2555)/2)
    have hp : lowerPayment 2554 = (282058020262:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2554+point 2 split 4096 2555)/2 = (486340679:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((486340679:ℝ)/168755200)/ClassicalSixthBranch.v ((486340679:ℝ)/168755200) = (616517396471:ℝ)/297942309752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2554
  · change lowerPayment 2555 ≤ lowerValue ((point 2 split 4096 2555+point 2 split 4096 2556)/2)
    have hp : lowerPayment 2555 = (282145869712:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2555+point 2 split 4096 2556)/2 = (486398941:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((486398941:ℝ)/168755200)/ClassicalSixthBranch.v ((486398941:ℝ)/168755200) = (616440082797:ℝ)/297894301864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2555
  · change lowerPayment 2556 ≤ lowerValue ((point 2 split 4096 2556+point 2 split 4096 2557)/2)
    have hp : lowerPayment 2556 = (282233717506:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2556+point 2 split 4096 2557)/2 = (486457203:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((486457203:ℝ)/168755200)/ClassicalSixthBranch.v ((486457203:ℝ)/168755200) = (616362769123:ℝ)/297846293976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2556
  · change lowerPayment 2557 ≤ lowerValue ((point 2 split 4096 2557+point 2 split 4096 2558)/2)
    have hp : lowerPayment 2557 = (282321563659:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2557+point 2 split 4096 2558)/2 = (97303093:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((97303093:ℝ)/33751040)/ClassicalSixthBranch.v ((97303093:ℝ)/33751040) = (616285455449:ℝ)/297798286088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2557
  · change lowerPayment 2558 ≤ lowerValue ((point 2 split 4096 2558+point 2 split 4096 2559)/2)
    have hp : lowerPayment 2558 = (282409408186:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2558+point 2 split 4096 2559)/2 = (486573727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((486573727:ℝ)/168755200)/ClassicalSixthBranch.v ((486573727:ℝ)/168755200) = (24648325671:ℝ)/11910011128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2558
  · change lowerPayment 2559 ≤ lowerValue ((point 2 split 4096 2559+point 2 split 4096 2560)/2)
    have hp : lowerPayment 2559 = (282497251100:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2559+point 2 split 4096 2560)/2 = (486631989:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((486631989:ℝ)/168755200)/ClassicalSixthBranch.v ((486631989:ℝ)/168755200) = (616130828101:ℝ)/297702270312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2559
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_159
