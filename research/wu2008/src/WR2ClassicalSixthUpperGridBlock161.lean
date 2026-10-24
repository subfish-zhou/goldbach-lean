import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints161
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_161 (j : Fin 16) : upperPayment (16*161+j.val) ≤
    upperValue ((point split endpoint 4096 (16*161+j.val)+point split endpoint 4096 (16*161+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2576 ≤ upperValue ((point split endpoint 4096 2576+point split endpoint 4096 2577)/2)
    have hp : upperPayment 2576 = (212701201686:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2576+point split endpoint 4096 2577)/2 = (640950527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640950527:ℝ)/168755200)*ClassicalSixthBranch.v ((640950527:ℝ)/168755200)/ClassicalSixthBranch.r = (102652470983825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2576
  · change upperPayment 2577 ≤ upperValue ((point split endpoint 4096 2577+point split endpoint 4096 2578)/2)
    have hp : upperPayment 2577 = (212586625202:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2577+point split endpoint 4096 2578)/2 = (640975677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640975677:ℝ)/168755200)*ClassicalSixthBranch.v ((640975677:ℝ)/168755200)/ClassicalSixthBranch.r = (102631669700505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2577
  · change upperPayment 2578 ≤ upperValue ((point split endpoint 4096 2578+point split endpoint 4096 2579)/2)
    have hp : upperPayment 2578 = (212472019136:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2578+point split endpoint 4096 2579)/2 = (6223309:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((6223309:ℝ)/1638400)*ClassicalSixthBranch.v ((6223309:ℝ)/1638400)/ClassicalSixthBranch.r = (996222043119:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2578
  · change upperPayment 2579 ≤ upperValue ((point split endpoint 4096 2579+point split endpoint 4096 2580)/2)
    have hp : upperPayment 2579 = (212357383482:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2579+point split endpoint 4096 2580)/2 = (641025977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641025977:ℝ)/168755200)*ClassicalSixthBranch.v ((641025977:ℝ)/168755200)/ClassicalSixthBranch.r = (102590073206081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2579
  · change upperPayment 2580 ≤ upperValue ((point split endpoint 4096 2580+point split endpoint 4096 2581)/2)
    have hp : upperPayment 2580 = (212242718233:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2580+point split endpoint 4096 2581)/2 = (641051127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641051127:ℝ)/168755200)*ClassicalSixthBranch.v ((641051127:ℝ)/168755200)/ClassicalSixthBranch.r = (102569277994977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2580
  · change upperPayment 2581 ≤ upperValue ((point split endpoint 4096 2581+point split endpoint 4096 2582)/2)
    have hp : upperPayment 2581 = (212128023382:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2581+point split endpoint 4096 2582)/2 = (641076277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641076277:ℝ)/168755200)*ClassicalSixthBranch.v ((641076277:ℝ)/168755200)/ClassicalSixthBranch.r = (102548484807945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2581
  · change upperPayment 2582 ≤ upperValue ((point split endpoint 4096 2582+point split endpoint 4096 2583)/2)
    have hp : upperPayment 2582 = (212013298924:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2582+point split endpoint 4096 2583)/2 = (641101427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641101427:ℝ)/168755200)*ClassicalSixthBranch.v ((641101427:ℝ)/168755200)/ClassicalSixthBranch.r = (102527693644985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2582
  · change upperPayment 2583 ≤ upperValue ((point split endpoint 4096 2583+point split endpoint 4096 2584)/2)
    have hp : upperPayment 2583 = (211898544852:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2583+point split endpoint 4096 2584)/2 = (641126577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641126577:ℝ)/168755200)*ClassicalSixthBranch.v ((641126577:ℝ)/168755200)/ClassicalSixthBranch.r = (102506904506097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2583
  · change upperPayment 2584 ≤ upperValue ((point split endpoint 4096 2584+point split endpoint 4096 2585)/2)
    have hp : upperPayment 2584 = (211783761158:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2584+point split endpoint 4096 2585)/2 = (641151727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641151727:ℝ)/168755200)*ClassicalSixthBranch.v ((641151727:ℝ)/168755200)/ClassicalSixthBranch.r = (102486117391281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2584
  · change upperPayment 2585 ≤ upperValue ((point split endpoint 4096 2585+point split endpoint 4096 2586)/2)
    have hp : upperPayment 2585 = (211668947837:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2585+point split endpoint 4096 2586)/2 = (641176877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641176877:ℝ)/168755200)*ClassicalSixthBranch.v ((641176877:ℝ)/168755200)/ClassicalSixthBranch.r = (102465332300537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2585
  · change upperPayment 2586 ≤ upperValue ((point split endpoint 4096 2586+point split endpoint 4096 2587)/2)
    have hp : upperPayment 2586 = (211554104882:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2586+point split endpoint 4096 2587)/2 = (641202027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641202027:ℝ)/168755200)*ClassicalSixthBranch.v ((641202027:ℝ)/168755200)/ClassicalSixthBranch.r = (102444549233865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2586
  · change upperPayment 2587 ≤ upperValue ((point split endpoint 4096 2587+point split endpoint 4096 2588)/2)
    have hp : upperPayment 2587 = (211439232287:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2587+point split endpoint 4096 2588)/2 = (641227177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641227177:ℝ)/168755200)*ClassicalSixthBranch.v ((641227177:ℝ)/168755200)/ClassicalSixthBranch.r = (102423768191265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2587
  · change upperPayment 2588 ≤ upperValue ((point split endpoint 4096 2588+point split endpoint 4096 2589)/2)
    have hp : upperPayment 2588 = (211324330044:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2588+point split endpoint 4096 2589)/2 = (641252327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641252327:ℝ)/168755200)*ClassicalSixthBranch.v ((641252327:ℝ)/168755200)/ClassicalSixthBranch.r = (102402989172737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2588
  · change upperPayment 2589 ≤ upperValue ((point split endpoint 4096 2589+point split endpoint 4096 2590)/2)
    have hp : upperPayment 2589 = (211209398148:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2589+point split endpoint 4096 2590)/2 = (641277477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641277477:ℝ)/168755200)*ClassicalSixthBranch.v ((641277477:ℝ)/168755200)/ClassicalSixthBranch.r = (102382212178281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2589
  · change upperPayment 2590 ≤ upperValue ((point split endpoint 4096 2590+point split endpoint 4096 2591)/2)
    have hp : upperPayment 2590 = (211094436591:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2590+point split endpoint 4096 2591)/2 = (641302627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641302627:ℝ)/168755200)*ClassicalSixthBranch.v ((641302627:ℝ)/168755200)/ClassicalSixthBranch.r = (102361437207897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2590
  · change upperPayment 2591 ≤ upperValue ((point split endpoint 4096 2591+point split endpoint 4096 2592)/2)
    have hp : upperPayment 2591 = (210979445368:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2591+point split endpoint 4096 2592)/2 = (641327777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641327777:ℝ)/168755200)*ClassicalSixthBranch.v ((641327777:ℝ)/168755200)/ClassicalSixthBranch.r = (102340664261585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2591
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_161
