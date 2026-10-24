import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints160
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_160 (j : Fin 16) : upperPayment (16*160+j.val) ≤
    upperValue ((point split endpoint 4096 (16*160+j.val)+point split endpoint 4096 (16*160+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2560 ≤ upperValue ((point split endpoint 4096 2560+point split endpoint 4096 2561)/2)
    have hp : upperPayment 2560 = (214530407636:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2560+point split endpoint 4096 2561)/2 = (640548127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640548127:ℝ)/168755200)*ClassicalSixthBranch.v ((640548127:ℝ)/168755200)/ClassicalSixthBranch.r = (102985566790737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2560
  · change upperPayment 2561 ≤ upperValue ((point split endpoint 4096 2561+point split endpoint 4096 2562)/2)
    have hp : upperPayment 2561 = (214416303574:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2561+point split endpoint 4096 2562)/2 = (640573277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640573277:ℝ)/168755200)*ClassicalSixthBranch.v ((640573277:ℝ)/168755200)/ClassicalSixthBranch.r = (102964733122265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2561
  · change upperPayment 2562 ≤ upperValue ((point split endpoint 4096 2562+point split endpoint 4096 2563)/2)
    have hp : upperPayment 2562 = (214302170034:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2562+point split endpoint 4096 2563)/2 = (640598427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640598427:ℝ)/168755200)*ClassicalSixthBranch.v ((640598427:ℝ)/168755200)/ClassicalSixthBranch.r = (102943901477865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2562
  · change upperPayment 2563 ≤ upperValue ((point split endpoint 4096 2563+point split endpoint 4096 2564)/2)
    have hp : upperPayment 2563 = (214188007010:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2563+point split endpoint 4096 2564)/2 = (640623577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640623577:ℝ)/168755200)*ClassicalSixthBranch.v ((640623577:ℝ)/168755200)/ClassicalSixthBranch.r = (102923071857537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2563
  · change upperPayment 2564 ≤ upperValue ((point split endpoint 4096 2564+point split endpoint 4096 2565)/2)
    have hp : upperPayment 2564 = (214073814495:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2564+point split endpoint 4096 2565)/2 = (640648727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640648727:ℝ)/168755200)*ClassicalSixthBranch.v ((640648727:ℝ)/168755200)/ClassicalSixthBranch.r = (102902244261281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2564
  · change upperPayment 2565 ≤ upperValue ((point split endpoint 4096 2565+point split endpoint 4096 2566)/2)
    have hp : upperPayment 2565 = (213959592484:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2565+point split endpoint 4096 2566)/2 = (640673877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640673877:ℝ)/168755200)*ClassicalSixthBranch.v ((640673877:ℝ)/168755200)/ClassicalSixthBranch.r = (102881418689097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2565
  · change upperPayment 2566 ≤ upperValue ((point split endpoint 4096 2566+point split endpoint 4096 2567)/2)
    have hp : upperPayment 2566 = (213845340968:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2566+point split endpoint 4096 2567)/2 = (640699027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640699027:ℝ)/168755200)*ClassicalSixthBranch.v ((640699027:ℝ)/168755200)/ClassicalSixthBranch.r = (102860595140985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2566
  · change upperPayment 2567 ≤ upperValue ((point split endpoint 4096 2567+point split endpoint 4096 2568)/2)
    have hp : upperPayment 2567 = (213731059943:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2567+point split endpoint 4096 2568)/2 = (640724177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640724177:ℝ)/168755200)*ClassicalSixthBranch.v ((640724177:ℝ)/168755200)/ClassicalSixthBranch.r = (102839773616945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2567
  · change upperPayment 2568 ≤ upperValue ((point split endpoint 4096 2568+point split endpoint 4096 2569)/2)
    have hp : upperPayment 2568 = (213616749401:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2568+point split endpoint 4096 2569)/2 = (640749327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640749327:ℝ)/168755200)*ClassicalSixthBranch.v ((640749327:ℝ)/168755200)/ClassicalSixthBranch.r = (102818954116977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2568
  · change upperPayment 2569 ≤ upperValue ((point split endpoint 4096 2569+point split endpoint 4096 2570)/2)
    have hp : upperPayment 2569 = (213502409335:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2569+point split endpoint 4096 2570)/2 = (640774477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640774477:ℝ)/168755200)*ClassicalSixthBranch.v ((640774477:ℝ)/168755200)/ClassicalSixthBranch.r = (102798136641081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2569
  · change upperPayment 2570 ≤ upperValue ((point split endpoint 4096 2570+point split endpoint 4096 2571)/2)
    have hp : upperPayment 2570 = (213388039741:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2570+point split endpoint 4096 2571)/2 = (640799627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640799627:ℝ)/168755200)*ClassicalSixthBranch.v ((640799627:ℝ)/168755200)/ClassicalSixthBranch.r = (102777321189257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2570
  · change upperPayment 2571 ≤ upperValue ((point split endpoint 4096 2571+point split endpoint 4096 2572)/2)
    have hp : upperPayment 2571 = (213273640610:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2571+point split endpoint 4096 2572)/2 = (640824777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640824777:ℝ)/168755200)*ClassicalSixthBranch.v ((640824777:ℝ)/168755200)/ClassicalSixthBranch.r = (102756507761505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2571
  · change upperPayment 2572 ≤ upperValue ((point split endpoint 4096 2572+point split endpoint 4096 2573)/2)
    have hp : upperPayment 2572 = (213159211936:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2572+point split endpoint 4096 2573)/2 = (640849927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640849927:ℝ)/168755200)*ClassicalSixthBranch.v ((640849927:ℝ)/168755200)/ClassicalSixthBranch.r = (102735696357825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2572
  · change upperPayment 2573 ≤ upperValue ((point split endpoint 4096 2573+point split endpoint 4096 2574)/2)
    have hp : upperPayment 2573 = (213044753714:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2573+point split endpoint 4096 2574)/2 = (640875077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640875077:ℝ)/168755200)*ClassicalSixthBranch.v ((640875077:ℝ)/168755200)/ClassicalSixthBranch.r = (102714886978217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2573
  · change upperPayment 2574 ≤ upperValue ((point split endpoint 4096 2574+point split endpoint 4096 2575)/2)
    have hp : upperPayment 2574 = (212930265935:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2574+point split endpoint 4096 2575)/2 = (640900227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640900227:ℝ)/168755200)*ClassicalSixthBranch.v ((640900227:ℝ)/168755200)/ClassicalSixthBranch.r = (102694079622681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2574
  · change upperPayment 2575 ≤ upperValue ((point split endpoint 4096 2575+point split endpoint 4096 2576)/2)
    have hp : upperPayment 2575 = (212815748595:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2575+point split endpoint 4096 2576)/2 = (640925377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640925377:ℝ)/168755200)*ClassicalSixthBranch.v ((640925377:ℝ)/168755200)/ClassicalSixthBranch.r = (102673274291217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2575
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_160
