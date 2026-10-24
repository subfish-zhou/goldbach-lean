import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints038
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_038 (j : Fin 16) : upperPayment (16*38+j.val) ≤
    upperValue ((point split endpoint 4096 (16*38+j.val)+point split endpoint 4096 (16*38+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 608 ≤ upperValue ((point split endpoint 4096 608+point split endpoint 4096 609)/2)
    have hp : upperPayment 608 = (387758270679:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 608+point split endpoint 4096 609)/2 = (591455327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591455327:ℝ)/168755200)*ClassicalSixthBranch.v ((591455327:ℝ)/168755200)/ClassicalSixthBranch.r = (147511027961297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_608
  · change upperPayment 609 ≤ upperValue ((point split endpoint 4096 609+point split endpoint 4096 610)/2)
    have hp : upperPayment 609 = (387692050136:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 609+point split endpoint 4096 610)/2 = (591480477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591480477:ℝ)/168755200)*ClassicalSixthBranch.v ((591480477:ℝ)/168755200)/ClassicalSixthBranch.r = (147486243304281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_609
  · change upperPayment 610 ≤ upperValue ((point split endpoint 4096 610+point split endpoint 4096 611)/2)
    have hp : upperPayment 610 = (387625808841:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 610+point split endpoint 4096 611)/2 = (591505627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591505627:ℝ)/168755200)*ClassicalSixthBranch.v ((591505627:ℝ)/168755200)/ClassicalSixthBranch.r = (147461460671337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_610
  · change upperPayment 611 ≤ upperValue ((point split endpoint 4096 611+point split endpoint 4096 612)/2)
    have hp : upperPayment 611 = (387559546790:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 611+point split endpoint 4096 612)/2 = (591530777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591530777:ℝ)/168755200)*ClassicalSixthBranch.v ((591530777:ℝ)/168755200)/ClassicalSixthBranch.r = (147436680062465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_611
  · change upperPayment 612 ≤ upperValue ((point split endpoint 4096 612+point split endpoint 4096 613)/2)
    have hp : upperPayment 612 = (387493263980:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 612+point split endpoint 4096 613)/2 = (591555927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591555927:ℝ)/168755200)*ClassicalSixthBranch.v ((591555927:ℝ)/168755200)/ClassicalSixthBranch.r = (147411901477665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_612
  · change upperPayment 613 ≤ upperValue ((point split endpoint 4096 613+point split endpoint 4096 614)/2)
    have hp : upperPayment 613 = (387426960410:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 613+point split endpoint 4096 614)/2 = (591581077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591581077:ℝ)/168755200)*ClassicalSixthBranch.v ((591581077:ℝ)/168755200)/ClassicalSixthBranch.r = (147387124916937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_613
  · change upperPayment 614 ≤ upperValue ((point split endpoint 4096 614+point split endpoint 4096 615)/2)
    have hp : upperPayment 614 = (387360636075:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 614+point split endpoint 4096 615)/2 = (591606227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591606227:ℝ)/168755200)*ClassicalSixthBranch.v ((591606227:ℝ)/168755200)/ClassicalSixthBranch.r = (147362350380281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_614
  · change upperPayment 615 ≤ upperValue ((point split endpoint 4096 615+point split endpoint 4096 616)/2)
    have hp : upperPayment 615 = (387294290974:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 615+point split endpoint 4096 616)/2 = (591631377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591631377:ℝ)/168755200)*ClassicalSixthBranch.v ((591631377:ℝ)/168755200)/ClassicalSixthBranch.r = (147337577867697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_615
  · change upperPayment 616 ≤ upperValue ((point split endpoint 4096 616+point split endpoint 4096 617)/2)
    have hp : upperPayment 616 = (387227925102:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 616+point split endpoint 4096 617)/2 = (591656527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591656527:ℝ)/168755200)*ClassicalSixthBranch.v ((591656527:ℝ)/168755200)/ClassicalSixthBranch.r = (147312807379185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_616
  · change upperPayment 617 ≤ upperValue ((point split endpoint 4096 617+point split endpoint 4096 618)/2)
    have hp : upperPayment 617 = (387161538458:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 617+point split endpoint 4096 618)/2 = (591681677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591681677:ℝ)/168755200)*ClassicalSixthBranch.v ((591681677:ℝ)/168755200)/ClassicalSixthBranch.r = (147288038914745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_617
  · change upperPayment 618 ≤ upperValue ((point split endpoint 4096 618+point split endpoint 4096 619)/2)
    have hp : upperPayment 618 = (387095131038:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 618+point split endpoint 4096 619)/2 = (591706827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591706827:ℝ)/168755200)*ClassicalSixthBranch.v ((591706827:ℝ)/168755200)/ClassicalSixthBranch.r = (147263272474377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_618
  · change upperPayment 619 ≤ upperValue ((point split endpoint 4096 619+point split endpoint 4096 620)/2)
    have hp : upperPayment 619 = (387028702840:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 619+point split endpoint 4096 620)/2 = (591731977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591731977:ℝ)/168755200)*ClassicalSixthBranch.v ((591731977:ℝ)/168755200)/ClassicalSixthBranch.r = (147238508058081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_619
  · change upperPayment 620 ≤ upperValue ((point split endpoint 4096 620+point split endpoint 4096 621)/2)
    have hp : upperPayment 620 = (386962253860:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 620+point split endpoint 4096 621)/2 = (591757127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591757127:ℝ)/168755200)*ClassicalSixthBranch.v ((591757127:ℝ)/168755200)/ClassicalSixthBranch.r = (147213745665857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_620
  · change upperPayment 621 ≤ upperValue ((point split endpoint 4096 621+point split endpoint 4096 622)/2)
    have hp : upperPayment 621 = (386895784097:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 621+point split endpoint 4096 622)/2 = (5745459:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((5745459:ℝ)/1638400)*ClassicalSixthBranch.v ((5745459:ℝ)/1638400)/ClassicalSixthBranch.r = (1429019274735:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_621
  · change upperPayment 622 ≤ upperValue ((point split endpoint 4096 622+point split endpoint 4096 623)/2)
    have hp : upperPayment 622 = (386829293546:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 622+point split endpoint 4096 623)/2 = (591807427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591807427:ℝ)/168755200)*ClassicalSixthBranch.v ((591807427:ℝ)/168755200)/ClassicalSixthBranch.r = (147164226953625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_622
  · change upperPayment 623 ≤ upperValue ((point split endpoint 4096 623+point split endpoint 4096 624)/2)
    have hp : upperPayment 623 = (386762782205:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 623+point split endpoint 4096 624)/2 = (591832577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591832577:ℝ)/168755200)*ClassicalSixthBranch.v ((591832577:ℝ)/168755200)/ClassicalSixthBranch.r = (147139470633617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_623
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_038
