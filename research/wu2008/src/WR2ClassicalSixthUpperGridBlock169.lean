import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints169
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_169 (j : Fin 16) : upperPayment (16*169+j.val) ≤
    upperValue ((point split endpoint 4096 (16*169+j.val)+point split endpoint 4096 (16*169+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2704 ≤ upperValue ((point split endpoint 4096 2704+point split endpoint 4096 2705)/2)
    have hp : upperPayment 2704 = (197792715041:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2704+point split endpoint 4096 2705)/2 = (644169727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644169727:ℝ)/168755200)*ClassicalSixthBranch.v ((644169727:ℝ)/168755200)/ClassicalSixthBranch.r = (100006358376081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2704
  · change upperPayment 2705 ≤ upperValue ((point split endpoint 4096 2705+point split endpoint 4096 2706)/2)
    have hp : upperPayment 2705 = (197674298138:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2705+point split endpoint 4096 2706)/2 = (644194877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644194877:ℝ)/168755200)*ClassicalSixthBranch.v ((644194877:ℝ)/168755200)/ClassicalSixthBranch.r = (970736079359:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2705
  · change upperPayment 2706 ≤ upperValue ((point split endpoint 4096 2706+point split endpoint 4096 2707)/2)
    have hp : upperPayment 2706 = (197555850796:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2706+point split endpoint 4096 2707)/2 = (644220027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644220027:ℝ)/168755200)*ClassicalSixthBranch.v ((644220027:ℝ)/168755200)/ClassicalSixthBranch.r = (99965275995945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2706
  · change upperPayment 2707 ≤ upperValue ((point split endpoint 4096 2707+point split endpoint 4096 2708)/2)
    have hp : upperPayment 2707 = (197437373008:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2707+point split endpoint 4096 2708)/2 = (644245177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644245177:ℝ)/168755200)*ClassicalSixthBranch.v ((644245177:ℝ)/168755200)/ClassicalSixthBranch.r = (99944737841985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2707
  · change upperPayment 2708 ≤ upperValue ((point split endpoint 4096 2708+point split endpoint 4096 2709)/2)
    have hp : upperPayment 2708 = (197318864767:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2708+point split endpoint 4096 2709)/2 = (644270327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644270327:ℝ)/168755200)*ClassicalSixthBranch.v ((644270327:ℝ)/168755200)/ClassicalSixthBranch.r = (99924201712097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2708
  · change upperPayment 2709 ≤ upperValue ((point split endpoint 4096 2709+point split endpoint 4096 2710)/2)
    have hp : upperPayment 2709 = (197200326068:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2709+point split endpoint 4096 2710)/2 = (644295477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644295477:ℝ)/168755200)*ClassicalSixthBranch.v ((644295477:ℝ)/168755200)/ClassicalSixthBranch.r = (99903667606281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2709
  · change upperPayment 2710 ≤ upperValue ((point split endpoint 4096 2710+point split endpoint 4096 2711)/2)
    have hp : upperPayment 2710 = (197081756901:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2710+point split endpoint 4096 2711)/2 = (644320627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644320627:ℝ)/168755200)*ClassicalSixthBranch.v ((644320627:ℝ)/168755200)/ClassicalSixthBranch.r = (99883135524537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2710
  · change upperPayment 2711 ≤ upperValue ((point split endpoint 4096 2711+point split endpoint 4096 2712)/2)
    have hp : upperPayment 2711 = (196963157262:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2711+point split endpoint 4096 2712)/2 = (644345777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644345777:ℝ)/168755200)*ClassicalSixthBranch.v ((644345777:ℝ)/168755200)/ClassicalSixthBranch.r = (99862605466865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2711
  · change upperPayment 2712 ≤ upperValue ((point split endpoint 4096 2712+point split endpoint 4096 2713)/2)
    have hp : upperPayment 2712 = (196844527142:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2712+point split endpoint 4096 2713)/2 = (644370927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644370927:ℝ)/168755200)*ClassicalSixthBranch.v ((644370927:ℝ)/168755200)/ClassicalSixthBranch.r = (99842077433265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2712
  · change upperPayment 2713 ≤ upperValue ((point split endpoint 4096 2713+point split endpoint 4096 2714)/2)
    have hp : upperPayment 2713 = (196725866535:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2713+point split endpoint 4096 2714)/2 = (644396077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644396077:ℝ)/168755200)*ClassicalSixthBranch.v ((644396077:ℝ)/168755200)/ClassicalSixthBranch.r = (99821551423737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2713
  · change upperPayment 2714 ≤ upperValue ((point split endpoint 4096 2714+point split endpoint 4096 2715)/2)
    have hp : upperPayment 2714 = (196607175435:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2714+point split endpoint 4096 2715)/2 = (644421227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644421227:ℝ)/168755200)*ClassicalSixthBranch.v ((644421227:ℝ)/168755200)/ClassicalSixthBranch.r = (99801027438281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2714
  · change upperPayment 2715 ≤ upperValue ((point split endpoint 4096 2715+point split endpoint 4096 2716)/2)
    have hp : upperPayment 2715 = (196488453833:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2715+point split endpoint 4096 2716)/2 = (644446377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644446377:ℝ)/168755200)*ClassicalSixthBranch.v ((644446377:ℝ)/168755200)/ClassicalSixthBranch.r = (99780505476897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2715
  · change upperPayment 2716 ≤ upperValue ((point split endpoint 4096 2716+point split endpoint 4096 2717)/2)
    have hp : upperPayment 2716 = (196369701724:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2716+point split endpoint 4096 2717)/2 = (644471527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644471527:ℝ)/168755200)*ClassicalSixthBranch.v ((644471527:ℝ)/168755200)/ClassicalSixthBranch.r = (99759985539585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2716
  · change upperPayment 2717 ≤ upperValue ((point split endpoint 4096 2717+point split endpoint 4096 2718)/2)
    have hp : upperPayment 2717 = (196250919100:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2717+point split endpoint 4096 2718)/2 = (644496677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644496677:ℝ)/168755200)*ClassicalSixthBranch.v ((644496677:ℝ)/168755200)/ClassicalSixthBranch.r = (99739467626345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2717
  · change upperPayment 2718 ≤ upperValue ((point split endpoint 4096 2718+point split endpoint 4096 2719)/2)
    have hp : upperPayment 2718 = (196132105955:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2718+point split endpoint 4096 2719)/2 = (644521827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644521827:ℝ)/168755200)*ClassicalSixthBranch.v ((644521827:ℝ)/168755200)/ClassicalSixthBranch.r = (99718951737177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2718
  · change upperPayment 2719 ≤ upperValue ((point split endpoint 4096 2719+point split endpoint 4096 2720)/2)
    have hp : upperPayment 2719 = (196013262281:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2719+point split endpoint 4096 2720)/2 = (644546977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((644546977:ℝ)/168755200)*ClassicalSixthBranch.v ((644546977:ℝ)/168755200)/ClassicalSixthBranch.r = (99698437872081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2719
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_169
