import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints006
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_006 (j : Fin 16) : upperPayment (16*6+j.val) ≤
    upperValue ((point split endpoint 4096 (16*6+j.val)+point split endpoint 4096 (16*6+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 96 ≤ upperValue ((point split endpoint 4096 96+point split endpoint 4096 97)/2)
    have hp : upperPayment 96 = (418998364751:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 96+point split endpoint 4096 97)/2 = (578578527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578578527:ℝ)/168755200)*ClassicalSixthBranch.v ((578578527:ℝ)/168755200)/ClassicalSixthBranch.r = (160466589681105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_96
  · change upperPayment 97 ≤ upperValue ((point split endpoint 4096 97+point split endpoint 4096 98)/2)
    have hp : upperPayment 97 = (418942423080:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 97+point split endpoint 4096 98)/2 = (578603677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578603677:ℝ)/168755200)*ClassicalSixthBranch.v ((578603677:ℝ)/168755200)/ClassicalSixthBranch.r = (160440768699225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_97
  · change upperPayment 98 ≤ upperValue ((point split endpoint 4096 98+point split endpoint 4096 99)/2)
    have hp : upperPayment 98 = (418886461952:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 98+point split endpoint 4096 99)/2 = (578628827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578628827:ℝ)/168755200)*ClassicalSixthBranch.v ((578628827:ℝ)/168755200)/ClassicalSixthBranch.r = (160414949741417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_98
  · change upperPayment 99 ≤ upperValue ((point split endpoint 4096 99+point split endpoint 4096 100)/2)
    have hp : upperPayment 99 = (418830481366:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 99+point split endpoint 4096 100)/2 = (578653977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578653977:ℝ)/168755200)*ClassicalSixthBranch.v ((578653977:ℝ)/168755200)/ClassicalSixthBranch.r = (160389132807681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_99
  · change upperPayment 100 ≤ upperValue ((point split endpoint 4096 100+point split endpoint 4096 101)/2)
    have hp : upperPayment 100 = (418774481319:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 100+point split endpoint 4096 101)/2 = (578679127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578679127:ℝ)/168755200)*ClassicalSixthBranch.v ((578679127:ℝ)/168755200)/ClassicalSixthBranch.r = (160363317898017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_100
  · change upperPayment 101 ≤ upperValue ((point split endpoint 4096 101+point split endpoint 4096 102)/2)
    have hp : upperPayment 101 = (418718461808:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 101+point split endpoint 4096 102)/2 = (578704277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578704277:ℝ)/168755200)*ClassicalSixthBranch.v ((578704277:ℝ)/168755200)/ClassicalSixthBranch.r = (160337505012425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_101
  · change upperPayment 102 ≤ upperValue ((point split endpoint 4096 102+point split endpoint 4096 103)/2)
    have hp : upperPayment 102 = (418662422833:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 102+point split endpoint 4096 103)/2 = (578729427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578729427:ℝ)/168755200)*ClassicalSixthBranch.v ((578729427:ℝ)/168755200)/ClassicalSixthBranch.r = (160311694150905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_102
  · change upperPayment 103 ≤ upperValue ((point split endpoint 4096 103+point split endpoint 4096 104)/2)
    have hp : upperPayment 103 = (418606364389:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 103+point split endpoint 4096 104)/2 = (578754577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578754577:ℝ)/168755200)*ClassicalSixthBranch.v ((578754577:ℝ)/168755200)/ClassicalSixthBranch.r = (160285885313457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_103
  · change upperPayment 104 ≤ upperValue ((point split endpoint 4096 104+point split endpoint 4096 105)/2)
    have hp : upperPayment 104 = (418550286476:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 104+point split endpoint 4096 105)/2 = (578779727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578779727:ℝ)/168755200)*ClassicalSixthBranch.v ((578779727:ℝ)/168755200)/ClassicalSixthBranch.r = (160260078500081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_104
  · change upperPayment 105 ≤ upperValue ((point split endpoint 4096 105+point split endpoint 4096 106)/2)
    have hp : upperPayment 105 = (418494189091:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 105+point split endpoint 4096 106)/2 = (578804877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578804877:ℝ)/168755200)*ClassicalSixthBranch.v ((578804877:ℝ)/168755200)/ClassicalSixthBranch.r = (160234273710777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_105
  · change upperPayment 106 ≤ upperValue ((point split endpoint 4096 106+point split endpoint 4096 107)/2)
    have hp : upperPayment 106 = (418438072231:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 106+point split endpoint 4096 107)/2 = (5619709:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((5619709:ℝ)/1638400)*ClassicalSixthBranch.v ((5619709:ℝ)/1638400)/ClassicalSixthBranch.r = (1555422048015:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_106
  · change upperPayment 107 ≤ upperValue ((point split endpoint 4096 107+point split endpoint 4096 108)/2)
    have hp : upperPayment 107 = (418381935895:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 107+point split endpoint 4096 108)/2 = (578855177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578855177:ℝ)/168755200)*ClassicalSixthBranch.v ((578855177:ℝ)/168755200)/ClassicalSixthBranch.r = (160182670204385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_107
  · change upperPayment 108 ≤ upperValue ((point split endpoint 4096 108+point split endpoint 4096 109)/2)
    have hp : upperPayment 108 = (418325780081:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 108+point split endpoint 4096 109)/2 = (578880327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578880327:ℝ)/168755200)*ClassicalSixthBranch.v ((578880327:ℝ)/168755200)/ClassicalSixthBranch.r = (160156871487297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_108
  · change upperPayment 109 ≤ upperValue ((point split endpoint 4096 109+point split endpoint 4096 110)/2)
    have hp : upperPayment 109 = (418269604785:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 109+point split endpoint 4096 110)/2 = (578905477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578905477:ℝ)/168755200)*ClassicalSixthBranch.v ((578905477:ℝ)/168755200)/ClassicalSixthBranch.r = (160131074794281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_109
  · change upperPayment 110 ≤ upperValue ((point split endpoint 4096 110+point split endpoint 4096 111)/2)
    have hp : upperPayment 110 = (418213410006:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 110+point split endpoint 4096 111)/2 = (578930627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578930627:ℝ)/168755200)*ClassicalSixthBranch.v ((578930627:ℝ)/168755200)/ClassicalSixthBranch.r = (160105280125337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_110
  · change upperPayment 111 ≤ upperValue ((point split endpoint 4096 111+point split endpoint 4096 112)/2)
    have hp : upperPayment 111 = (418157195742:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 111+point split endpoint 4096 112)/2 = (578955777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578955777:ℝ)/168755200)*ClassicalSixthBranch.v ((578955777:ℝ)/168755200)/ClassicalSixthBranch.r = (160079487480465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_111
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_006
