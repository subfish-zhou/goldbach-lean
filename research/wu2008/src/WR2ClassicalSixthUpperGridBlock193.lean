import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints193
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_193 (j : Fin 16) : upperPayment (16*193+j.val) ≤
    upperValue ((point split endpoint 4096 (16*193+j.val)+point split endpoint 4096 (16*193+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3088 ≤ upperValue ((point split endpoint 4096 3088+point split endpoint 4096 3089)/2)
    have hp : upperPayment 3088 = (150015377759:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3088+point split endpoint 4096 3089)/2 = (653827327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653827327:ℝ)/168755200)*ClassicalSixthBranch.v ((653827327:ℝ)/168755200)/ClassicalSixthBranch.r = (92266994926737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3088
  · change upperPayment 3089 ≤ upperValue ((point split endpoint 4096 3089+point split endpoint 4096 3090)/2)
    have hp : upperPayment 3089 = (149884740016:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3089+point split endpoint 4096 3090)/2 = (653852477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653852477:ℝ)/168755200)*ClassicalSixthBranch.v ((653852477:ℝ)/168755200)/ClassicalSixthBranch.r = (92247229968281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3089
  · change upperPayment 3090 ≤ upperValue ((point split endpoint 4096 3090+point split endpoint 4096 3091)/2)
    have hp : upperPayment 3090 = (149754068980:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3090+point split endpoint 4096 3091)/2 = (653877627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653877627:ℝ)/168755200)*ClassicalSixthBranch.v ((653877627:ℝ)/168755200)/ClassicalSixthBranch.r = (92227467033897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3090
  · change upperPayment 3091 ≤ upperValue ((point split endpoint 4096 3091+point split endpoint 4096 3092)/2)
    have hp : upperPayment 3091 = (149623364643:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3091+point split endpoint 4096 3092)/2 = (653902777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653902777:ℝ)/168755200)*ClassicalSixthBranch.v ((653902777:ℝ)/168755200)/ClassicalSixthBranch.r = (92207706123585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3091
  · change upperPayment 3092 ≤ upperValue ((point split endpoint 4096 3092+point split endpoint 4096 3093)/2)
    have hp : upperPayment 3092 = (149492626997:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3092+point split endpoint 4096 3093)/2 = (653927927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653927927:ℝ)/168755200)*ClassicalSixthBranch.v ((653927927:ℝ)/168755200)/ClassicalSixthBranch.r = (92187947237345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3092
  · change upperPayment 3093 ≤ upperValue ((point split endpoint 4096 3093+point split endpoint 4096 3094)/2)
    have hp : upperPayment 3093 = (149361856035:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3093+point split endpoint 4096 3094)/2 = (6349059:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((6349059:ℝ)/1638400)*ClassicalSixthBranch.v ((6349059:ℝ)/1638400)/ClassicalSixthBranch.r = (894836799759:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3093
  · change upperPayment 3094 ≤ upperValue ((point split endpoint 4096 3094+point split endpoint 4096 3095)/2)
    have hp : upperPayment 3094 = (149231051748:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3094+point split endpoint 4096 3095)/2 = (653978227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653978227:ℝ)/168755200)*ClassicalSixthBranch.v ((653978227:ℝ)/168755200)/ClassicalSixthBranch.r = (92148435537081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3094
  · change upperPayment 3095 ≤ upperValue ((point split endpoint 4096 3095+point split endpoint 4096 3096)/2)
    have hp : upperPayment 3095 = (149100214128:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3095+point split endpoint 4096 3096)/2 = (654003377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654003377:ℝ)/168755200)*ClassicalSixthBranch.v ((654003377:ℝ)/168755200)/ClassicalSixthBranch.r = (92128682723057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3095
  · change upperPayment 3096 ≤ upperValue ((point split endpoint 4096 3096+point split endpoint 4096 3097)/2)
    have hp : upperPayment 3096 = (148969343167:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3096+point split endpoint 4096 3097)/2 = (654028527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654028527:ℝ)/168755200)*ClassicalSixthBranch.v ((654028527:ℝ)/168755200)/ClassicalSixthBranch.r = (92108931933105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3096
  · change upperPayment 3097 ≤ upperValue ((point split endpoint 4096 3097+point split endpoint 4096 3098)/2)
    have hp : upperPayment 3097 = (148838438857:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3097+point split endpoint 4096 3098)/2 = (654053677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654053677:ℝ)/168755200)*ClassicalSixthBranch.v ((654053677:ℝ)/168755200)/ClassicalSixthBranch.r = (92089183167225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3097
  · change upperPayment 3098 ≤ upperValue ((point split endpoint 4096 3098+point split endpoint 4096 3099)/2)
    have hp : upperPayment 3098 = (148707501191:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3098+point split endpoint 4096 3099)/2 = (654078827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654078827:ℝ)/168755200)*ClassicalSixthBranch.v ((654078827:ℝ)/168755200)/ClassicalSixthBranch.r = (92069436425417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3098
  · change upperPayment 3099 ≤ upperValue ((point split endpoint 4096 3099+point split endpoint 4096 3100)/2)
    have hp : upperPayment 3099 = (148576530159:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3099+point split endpoint 4096 3100)/2 = (654103977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654103977:ℝ)/168755200)*ClassicalSixthBranch.v ((654103977:ℝ)/168755200)/ClassicalSixthBranch.r = (92049691707681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3099
  · change upperPayment 3100 ≤ upperValue ((point split endpoint 4096 3100+point split endpoint 4096 3101)/2)
    have hp : upperPayment 3100 = (148445525754:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3100+point split endpoint 4096 3101)/2 = (654129127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654129127:ℝ)/168755200)*ClassicalSixthBranch.v ((654129127:ℝ)/168755200)/ClassicalSixthBranch.r = (92029949014017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3100
  · change upperPayment 3101 ≤ upperValue ((point split endpoint 4096 3101+point split endpoint 4096 3102)/2)
    have hp : upperPayment 3101 = (148314487969:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3101+point split endpoint 4096 3102)/2 = (654154277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654154277:ℝ)/168755200)*ClassicalSixthBranch.v ((654154277:ℝ)/168755200)/ClassicalSixthBranch.r = (92010208344425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3101
  · change upperPayment 3102 ≤ upperValue ((point split endpoint 4096 3102+point split endpoint 4096 3103)/2)
    have hp : upperPayment 3102 = (148183416794:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3102+point split endpoint 4096 3103)/2 = (654179427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654179427:ℝ)/168755200)*ClassicalSixthBranch.v ((654179427:ℝ)/168755200)/ClassicalSixthBranch.r = (91990469698905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3102
  · change upperPayment 3103 ≤ upperValue ((point split endpoint 4096 3103+point split endpoint 4096 3104)/2)
    have hp : upperPayment 3103 = (148052312222:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3103+point split endpoint 4096 3104)/2 = (654204577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((654204577:ℝ)/168755200)*ClassicalSixthBranch.v ((654204577:ℝ)/168755200)/ClassicalSixthBranch.r = (91970733077457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3103
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_193
