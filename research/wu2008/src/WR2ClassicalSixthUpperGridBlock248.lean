import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints248
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_248 (j : Fin 16) : upperPayment (16*248+j.val) ≤
    upperValue ((point split endpoint 4096 (16*248+j.val)+point split endpoint 4096 (16*248+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3968 ≤ upperValue ((point split endpoint 4096 3968+point split endpoint 4096 3969)/2)
    have hp : upperPayment 3968 = (21181141031:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3968+point split endpoint 4096 3969)/2 = (675959327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675959327:ℝ)/168755200)*ClassicalSixthBranch.v ((675959327:ℝ)/168755200)/ClassicalSixthBranch.r = (75656661572177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3968
  · change upperPayment 3969 ≤ upperValue ((point split endpoint 4096 3969+point split endpoint 4096 3970)/2)
    have hp : upperPayment 3969 = (21017690220:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3969+point split endpoint 4096 3970)/2 = (675984477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675984477:ℝ)/168755200)*ClassicalSixthBranch.v ((675984477:ℝ)/168755200)/ClassicalSixthBranch.r = (75638677797081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3969
  · change upperPayment 3970 ≤ upperValue ((point split endpoint 4096 3970+point split endpoint 4096 3971)/2)
    have hp : upperPayment 3970 = (20854197596:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3970+point split endpoint 4096 3971)/2 = (676009627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676009627:ℝ)/168755200)*ClassicalSixthBranch.v ((676009627:ℝ)/168755200)/ClassicalSixthBranch.r = (75620696046057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3970
  · change upperPayment 3971 ≤ upperValue ((point split endpoint 4096 3971+point split endpoint 4096 3972)/2)
    have hp : upperPayment 3971 = (20690663147:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3971+point split endpoint 4096 3972)/2 = (676034777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676034777:ℝ)/168755200)*ClassicalSixthBranch.v ((676034777:ℝ)/168755200)/ClassicalSixthBranch.r = (75602716319105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3971
  · change upperPayment 3972 ≤ upperValue ((point split endpoint 4096 3972+point split endpoint 4096 3973)/2)
    have hp : upperPayment 3972 = (20527086862:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3972+point split endpoint 4096 3973)/2 = (676059927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676059927:ℝ)/168755200)*ClassicalSixthBranch.v ((676059927:ℝ)/168755200)/ClassicalSixthBranch.r = (75584738616225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3972
  · change upperPayment 3973 ≤ upperValue ((point split endpoint 4096 3973+point split endpoint 4096 3974)/2)
    have hp : upperPayment 3973 = (20363468728:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3973+point split endpoint 4096 3974)/2 = (676085077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676085077:ℝ)/168755200)*ClassicalSixthBranch.v ((676085077:ℝ)/168755200)/ClassicalSixthBranch.r = (75566762937417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3973
  · change upperPayment 3974 ≤ upperValue ((point split endpoint 4096 3974+point split endpoint 4096 3975)/2)
    have hp : upperPayment 3974 = (20199808735:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3974+point split endpoint 4096 3975)/2 = (676110227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676110227:ℝ)/168755200)*ClassicalSixthBranch.v ((676110227:ℝ)/168755200)/ClassicalSixthBranch.r = (75548789282681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3974
  · change upperPayment 3975 ≤ upperValue ((point split endpoint 4096 3975+point split endpoint 4096 3976)/2)
    have hp : upperPayment 3975 = (20036106871:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3975+point split endpoint 4096 3976)/2 = (676135377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676135377:ℝ)/168755200)*ClassicalSixthBranch.v ((676135377:ℝ)/168755200)/ClassicalSixthBranch.r = (75530817652017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3975
  · change upperPayment 3976 ≤ upperValue ((point split endpoint 4096 3976+point split endpoint 4096 3977)/2)
    have hp : upperPayment 3976 = (19872363124:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3976+point split endpoint 4096 3977)/2 = (676160527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676160527:ℝ)/168755200)*ClassicalSixthBranch.v ((676160527:ℝ)/168755200)/ClassicalSixthBranch.r = (75512848045425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3976
  · change upperPayment 3977 ≤ upperValue ((point split endpoint 4096 3977+point split endpoint 4096 3978)/2)
    have hp : upperPayment 3977 = (19708577482:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3977+point split endpoint 4096 3978)/2 = (676185677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676185677:ℝ)/168755200)*ClassicalSixthBranch.v ((676185677:ℝ)/168755200)/ClassicalSixthBranch.r = (75494880462905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3977
  · change upperPayment 3978 ≤ upperValue ((point split endpoint 4096 3978+point split endpoint 4096 3979)/2)
    have hp : upperPayment 3978 = (19544749934:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3978+point split endpoint 4096 3979)/2 = (676210827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676210827:ℝ)/168755200)*ClassicalSixthBranch.v ((676210827:ℝ)/168755200)/ClassicalSixthBranch.r = (75476914904457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3978
  · change upperPayment 3979 ≤ upperValue ((point split endpoint 4096 3979+point split endpoint 4096 3980)/2)
    have hp : upperPayment 3979 = (19380880468:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3979+point split endpoint 4096 3980)/2 = (676235977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676235977:ℝ)/168755200)*ClassicalSixthBranch.v ((676235977:ℝ)/168755200)/ClassicalSixthBranch.r = (75458951370081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3979
  · change upperPayment 3980 ≤ upperValue ((point split endpoint 4096 3980+point split endpoint 4096 3981)/2)
    have hp : upperPayment 3980 = (19216969073:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3980+point split endpoint 4096 3981)/2 = (676261127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676261127:ℝ)/168755200)*ClassicalSixthBranch.v ((676261127:ℝ)/168755200)/ClassicalSixthBranch.r = (75440989859777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3980
  · change upperPayment 3981 ≤ upperValue ((point split endpoint 4096 3981+point split endpoint 4096 3982)/2)
    have hp : upperPayment 3981 = (19053015737:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3981+point split endpoint 4096 3982)/2 = (676286277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676286277:ℝ)/168755200)*ClassicalSixthBranch.v ((676286277:ℝ)/168755200)/ClassicalSixthBranch.r = (75423030373545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3981
  · change upperPayment 3982 ≤ upperValue ((point split endpoint 4096 3982+point split endpoint 4096 3983)/2)
    have hp : upperPayment 3982 = (18889020448:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3982+point split endpoint 4096 3983)/2 = (676311427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676311427:ℝ)/168755200)*ClassicalSixthBranch.v ((676311427:ℝ)/168755200)/ClassicalSixthBranch.r = (75405072911385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3982
  · change upperPayment 3983 ≤ upperValue ((point split endpoint 4096 3983+point split endpoint 4096 3984)/2)
    have hp : upperPayment 3983 = (18724983194:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3983+point split endpoint 4096 3984)/2 = (676336577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676336577:ℝ)/168755200)*ClassicalSixthBranch.v ((676336577:ℝ)/168755200)/ClassicalSixthBranch.r = (75387117473297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3983
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_248
