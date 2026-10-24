import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints128
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_128 (j : Fin 16) : upperPayment (16*128+j.val) ≤
    upperValue ((point split endpoint 4096 (16*128+j.val)+point split endpoint 4096 (16*128+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2048 ≤ upperValue ((point split endpoint 4096 2048+point split endpoint 4096 2049)/2)
    have hp : upperPayment 2048 = (269219130468:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2048+point split endpoint 4096 2049)/2 = (627671327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627671327:ℝ)/168755200)*ClassicalSixthBranch.v ((627671327:ℝ)/168755200)/ClassicalSixthBranch.r = (113918222376017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2048
  · change upperPayment 2049 ≤ upperValue ((point split endpoint 4096 2049+point split endpoint 4096 2050)/2)
    have hp : upperPayment 2049 = (269119322944:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2049+point split endpoint 4096 2050)/2 = (627696477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627696477:ℝ)/168755200)*ClassicalSixthBranch.v ((627696477:ℝ)/168755200)/ClassicalSixthBranch.r = (113896352382681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2049
  · change upperPayment 2050 ≤ upperValue ((point split endpoint 4096 2050+point split endpoint 4096 2051)/2)
    have hp : upperPayment 2050 = (269019488943:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2050+point split endpoint 4096 2051)/2 = (627721627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627721627:ℝ)/168755200)*ClassicalSixthBranch.v ((627721627:ℝ)/168755200)/ClassicalSixthBranch.r = (113874484413417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2050
  · change upperPayment 2051 ≤ upperValue ((point split endpoint 4096 2051+point split endpoint 4096 2052)/2)
    have hp : upperPayment 2051 = (268919628460:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2051+point split endpoint 4096 2052)/2 = (627746777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627746777:ℝ)/168755200)*ClassicalSixthBranch.v ((627746777:ℝ)/168755200)/ClassicalSixthBranch.r = (113852618468225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2051
  · change upperPayment 2052 ≤ upperValue ((point split endpoint 4096 2052+point split endpoint 4096 2053)/2)
    have hp : upperPayment 2052 = (268819741489:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2052+point split endpoint 4096 2053)/2 = (627771927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627771927:ℝ)/168755200)*ClassicalSixthBranch.v ((627771927:ℝ)/168755200)/ClassicalSixthBranch.r = (113830754547105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2052
  · change upperPayment 2053 ≤ upperValue ((point split endpoint 4096 2053+point split endpoint 4096 2054)/2)
    have hp : upperPayment 2053 = (268719828026:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2053+point split endpoint 4096 2054)/2 = (627797077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627797077:ℝ)/168755200)*ClassicalSixthBranch.v ((627797077:ℝ)/168755200)/ClassicalSixthBranch.r = (113808892650057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2053
  · change upperPayment 2054 ≤ upperValue ((point split endpoint 4096 2054+point split endpoint 4096 2055)/2)
    have hp : upperPayment 2054 = (268619888065:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2054+point split endpoint 4096 2055)/2 = (627822227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627822227:ℝ)/168755200)*ClassicalSixthBranch.v ((627822227:ℝ)/168755200)/ClassicalSixthBranch.r = (113787032777081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2054
  · change upperPayment 2055 ≤ upperValue ((point split endpoint 4096 2055+point split endpoint 4096 2056)/2)
    have hp : upperPayment 2055 = (268519921601:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2055+point split endpoint 4096 2056)/2 = (627847377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627847377:ℝ)/168755200)*ClassicalSixthBranch.v ((627847377:ℝ)/168755200)/ClassicalSixthBranch.r = (113765174928177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2055
  · change upperPayment 2056 ≤ upperValue ((point split endpoint 4096 2056+point split endpoint 4096 2057)/2)
    have hp : upperPayment 2056 = (268419928628:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2056+point split endpoint 4096 2057)/2 = (627872527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627872527:ℝ)/168755200)*ClassicalSixthBranch.v ((627872527:ℝ)/168755200)/ClassicalSixthBranch.r = (113743319103345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2056
  · change upperPayment 2057 ≤ upperValue ((point split endpoint 4096 2057+point split endpoint 4096 2058)/2)
    have hp : upperPayment 2057 = (268319909141:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2057+point split endpoint 4096 2058)/2 = (627897677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627897677:ℝ)/168755200)*ClassicalSixthBranch.v ((627897677:ℝ)/168755200)/ClassicalSixthBranch.r = (113721465302585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2057
  · change upperPayment 2058 ≤ upperValue ((point split endpoint 4096 2058+point split endpoint 4096 2059)/2)
    have hp : upperPayment 2058 = (268219863136:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2058+point split endpoint 4096 2059)/2 = (627922827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627922827:ℝ)/168755200)*ClassicalSixthBranch.v ((627922827:ℝ)/168755200)/ClassicalSixthBranch.r = (113699613525897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2058
  · change upperPayment 2059 ≤ upperValue ((point split endpoint 4096 2059+point split endpoint 4096 2060)/2)
    have hp : upperPayment 2059 = (268119790605:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2059+point split endpoint 4096 2060)/2 = (627947977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627947977:ℝ)/168755200)*ClassicalSixthBranch.v ((627947977:ℝ)/168755200)/ClassicalSixthBranch.r = (113677763773281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2059
  · change upperPayment 2060 ≤ upperValue ((point split endpoint 4096 2060+point split endpoint 4096 2061)/2)
    have hp : upperPayment 2060 = (268019691545:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2060+point split endpoint 4096 2061)/2 = (627973127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627973127:ℝ)/168755200)*ClassicalSixthBranch.v ((627973127:ℝ)/168755200)/ClassicalSixthBranch.r = (113655916044737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2060
  · change upperPayment 2061 ≤ upperValue ((point split endpoint 4096 2061+point split endpoint 4096 2062)/2)
    have hp : upperPayment 2061 = (267919565950:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2061+point split endpoint 4096 2062)/2 = (627998277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((627998277:ℝ)/168755200)*ClassicalSixthBranch.v ((627998277:ℝ)/168755200)/ClassicalSixthBranch.r = (113634070340265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2061
  · change upperPayment 2062 ≤ upperValue ((point split endpoint 4096 2062+point split endpoint 4096 2063)/2)
    have hp : upperPayment 2062 = (267819413815:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2062+point split endpoint 4096 2063)/2 = (628023427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((628023427:ℝ)/168755200)*ClassicalSixthBranch.v ((628023427:ℝ)/168755200)/ClassicalSixthBranch.r = (113612226659865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2062
  · change upperPayment 2063 ≤ upperValue ((point split endpoint 4096 2063+point split endpoint 4096 2064)/2)
    have hp : upperPayment 2063 = (267719235134:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2063+point split endpoint 4096 2064)/2 = (6097559:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((6097559:ℝ)/1638400)*ClassicalSixthBranch.v ((6097559:ℝ)/1638400)/ClassicalSixthBranch.r = (1102819271879:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2063
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_128
