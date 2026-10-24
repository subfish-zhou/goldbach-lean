import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints061
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_061 (j : Fin 16) : upperPayment (16*61+j.val) ≤
    upperValue ((point split endpoint 4096 (16*61+j.val)+point split endpoint 4096 (16*61+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 976 ≤ upperValue ((point split endpoint 4096 976+point split endpoint 4096 977)/2)
    have hp : upperPayment 976 = (361963135691:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 976+point split endpoint 4096 977)/2 = (600710527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600710527:ℝ)/168755200)*ClassicalSixthBranch.v ((600710527:ℝ)/168755200)/ClassicalSixthBranch.r = (138526955713425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_976
  · change upperPayment 977 ≤ upperValue ((point split endpoint 4096 977+point split endpoint 4096 978)/2)
    have hp : upperPayment 977 = (361889073725:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 977+point split endpoint 4096 978)/2 = (600735677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600735677:ℝ)/168755200)*ClassicalSixthBranch.v ((600735677:ℝ)/168755200)/ClassicalSixthBranch.r = (138502915914905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_977
  · change upperPayment 978 ≤ upperValue ((point split endpoint 4096 978+point split endpoint 4096 979)/2)
    have hp : upperPayment 978 = (361814989861:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 978+point split endpoint 4096 979)/2 = (600760827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600760827:ℝ)/168755200)*ClassicalSixthBranch.v ((600760827:ℝ)/168755200)/ClassicalSixthBranch.r = (138478878140457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_978
  · change upperPayment 979 ≤ upperValue ((point split endpoint 4096 979+point split endpoint 4096 980)/2)
    have hp : upperPayment 979 = (361740884094:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 979+point split endpoint 4096 980)/2 = (600785977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600785977:ℝ)/168755200)*ClassicalSixthBranch.v ((600785977:ℝ)/168755200)/ClassicalSixthBranch.r = (138454842390081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_979
  · change upperPayment 980 ≤ upperValue ((point split endpoint 4096 980+point split endpoint 4096 981)/2)
    have hp : upperPayment 980 = (361666756423:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 980+point split endpoint 4096 981)/2 = (600811127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600811127:ℝ)/168755200)*ClassicalSixthBranch.v ((600811127:ℝ)/168755200)/ClassicalSixthBranch.r = (138430808663777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_980
  · change upperPayment 981 ≤ upperValue ((point split endpoint 4096 981+point split endpoint 4096 982)/2)
    have hp : upperPayment 981 = (361592606842:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 981+point split endpoint 4096 982)/2 = (600836277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600836277:ℝ)/168755200)*ClassicalSixthBranch.v ((600836277:ℝ)/168755200)/ClassicalSixthBranch.r = (138406776961545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_981
  · change upperPayment 982 ≤ upperValue ((point split endpoint 4096 982+point split endpoint 4096 983)/2)
    have hp : upperPayment 982 = (361518435349:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 982+point split endpoint 4096 983)/2 = (600861427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600861427:ℝ)/168755200)*ClassicalSixthBranch.v ((600861427:ℝ)/168755200)/ClassicalSixthBranch.r = (138382747283385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_982
  · change upperPayment 983 ≤ upperValue ((point split endpoint 4096 983+point split endpoint 4096 984)/2)
    have hp : upperPayment 983 = (361444241941:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 983+point split endpoint 4096 984)/2 = (600886577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600886577:ℝ)/168755200)*ClassicalSixthBranch.v ((600886577:ℝ)/168755200)/ClassicalSixthBranch.r = (138358719629297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_983
  · change upperPayment 984 ≤ upperValue ((point split endpoint 4096 984+point split endpoint 4096 985)/2)
    have hp : upperPayment 984 = (361370026614:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 984+point split endpoint 4096 985)/2 = (600911727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600911727:ℝ)/168755200)*ClassicalSixthBranch.v ((600911727:ℝ)/168755200)/ClassicalSixthBranch.r = (138334693999281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_984
  · change upperPayment 985 ≤ upperValue ((point split endpoint 4096 985+point split endpoint 4096 986)/2)
    have hp : upperPayment 985 = (361295789365:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 985+point split endpoint 4096 986)/2 = (600936877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600936877:ℝ)/168755200)*ClassicalSixthBranch.v ((600936877:ℝ)/168755200)/ClassicalSixthBranch.r = (138310670393337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_985
  · change upperPayment 986 ≤ upperValue ((point split endpoint 4096 986+point split endpoint 4096 987)/2)
    have hp : upperPayment 986 = (361221530190:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 986+point split endpoint 4096 987)/2 = (600962027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600962027:ℝ)/168755200)*ClassicalSixthBranch.v ((600962027:ℝ)/168755200)/ClassicalSixthBranch.r = (138286648811465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_986
  · change upperPayment 987 ≤ upperValue ((point split endpoint 4096 987+point split endpoint 4096 988)/2)
    have hp : upperPayment 987 = (361147249085:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 987+point split endpoint 4096 988)/2 = (600987177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600987177:ℝ)/168755200)*ClassicalSixthBranch.v ((600987177:ℝ)/168755200)/ClassicalSixthBranch.r = (138262629253665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_987
  · change upperPayment 988 ≤ upperValue ((point split endpoint 4096 988+point split endpoint 4096 989)/2)
    have hp : upperPayment 988 = (361072946049:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 988+point split endpoint 4096 989)/2 = (601012327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601012327:ℝ)/168755200)*ClassicalSixthBranch.v ((601012327:ℝ)/168755200)/ClassicalSixthBranch.r = (138238611719937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_988
  · change upperPayment 989 ≤ upperValue ((point split endpoint 4096 989+point split endpoint 4096 990)/2)
    have hp : upperPayment 989 = (360998621076:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 989+point split endpoint 4096 990)/2 = (601037477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601037477:ℝ)/168755200)*ClassicalSixthBranch.v ((601037477:ℝ)/168755200)/ClassicalSixthBranch.r = (138214596210281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_989
  · change upperPayment 990 ≤ upperValue ((point split endpoint 4096 990+point split endpoint 4096 991)/2)
    have hp : upperPayment 990 = (360924274164:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 990+point split endpoint 4096 991)/2 = (601062627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601062627:ℝ)/168755200)*ClassicalSixthBranch.v ((601062627:ℝ)/168755200)/ClassicalSixthBranch.r = (138190582724697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_990
  · change upperPayment 991 ≤ upperValue ((point split endpoint 4096 991+point split endpoint 4096 992)/2)
    have hp : upperPayment 991 = (360849905310:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 991+point split endpoint 4096 992)/2 = (601087777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601087777:ℝ)/168755200)*ClassicalSixthBranch.v ((601087777:ℝ)/168755200)/ClassicalSixthBranch.r = (138166571263185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_991
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_061
