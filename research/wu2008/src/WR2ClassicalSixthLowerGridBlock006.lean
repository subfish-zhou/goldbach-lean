import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints006
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_006 (j : Fin 16) : lowerPayment (16*6+j.val) ≤
    lowerValue ((point 2 split 4096 (16*6+j.val)+point 2 split 4096 (16*6+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 96 ≤ lowerValue ((point 2 split 4096 96+point 2 split 4096 97)/2)
    have hp : lowerPayment 96 = (15390006442:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 96+point 2 split 4096 97)/2 = (343132683:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((343132683:ℝ)/168755200)/ClassicalSixthBranch.v ((343132683:ℝ)/168755200) = (806554407163:ℝ)/415945698456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_96
  · change lowerPayment 97 ≤ lowerValue ((point 2 split 4096 97+point 2 split 4096 98)/2)
    have hp : lowerPayment 97 = (15545863360:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 97+point 2 split 4096 98)/2 = (68638189:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((68638189:ℝ)/33751040)/ClassicalSixthBranch.v ((68638189:ℝ)/33751040) = (806477093489:ℝ)/415897690568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_97
  · change lowerPayment 98 ≤ lowerValue ((point 2 split 4096 98+point 2 split 4096 99)/2)
    have hp : lowerPayment 98 = (15701648133:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 98+point 2 split 4096 99)/2 = (343249207:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((343249207:ℝ)/168755200)/ClassicalSixthBranch.v ((343249207:ℝ)/168755200) = (161279955963:ℝ)/83169936536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_98
  · change lowerPayment 99 ≤ lowerValue ((point 2 split 4096 99+point 2 split 4096 100)/2)
    have hp : lowerPayment 99 = (15857360827:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 99+point 2 split 4096 100)/2 = (343307469:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((343307469:ℝ)/168755200)/ClassicalSixthBranch.v ((343307469:ℝ)/168755200) = (806322466141:ℝ)/415801674792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_99
  · change lowerPayment 100 ≤ lowerValue ((point 2 split 4096 100+point 2 split 4096 101)/2)
    have hp : lowerPayment 100 = (16013001506:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 100+point 2 split 4096 101)/2 = (343365731:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((343365731:ℝ)/168755200)/ClassicalSixthBranch.v ((343365731:ℝ)/168755200) = (806245152467:ℝ)/415753666904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_100
  · change lowerPayment 101 ≤ lowerValue ((point 2 split 4096 101+point 2 split 4096 102)/2)
    have hp : lowerPayment 101 = (16168570236:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 101+point 2 split 4096 102)/2 = (343423993:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((343423993:ℝ)/168755200)/ClassicalSixthBranch.v ((343423993:ℝ)/168755200) = (806167838793:ℝ)/415705659016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_101
  · change lowerPayment 102 ≤ lowerValue ((point 2 split 4096 102+point 2 split 4096 103)/2)
    have hp : lowerPayment 102 = (16324067083:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 102+point 2 split 4096 103)/2 = (68696451:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((68696451:ℝ)/33751040)/ClassicalSixthBranch.v ((68696451:ℝ)/33751040) = (806090525119:ℝ)/415657651128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_102
  · change lowerPayment 103 ≤ lowerValue ((point 2 split 4096 103+point 2 split 4096 104)/2)
    have hp : lowerPayment 103 = (16479492112:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 103+point 2 split 4096 104)/2 = (343540517:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((343540517:ℝ)/168755200)/ClassicalSixthBranch.v ((343540517:ℝ)/168755200) = (161202642289:ℝ)/83121928648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_103
  · change lowerPayment 104 ≤ lowerValue ((point 2 split 4096 104+point 2 split 4096 105)/2)
    have hp : lowerPayment 104 = (16634845389:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 104+point 2 split 4096 105)/2 = (343598779:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((343598779:ℝ)/168755200)/ClassicalSixthBranch.v ((343598779:ℝ)/168755200) = (805935897771:ℝ)/415561635352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_104
  · change lowerPayment 105 ≤ lowerValue ((point 2 split 4096 105+point 2 split 4096 106)/2)
    have hp : lowerPayment 105 = (16790126979:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 105+point 2 split 4096 106)/2 = (343657041:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((343657041:ℝ)/168755200)/ClassicalSixthBranch.v ((343657041:ℝ)/168755200) = (805858584097:ℝ)/415513627464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_105
  · change lowerPayment 106 ≤ lowerValue ((point 2 split 4096 106+point 2 split 4096 107)/2)
    have hp : lowerPayment 106 = (16945336947:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 106+point 2 split 4096 107)/2 = (343715303:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((343715303:ℝ)/168755200)/ClassicalSixthBranch.v ((343715303:ℝ)/168755200) = (805781270423:ℝ)/415465619576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_106
  · change lowerPayment 107 ≤ lowerValue ((point 2 split 4096 107+point 2 split 4096 108)/2)
    have hp : lowerPayment 107 = (17100475358:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 107+point 2 split 4096 108)/2 = (68754713:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((68754713:ℝ)/33751040)/ClassicalSixthBranch.v ((68754713:ℝ)/33751040) = (805703956749:ℝ)/415417611688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_107
  · change lowerPayment 108 ≤ lowerValue ((point 2 split 4096 108+point 2 split 4096 109)/2)
    have hp : lowerPayment 108 = (17255542278:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 108+point 2 split 4096 109)/2 = (343831827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((343831827:ℝ)/168755200)/ClassicalSixthBranch.v ((343831827:ℝ)/168755200) = (32225065723:ℝ)/16614784152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_108
  · change lowerPayment 109 ≤ lowerValue ((point 2 split 4096 109+point 2 split 4096 110)/2)
    have hp : lowerPayment 109 = (17410537771:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 109+point 2 split 4096 110)/2 = (343890089:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((343890089:ℝ)/168755200)/ClassicalSixthBranch.v ((343890089:ℝ)/168755200) = (805549329401:ℝ)/415321595912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_109
  · change lowerPayment 110 ≤ lowerValue ((point 2 split 4096 110+point 2 split 4096 111)/2)
    have hp : lowerPayment 110 = (17565461903:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 110+point 2 split 4096 111)/2 = (343948351:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((343948351:ℝ)/168755200)/ClassicalSixthBranch.v ((343948351:ℝ)/168755200) = (805472015727:ℝ)/415273588024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_110
  · change lowerPayment 111 ≤ lowerValue ((point 2 split 4096 111+point 2 split 4096 112)/2)
    have hp : lowerPayment 111 = (17720314737:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 111+point 2 split 4096 112)/2 = (344006613:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((344006613:ℝ)/168755200)/ClassicalSixthBranch.v ((344006613:ℝ)/168755200) = (805394702053:ℝ)/415225580136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_111
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_006
