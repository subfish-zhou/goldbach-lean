import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints031
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_031 (j : Fin 16) : middlePayment (16*31+j.val) ≤
    middleValue ((point 4 cut 1024 (16*31+j.val)+point 4 cut 1024 (16*31+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 496 ≤ middleValue ((point 4 cut 1024 496+point 4 cut 1024 497)/2)
    have hp : middlePayment 496 = (645012788305:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 496+point 4 cut 1024 497)/2 = (84628829:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84628829:ℝ)/21094400) = (6794240:ℝ)/4272263 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84628829:ℝ)/21094400)-4 = (251229:ℝ)/21094400 by norm_num]
    exact paid_middle_496
  · change middlePayment 497 ≤ middleValue ((point 4 cut 1024 497+point 4 cut 1024 498)/2)
    have hp : middlePayment 497 = (645052423661:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 497+point 4 cut 1024 498)/2 = (16925867:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16925867:ℝ)/4218880) = (33971200:ℝ)/21360809 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16925867:ℝ)/4218880)-4 = (50347:ℝ)/4218880 by norm_num]
    exact paid_middle_497
  · change middlePayment 498 ≤ middleValue ((point 4 cut 1024 498+point 4 cut 1024 499)/2)
    have hp : middlePayment 498 = (645092060557:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 498+point 4 cut 1024 499)/2 = (84629841:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84629841:ℝ)/21094400) = (33971200:ℝ)/21360303 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84629841:ℝ)/21094400)-4 = (252241:ℝ)/21094400 by norm_num]
    exact paid_middle_498
  · change middlePayment 499 ≤ middleValue ((point 4 cut 1024 499+point 4 cut 1024 500)/2)
    have hp : middlePayment 499 = (645131698994:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 499+point 4 cut 1024 500)/2 = (84630347:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84630347:ℝ)/21094400) = (33971200:ℝ)/21359797 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84630347:ℝ)/21094400)-4 = (252747:ℝ)/21094400 by norm_num]
    exact paid_middle_499
  · change middlePayment 500 ≤ middleValue ((point 4 cut 1024 500+point 4 cut 1024 501)/2)
    have hp : middlePayment 500 = (645171338973:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 500+point 4 cut 1024 501)/2 = (84630853:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84630853:ℝ)/21094400) = (33971200:ℝ)/21359291 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84630853:ℝ)/21094400)-4 = (253253:ℝ)/21094400 by norm_num]
    exact paid_middle_500
  · change middlePayment 501 ≤ middleValue ((point 4 cut 1024 501+point 4 cut 1024 502)/2)
    have hp : middlePayment 501 = (645210980493:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 501+point 4 cut 1024 502)/2 = (84631359:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84631359:ℝ)/21094400) = (6794240:ℝ)/4271757 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84631359:ℝ)/21094400)-4 = (253759:ℝ)/21094400 by norm_num]
    exact paid_middle_501
  · change middlePayment 502 ≤ middleValue ((point 4 cut 1024 502+point 4 cut 1024 503)/2)
    have hp : middlePayment 502 = (645250623554:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 502+point 4 cut 1024 503)/2 = (16926373:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16926373:ℝ)/4218880) = (33971200:ℝ)/21358279 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16926373:ℝ)/4218880)-4 = (50853:ℝ)/4218880 by norm_num]
    exact paid_middle_502
  · change middlePayment 503 ≤ middleValue ((point 4 cut 1024 503+point 4 cut 1024 504)/2)
    have hp : middlePayment 503 = (645290268157:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 503+point 4 cut 1024 504)/2 = (84632371:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84632371:ℝ)/21094400) = (33971200:ℝ)/21357773 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84632371:ℝ)/21094400)-4 = (254771:ℝ)/21094400 by norm_num]
    exact paid_middle_503
  · change middlePayment 504 ≤ middleValue ((point 4 cut 1024 504+point 4 cut 1024 505)/2)
    have hp : middlePayment 504 = (645329914301:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 504+point 4 cut 1024 505)/2 = (84632877:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84632877:ℝ)/21094400) = (33971200:ℝ)/21357267 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84632877:ℝ)/21094400)-4 = (255277:ℝ)/21094400 by norm_num]
    exact paid_middle_504
  · change middlePayment 505 ≤ middleValue ((point 4 cut 1024 505+point 4 cut 1024 506)/2)
    have hp : middlePayment 505 = (645369561987:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 505+point 4 cut 1024 506)/2 = (84633383:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84633383:ℝ)/21094400) = (33971200:ℝ)/21356761 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84633383:ℝ)/21094400)-4 = (255783:ℝ)/21094400 by norm_num]
    exact paid_middle_505
  · change middlePayment 506 ≤ middleValue ((point 4 cut 1024 506+point 4 cut 1024 507)/2)
    have hp : middlePayment 506 = (645409211214:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 506+point 4 cut 1024 507)/2 = (84633889:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84633889:ℝ)/21094400) = (6794240:ℝ)/4271251 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84633889:ℝ)/21094400)-4 = (256289:ℝ)/21094400 by norm_num]
    exact paid_middle_506
  · change middlePayment 507 ≤ middleValue ((point 4 cut 1024 507+point 4 cut 1024 508)/2)
    have hp : middlePayment 507 = (645448861983:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 507+point 4 cut 1024 508)/2 = (16926879:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16926879:ℝ)/4218880) = (33971200:ℝ)/21355749 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16926879:ℝ)/4218880)-4 = (51359:ℝ)/4218880 by norm_num]
    exact paid_middle_507
  · change middlePayment 508 ≤ middleValue ((point 4 cut 1024 508+point 4 cut 1024 509)/2)
    have hp : middlePayment 508 = (645488514294:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 508+point 4 cut 1024 509)/2 = (84634901:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84634901:ℝ)/21094400) = (33971200:ℝ)/21355243 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84634901:ℝ)/21094400)-4 = (257301:ℝ)/21094400 by norm_num]
    exact paid_middle_508
  · change middlePayment 509 ≤ middleValue ((point 4 cut 1024 509+point 4 cut 1024 510)/2)
    have hp : middlePayment 509 = (645528168147:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 509+point 4 cut 1024 510)/2 = (84635407:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84635407:ℝ)/21094400) = (33971200:ℝ)/21354737 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84635407:ℝ)/21094400)-4 = (257807:ℝ)/21094400 by norm_num]
    exact paid_middle_509
  · change middlePayment 510 ≤ middleValue ((point 4 cut 1024 510+point 4 cut 1024 511)/2)
    have hp : middlePayment 510 = (645567823541:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 510+point 4 cut 1024 511)/2 = (84635913:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84635913:ℝ)/21094400) = (33971200:ℝ)/21354231 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84635913:ℝ)/21094400)-4 = (258313:ℝ)/21094400 by norm_num]
    exact paid_middle_510
  · change middlePayment 511 ≤ middleValue ((point 4 cut 1024 511+point 4 cut 1024 512)/2)
    have hp : middlePayment 511 = (645607480478:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 511+point 4 cut 1024 512)/2 = (84636419:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84636419:ℝ)/21094400) = (1358848:ℝ)/854149 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84636419:ℝ)/21094400)-4 = (258819:ℝ)/21094400 by norm_num]
    exact paid_middle_511
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_031
