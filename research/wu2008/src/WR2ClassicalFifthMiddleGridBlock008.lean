import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints008
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_008 (j : Fin 16) : middlePayment (16*8+j.val) ≤
    middleValue ((point 4 cut 1024 (16*8+j.val)+point 4 cut 1024 (16*8+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 128 ≤ middleValue ((point 4 cut 1024 128+point 4 cut 1024 129)/2)
    have hp : middlePayment 128 = (630530958650:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 128+point 4 cut 1024 129)/2 = (84442621:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84442621:ℝ)/21094400) = (33971200:ℝ)/21547523 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84442621:ℝ)/21094400)-4 = (65021:ℝ)/21094400 by norm_num]
    exact paid_middle_128
  · change middlePayment 129 ≤ middleValue ((point 4 cut 1024 129+point 4 cut 1024 130)/2)
    have hp : middlePayment 129 = (630570032150:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 129+point 4 cut 1024 130)/2 = (84443127:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84443127:ℝ)/21094400) = (33971200:ℝ)/21547017 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84443127:ℝ)/21094400)-4 = (65527:ℝ)/21094400 by norm_num]
    exact paid_middle_129
  · change middlePayment 130 ≤ middleValue ((point 4 cut 1024 130+point 4 cut 1024 131)/2)
    have hp : middlePayment 130 = (630609107163:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 130+point 4 cut 1024 131)/2 = (84443633:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84443633:ℝ)/21094400) = (33971200:ℝ)/21546511 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84443633:ℝ)/21094400)-4 = (66033:ℝ)/21094400 by norm_num]
    exact paid_middle_130
  · change middlePayment 131 ≤ middleValue ((point 4 cut 1024 131+point 4 cut 1024 132)/2)
    have hp : middlePayment 131 = (630648183689:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 131+point 4 cut 1024 132)/2 = (84444139:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84444139:ℝ)/21094400) = (6794240:ℝ)/4309201 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84444139:ℝ)/21094400)-4 = (66539:ℝ)/21094400 by norm_num]
    exact paid_middle_131
  · change middlePayment 132 ≤ middleValue ((point 4 cut 1024 132+point 4 cut 1024 133)/2)
    have hp : middlePayment 132 = (630687261727:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 132+point 4 cut 1024 133)/2 = (16888929:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16888929:ℝ)/4218880) = (33971200:ℝ)/21545499 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16888929:ℝ)/4218880)-4 = (13409:ℝ)/4218880 by norm_num]
    exact paid_middle_132
  · change middlePayment 133 ≤ middleValue ((point 4 cut 1024 133+point 4 cut 1024 134)/2)
    have hp : middlePayment 133 = (630726341279:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 133+point 4 cut 1024 134)/2 = (84445151:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84445151:ℝ)/21094400) = (33971200:ℝ)/21544993 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84445151:ℝ)/21094400)-4 = (67551:ℝ)/21094400 by norm_num]
    exact paid_middle_133
  · change middlePayment 134 ≤ middleValue ((point 4 cut 1024 134+point 4 cut 1024 135)/2)
    have hp : middlePayment 134 = (630765422344:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 134+point 4 cut 1024 135)/2 = (84445657:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84445657:ℝ)/21094400) = (33971200:ℝ)/21544487 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84445657:ℝ)/21094400)-4 = (68057:ℝ)/21094400 by norm_num]
    exact paid_middle_134
  · change middlePayment 135 ≤ middleValue ((point 4 cut 1024 135+point 4 cut 1024 136)/2)
    have hp : middlePayment 135 = (630804504921:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 135+point 4 cut 1024 136)/2 = (84446163:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84446163:ℝ)/21094400) = (33971200:ℝ)/21543981 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84446163:ℝ)/21094400)-4 = (68563:ℝ)/21094400 by norm_num]
    exact paid_middle_135
  · change middlePayment 136 ≤ middleValue ((point 4 cut 1024 136+point 4 cut 1024 137)/2)
    have hp : middlePayment 136 = (630843589012:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 136+point 4 cut 1024 137)/2 = (84446669:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84446669:ℝ)/21094400) = (1358848:ℝ)/861739 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84446669:ℝ)/21094400)-4 = (69069:ℝ)/21094400 by norm_num]
    exact paid_middle_136
  · change middlePayment 137 ≤ middleValue ((point 4 cut 1024 137+point 4 cut 1024 138)/2)
    have hp : middlePayment 137 = (630882674617:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 137+point 4 cut 1024 138)/2 = (3377887:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3377887:ℝ)/843776) = (33971200:ℝ)/21542969 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3377887:ℝ)/843776)-4 = (2783:ℝ)/843776 by norm_num]
    exact paid_middle_137
  · change middlePayment 138 ≤ middleValue ((point 4 cut 1024 138+point 4 cut 1024 139)/2)
    have hp : middlePayment 138 = (630921761734:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 138+point 4 cut 1024 139)/2 = (84447681:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84447681:ℝ)/21094400) = (33971200:ℝ)/21542463 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84447681:ℝ)/21094400)-4 = (70081:ℝ)/21094400 by norm_num]
    exact paid_middle_138
  · change middlePayment 139 ≤ middleValue ((point 4 cut 1024 139+point 4 cut 1024 140)/2)
    have hp : middlePayment 139 = (630960850365:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 139+point 4 cut 1024 140)/2 = (84448187:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84448187:ℝ)/21094400) = (33971200:ℝ)/21541957 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84448187:ℝ)/21094400)-4 = (70587:ℝ)/21094400 by norm_num]
    exact paid_middle_139
  · change middlePayment 140 ≤ middleValue ((point 4 cut 1024 140+point 4 cut 1024 141)/2)
    have hp : middlePayment 140 = (630999940510:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 140+point 4 cut 1024 141)/2 = (84448693:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84448693:ℝ)/21094400) = (33971200:ℝ)/21541451 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84448693:ℝ)/21094400)-4 = (71093:ℝ)/21094400 by norm_num]
    exact paid_middle_140
  · change middlePayment 141 ≤ middleValue ((point 4 cut 1024 141+point 4 cut 1024 142)/2)
    have hp : middlePayment 141 = (631039032168:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 141+point 4 cut 1024 142)/2 = (84449199:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84449199:ℝ)/21094400) = (6794240:ℝ)/4308189 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84449199:ℝ)/21094400)-4 = (71599:ℝ)/21094400 by norm_num]
    exact paid_middle_141
  · change middlePayment 142 ≤ middleValue ((point 4 cut 1024 142+point 4 cut 1024 143)/2)
    have hp : middlePayment 142 = (631078125340:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 142+point 4 cut 1024 143)/2 = (16889941:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16889941:ℝ)/4218880) = (33971200:ℝ)/21540439 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16889941:ℝ)/4218880)-4 = (14421:ℝ)/4218880 by norm_num]
    exact paid_middle_142
  · change middlePayment 143 ≤ middleValue ((point 4 cut 1024 143+point 4 cut 1024 144)/2)
    have hp : middlePayment 143 = (631117220025:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 143+point 4 cut 1024 144)/2 = (84450211:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84450211:ℝ)/21094400) = (33971200:ℝ)/21539933 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84450211:ℝ)/21094400)-4 = (72611:ℝ)/21094400 by norm_num]
    exact paid_middle_143
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_008
