import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints044
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_044 (j : Fin 16) : middlePayment (16*44+j.val) ≤
    middleValue ((point 4 cut 1024 (16*44+j.val)+point 4 cut 1024 (16*44+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 704 ≤ middleValue ((point 4 cut 1024 704+point 4 cut 1024 705)/2)
    have hp : middlePayment 704 = (653290232541:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 704+point 4 cut 1024 705)/2 = (84734077:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84734077:ℝ)/21094400) = (33971200:ℝ)/21256067 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84734077:ℝ)/21094400)-4 = (356477:ℝ)/21094400 by norm_num]
    exact paid_middle_704
  · change middlePayment 705 ≤ middleValue ((point 4 cut 1024 705+point 4 cut 1024 706)/2)
    have hp : middlePayment 705 = (653330190110:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 705+point 4 cut 1024 706)/2 = (84734583:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84734583:ℝ)/21094400) = (33971200:ℝ)/21255561 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84734583:ℝ)/21094400)-4 = (356983:ℝ)/21094400 by norm_num]
    exact paid_middle_705
  · change middlePayment 706 ≤ middleValue ((point 4 cut 1024 706+point 4 cut 1024 707)/2)
    have hp : middlePayment 706 = (653370149236:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 706+point 4 cut 1024 707)/2 = (84735089:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84735089:ℝ)/21094400) = (6794240:ℝ)/4251011 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84735089:ℝ)/21094400)-4 = (357489:ℝ)/21094400 by norm_num]
    exact paid_middle_706
  · change middlePayment 707 ≤ middleValue ((point 4 cut 1024 707+point 4 cut 1024 708)/2)
    have hp : middlePayment 707 = (653410109920:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 707+point 4 cut 1024 708)/2 = (16947119:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16947119:ℝ)/4218880) = (33971200:ℝ)/21254549 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16947119:ℝ)/4218880)-4 = (71599:ℝ)/4218880 by norm_num]
    exact paid_middle_707
  · change middlePayment 708 ≤ middleValue ((point 4 cut 1024 708+point 4 cut 1024 709)/2)
    have hp : middlePayment 708 = (653450072161:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 708+point 4 cut 1024 709)/2 = (84736101:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84736101:ℝ)/21094400) = (33971200:ℝ)/21254043 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84736101:ℝ)/21094400)-4 = (358501:ℝ)/21094400 by norm_num]
    exact paid_middle_708
  · change middlePayment 709 ≤ middleValue ((point 4 cut 1024 709+point 4 cut 1024 710)/2)
    have hp : middlePayment 709 = (653490035959:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 709+point 4 cut 1024 710)/2 = (84736607:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84736607:ℝ)/21094400) = (33971200:ℝ)/21253537 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84736607:ℝ)/21094400)-4 = (359007:ℝ)/21094400 by norm_num]
    exact paid_middle_709
  · change middlePayment 710 ≤ middleValue ((point 4 cut 1024 710+point 4 cut 1024 711)/2)
    have hp : middlePayment 710 = (653530001316:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 710+point 4 cut 1024 711)/2 = (84737113:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84737113:ℝ)/21094400) = (33971200:ℝ)/21253031 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84737113:ℝ)/21094400)-4 = (359513:ℝ)/21094400 by norm_num]
    exact paid_middle_710
  · change middlePayment 711 ≤ middleValue ((point 4 cut 1024 711+point 4 cut 1024 712)/2)
    have hp : middlePayment 711 = (653569968230:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 711+point 4 cut 1024 712)/2 = (84737619:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84737619:ℝ)/21094400) = (1358848:ℝ)/850101 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84737619:ℝ)/21094400)-4 = (360019:ℝ)/21094400 by norm_num]
    exact paid_middle_711
  · change middlePayment 712 ≤ middleValue ((point 4 cut 1024 712+point 4 cut 1024 713)/2)
    have hp : middlePayment 712 = (653609936702:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 712+point 4 cut 1024 713)/2 = (3389525:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3389525:ℝ)/843776) = (33971200:ℝ)/21252019 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3389525:ℝ)/843776)-4 = (14421:ℝ)/843776 by norm_num]
    exact paid_middle_712
  · change middlePayment 713 ≤ middleValue ((point 4 cut 1024 713+point 4 cut 1024 714)/2)
    have hp : middlePayment 713 = (653649906732:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 713+point 4 cut 1024 714)/2 = (84738631:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84738631:ℝ)/21094400) = (33971200:ℝ)/21251513 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84738631:ℝ)/21094400)-4 = (361031:ℝ)/21094400 by norm_num]
    exact paid_middle_713
  · change middlePayment 714 ≤ middleValue ((point 4 cut 1024 714+point 4 cut 1024 715)/2)
    have hp : middlePayment 714 = (653689878319:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 714+point 4 cut 1024 715)/2 = (84739137:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84739137:ℝ)/21094400) = (33971200:ℝ)/21251007 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84739137:ℝ)/21094400)-4 = (361537:ℝ)/21094400 by norm_num]
    exact paid_middle_714
  · change middlePayment 715 ≤ middleValue ((point 4 cut 1024 715+point 4 cut 1024 716)/2)
    have hp : middlePayment 715 = (653729851465:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 715+point 4 cut 1024 716)/2 = (84739643:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84739643:ℝ)/21094400) = (33971200:ℝ)/21250501 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84739643:ℝ)/21094400)-4 = (362043:ℝ)/21094400 by norm_num]
    exact paid_middle_715
  · change middlePayment 716 ≤ middleValue ((point 4 cut 1024 716+point 4 cut 1024 717)/2)
    have hp : middlePayment 716 = (653769826169:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 716+point 4 cut 1024 717)/2 = (84740149:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84740149:ℝ)/21094400) = (6794240:ℝ)/4249999 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84740149:ℝ)/21094400)-4 = (362549:ℝ)/21094400 by norm_num]
    exact paid_middle_716
  · change middlePayment 717 ≤ middleValue ((point 4 cut 1024 717+point 4 cut 1024 718)/2)
    have hp : middlePayment 717 = (653809802431:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 717+point 4 cut 1024 718)/2 = (16948131:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16948131:ℝ)/4218880) = (33971200:ℝ)/21249489 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16948131:ℝ)/4218880)-4 = (72611:ℝ)/4218880 by norm_num]
    exact paid_middle_717
  · change middlePayment 718 ≤ middleValue ((point 4 cut 1024 718+point 4 cut 1024 719)/2)
    have hp : middlePayment 718 = (653849780251:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 718+point 4 cut 1024 719)/2 = (84741161:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84741161:ℝ)/21094400) = (33971200:ℝ)/21248983 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84741161:ℝ)/21094400)-4 = (363561:ℝ)/21094400 by norm_num]
    exact paid_middle_718
  · change middlePayment 719 ≤ middleValue ((point 4 cut 1024 719+point 4 cut 1024 720)/2)
    have hp : middlePayment 719 = (653889759630:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 719+point 4 cut 1024 720)/2 = (84741667:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84741667:ℝ)/21094400) = (33971200:ℝ)/21248477 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84741667:ℝ)/21094400)-4 = (364067:ℝ)/21094400 by norm_num]
    exact paid_middle_719
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_044
