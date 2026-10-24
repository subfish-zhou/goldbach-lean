import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints045
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_045 (j : Fin 16) : middlePayment (16*45+j.val) ≤
    middleValue ((point 4 cut 1024 (16*45+j.val)+point 4 cut 1024 (16*45+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 720 ≤ middleValue ((point 4 cut 1024 720+point 4 cut 1024 721)/2)
    have hp : middlePayment 720 = (653929740567:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 720+point 4 cut 1024 721)/2 = (84742173:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84742173:ℝ)/21094400) = (33971200:ℝ)/21247971 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84742173:ℝ)/21094400)-4 = (364573:ℝ)/21094400 by norm_num]
    exact paid_middle_720
  · change middlePayment 721 ≤ middleValue ((point 4 cut 1024 721+point 4 cut 1024 722)/2)
    have hp : middlePayment 721 = (653969723062:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 721+point 4 cut 1024 722)/2 = (84742679:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84742679:ℝ)/21094400) = (6794240:ℝ)/4249493 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84742679:ℝ)/21094400)-4 = (365079:ℝ)/21094400 by norm_num]
    exact paid_middle_721
  · change middlePayment 722 ≤ middleValue ((point 4 cut 1024 722+point 4 cut 1024 723)/2)
    have hp : middlePayment 722 = (654009707117:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 722+point 4 cut 1024 723)/2 = (16948637:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16948637:ℝ)/4218880) = (33971200:ℝ)/21246959 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16948637:ℝ)/4218880)-4 = (73117:ℝ)/4218880 by norm_num]
    exact paid_middle_722
  · change middlePayment 723 ≤ middleValue ((point 4 cut 1024 723+point 4 cut 1024 724)/2)
    have hp : middlePayment 723 = (654049692729:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 723+point 4 cut 1024 724)/2 = (84743691:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84743691:ℝ)/21094400) = (33971200:ℝ)/21246453 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84743691:ℝ)/21094400)-4 = (366091:ℝ)/21094400 by norm_num]
    exact paid_middle_723
  · change middlePayment 724 ≤ middleValue ((point 4 cut 1024 724+point 4 cut 1024 725)/2)
    have hp : middlePayment 724 = (654089679901:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 724+point 4 cut 1024 725)/2 = (84744197:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84744197:ℝ)/21094400) = (33971200:ℝ)/21245947 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84744197:ℝ)/21094400)-4 = (366597:ℝ)/21094400 by norm_num]
    exact paid_middle_724
  · change middlePayment 725 ≤ middleValue ((point 4 cut 1024 725+point 4 cut 1024 726)/2)
    have hp : middlePayment 725 = (654129668631:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 725+point 4 cut 1024 726)/2 = (84744703:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84744703:ℝ)/21094400) = (33971200:ℝ)/21245441 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84744703:ℝ)/21094400)-4 = (367103:ℝ)/21094400 by norm_num]
    exact paid_middle_725
  · change middlePayment 726 ≤ middleValue ((point 4 cut 1024 726+point 4 cut 1024 727)/2)
    have hp : middlePayment 726 = (654169658921:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 726+point 4 cut 1024 727)/2 = (84745209:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84745209:ℝ)/21094400) = (6794240:ℝ)/4248987 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84745209:ℝ)/21094400)-4 = (367609:ℝ)/21094400 by norm_num]
    exact paid_middle_726
  · change middlePayment 727 ≤ middleValue ((point 4 cut 1024 727+point 4 cut 1024 728)/2)
    have hp : middlePayment 727 = (654209650769:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 727+point 4 cut 1024 728)/2 = (16949143:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16949143:ℝ)/4218880) = (33971200:ℝ)/21244429 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16949143:ℝ)/4218880)-4 = (73623:ℝ)/4218880 by norm_num]
    exact paid_middle_727
  · change middlePayment 728 ≤ middleValue ((point 4 cut 1024 728+point 4 cut 1024 729)/2)
    have hp : middlePayment 728 = (654249644176:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 728+point 4 cut 1024 729)/2 = (84746221:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84746221:ℝ)/21094400) = (33971200:ℝ)/21243923 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84746221:ℝ)/21094400)-4 = (368621:ℝ)/21094400 by norm_num]
    exact paid_middle_728
  · change middlePayment 729 ≤ middleValue ((point 4 cut 1024 729+point 4 cut 1024 730)/2)
    have hp : middlePayment 729 = (654289639143:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 729+point 4 cut 1024 730)/2 = (84746727:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84746727:ℝ)/21094400) = (33971200:ℝ)/21243417 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84746727:ℝ)/21094400)-4 = (369127:ℝ)/21094400 by norm_num]
    exact paid_middle_729
  · change middlePayment 730 ≤ middleValue ((point 4 cut 1024 730+point 4 cut 1024 731)/2)
    have hp : middlePayment 730 = (654329635668:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 730+point 4 cut 1024 731)/2 = (84747233:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84747233:ℝ)/21094400) = (33971200:ℝ)/21242911 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84747233:ℝ)/21094400)-4 = (369633:ℝ)/21094400 by norm_num]
    exact paid_middle_730
  · change middlePayment 731 ≤ middleValue ((point 4 cut 1024 731+point 4 cut 1024 732)/2)
    have hp : middlePayment 731 = (654369633753:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 731+point 4 cut 1024 732)/2 = (84747739:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84747739:ℝ)/21094400) = (6794240:ℝ)/4248481 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84747739:ℝ)/21094400)-4 = (370139:ℝ)/21094400 by norm_num]
    exact paid_middle_731
  · change middlePayment 732 ≤ middleValue ((point 4 cut 1024 732+point 4 cut 1024 733)/2)
    have hp : middlePayment 732 = (654409633398:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 732+point 4 cut 1024 733)/2 = (16949649:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16949649:ℝ)/4218880) = (33971200:ℝ)/21241899 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16949649:ℝ)/4218880)-4 = (74129:ℝ)/4218880 by norm_num]
    exact paid_middle_732
  · change middlePayment 733 ≤ middleValue ((point 4 cut 1024 733+point 4 cut 1024 734)/2)
    have hp : middlePayment 733 = (654449634601:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 733+point 4 cut 1024 734)/2 = (84748751:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84748751:ℝ)/21094400) = (33971200:ℝ)/21241393 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84748751:ℝ)/21094400)-4 = (371151:ℝ)/21094400 by norm_num]
    exact paid_middle_733
  · change middlePayment 734 ≤ middleValue ((point 4 cut 1024 734+point 4 cut 1024 735)/2)
    have hp : middlePayment 734 = (654489637365:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 734+point 4 cut 1024 735)/2 = (84749257:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84749257:ℝ)/21094400) = (33971200:ℝ)/21240887 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84749257:ℝ)/21094400)-4 = (371657:ℝ)/21094400 by norm_num]
    exact paid_middle_734
  · change middlePayment 735 ≤ middleValue ((point 4 cut 1024 735+point 4 cut 1024 736)/2)
    have hp : middlePayment 735 = (654529641688:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 735+point 4 cut 1024 736)/2 = (84749763:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84749763:ℝ)/21094400) = (33971200:ℝ)/21240381 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84749763:ℝ)/21094400)-4 = (372163:ℝ)/21094400 by norm_num]
    exact paid_middle_735
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_045
