import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints053
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_053 (j : Fin 16) : middlePayment (16*53+j.val) ≤
    middleValue ((point 4 cut 1024 (16*53+j.val)+point 4 cut 1024 (16*53+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 848 ≤ middleValue ((point 4 cut 1024 848+point 4 cut 1024 849)/2)
    have hp : middlePayment 848 = (659060195230:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 848+point 4 cut 1024 849)/2 = (84806941:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84806941:ℝ)/21094400) = (33971200:ℝ)/21183203 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84806941:ℝ)/21094400)-4 = (429341:ℝ)/21094400 by norm_num]
    exact paid_middle_848
  · change middlePayment 849 ≤ middleValue ((point 4 cut 1024 849+point 4 cut 1024 850)/2)
    have hp : middlePayment 849 = (659100377870:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 849+point 4 cut 1024 850)/2 = (84807447:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84807447:ℝ)/21094400) = (33971200:ℝ)/21182697 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84807447:ℝ)/21094400)-4 = (429847:ℝ)/21094400 by norm_num]
    exact paid_middle_849
  · change middlePayment 850 ≤ middleValue ((point 4 cut 1024 850+point 4 cut 1024 851)/2)
    have hp : middlePayment 850 = (659140562078:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 850+point 4 cut 1024 851)/2 = (84807953:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84807953:ℝ)/21094400) = (33971200:ℝ)/21182191 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84807953:ℝ)/21094400)-4 = (430353:ℝ)/21094400 by norm_num]
    exact paid_middle_850
  · change middlePayment 851 ≤ middleValue ((point 4 cut 1024 851+point 4 cut 1024 852)/2)
    have hp : middlePayment 851 = (659180747854:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 851+point 4 cut 1024 852)/2 = (84808459:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84808459:ℝ)/21094400) = (6794240:ℝ)/4236337 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84808459:ℝ)/21094400)-4 = (430859:ℝ)/21094400 by norm_num]
    exact paid_middle_851
  · change middlePayment 852 ≤ middleValue ((point 4 cut 1024 852+point 4 cut 1024 853)/2)
    have hp : middlePayment 852 = (659220935200:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 852+point 4 cut 1024 853)/2 = (16961793:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16961793:ℝ)/4218880) = (33971200:ℝ)/21181179 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16961793:ℝ)/4218880)-4 = (86273:ℝ)/4218880 by norm_num]
    exact paid_middle_852
  · change middlePayment 853 ≤ middleValue ((point 4 cut 1024 853+point 4 cut 1024 854)/2)
    have hp : middlePayment 853 = (659261124115:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 853+point 4 cut 1024 854)/2 = (84809471:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84809471:ℝ)/21094400) = (33971200:ℝ)/21180673 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84809471:ℝ)/21094400)-4 = (431871:ℝ)/21094400 by norm_num]
    exact paid_middle_853
  · change middlePayment 854 ≤ middleValue ((point 4 cut 1024 854+point 4 cut 1024 855)/2)
    have hp : middlePayment 854 = (659301314598:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 854+point 4 cut 1024 855)/2 = (84809977:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84809977:ℝ)/21094400) = (33971200:ℝ)/21180167 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84809977:ℝ)/21094400)-4 = (432377:ℝ)/21094400 by norm_num]
    exact paid_middle_854
  · change middlePayment 855 ≤ middleValue ((point 4 cut 1024 855+point 4 cut 1024 856)/2)
    have hp : middlePayment 855 = (659341506651:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 855+point 4 cut 1024 856)/2 = (84810483:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84810483:ℝ)/21094400) = (33971200:ℝ)/21179661 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84810483:ℝ)/21094400)-4 = (432883:ℝ)/21094400 by norm_num]
    exact paid_middle_855
  · change middlePayment 856 ≤ middleValue ((point 4 cut 1024 856+point 4 cut 1024 857)/2)
    have hp : middlePayment 856 = (659381700274:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 856+point 4 cut 1024 857)/2 = (84810989:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84810989:ℝ)/21094400) = (6794240:ℝ)/4235831 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84810989:ℝ)/21094400)-4 = (433389:ℝ)/21094400 by norm_num]
    exact paid_middle_856
  · change middlePayment 857 ≤ middleValue ((point 4 cut 1024 857+point 4 cut 1024 858)/2)
    have hp : middlePayment 857 = (659421895465:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 857+point 4 cut 1024 858)/2 = (16962299:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16962299:ℝ)/4218880) = (33971200:ℝ)/21178649 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16962299:ℝ)/4218880)-4 = (86779:ℝ)/4218880 by norm_num]
    exact paid_middle_857
  · change middlePayment 858 ≤ middleValue ((point 4 cut 1024 858+point 4 cut 1024 859)/2)
    have hp : middlePayment 858 = (659462092226:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 858+point 4 cut 1024 859)/2 = (84812001:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84812001:ℝ)/21094400) = (33971200:ℝ)/21178143 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84812001:ℝ)/21094400)-4 = (434401:ℝ)/21094400 by norm_num]
    exact paid_middle_858
  · change middlePayment 859 ≤ middleValue ((point 4 cut 1024 859+point 4 cut 1024 860)/2)
    have hp : middlePayment 859 = (659502290556:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 859+point 4 cut 1024 860)/2 = (84812507:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84812507:ℝ)/21094400) = (33971200:ℝ)/21177637 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84812507:ℝ)/21094400)-4 = (434907:ℝ)/21094400 by norm_num]
    exact paid_middle_859
  · change middlePayment 860 ≤ middleValue ((point 4 cut 1024 860+point 4 cut 1024 861)/2)
    have hp : middlePayment 860 = (659542490456:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 860+point 4 cut 1024 861)/2 = (84813013:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84813013:ℝ)/21094400) = (33971200:ℝ)/21177131 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84813013:ℝ)/21094400)-4 = (435413:ℝ)/21094400 by norm_num]
    exact paid_middle_860
  · change middlePayment 861 ≤ middleValue ((point 4 cut 1024 861+point 4 cut 1024 862)/2)
    have hp : middlePayment 861 = (659582691926:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 861+point 4 cut 1024 862)/2 = (84813519:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84813519:ℝ)/21094400) = (1358848:ℝ)/847065 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84813519:ℝ)/21094400)-4 = (435919:ℝ)/21094400 by norm_num]
    exact paid_middle_861
  · change middlePayment 862 ≤ middleValue ((point 4 cut 1024 862+point 4 cut 1024 863)/2)
    have hp : middlePayment 862 = (659622894965:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 862+point 4 cut 1024 863)/2 = (3392561:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3392561:ℝ)/843776) = (33971200:ℝ)/21176119 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3392561:ℝ)/843776)-4 = (17457:ℝ)/843776 by norm_num]
    exact paid_middle_862
  · change middlePayment 863 ≤ middleValue ((point 4 cut 1024 863+point 4 cut 1024 864)/2)
    have hp : middlePayment 863 = (659663099574:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 863+point 4 cut 1024 864)/2 = (84814531:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84814531:ℝ)/21094400) = (33971200:ℝ)/21175613 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84814531:ℝ)/21094400)-4 = (436931:ℝ)/21094400 by norm_num]
    exact paid_middle_863
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_053
