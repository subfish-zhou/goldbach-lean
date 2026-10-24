import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints058
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_058 (j : Fin 16) : middlePayment (16*58+j.val) ≤
    middleValue ((point 4 cut 1024 (16*58+j.val)+point 4 cut 1024 (16*58+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 928 ≤ middleValue ((point 4 cut 1024 928+point 4 cut 1024 929)/2)
    have hp : middlePayment 928 = (662279770205:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 928+point 4 cut 1024 929)/2 = (84847421:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84847421:ℝ)/21094400) = (33971200:ℝ)/21142723 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84847421:ℝ)/21094400)-4 = (469821:ℝ)/21094400 by norm_num]
    exact paid_middle_928
  · change middlePayment 929 ≤ middleValue ((point 4 cut 1024 929+point 4 cut 1024 930)/2)
    have hp : middlePayment 929 = (662320078597:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 929+point 4 cut 1024 930)/2 = (84847927:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84847927:ℝ)/21094400) = (33971200:ℝ)/21142217 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84847927:ℝ)/21094400)-4 = (470327:ℝ)/21094400 by norm_num]
    exact paid_middle_929
  · change middlePayment 930 ≤ middleValue ((point 4 cut 1024 930+point 4 cut 1024 931)/2)
    have hp : middlePayment 930 = (662360388565:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 930+point 4 cut 1024 931)/2 = (84848433:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84848433:ℝ)/21094400) = (33971200:ℝ)/21141711 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84848433:ℝ)/21094400)-4 = (470833:ℝ)/21094400 by norm_num]
    exact paid_middle_930
  · change middlePayment 931 ≤ middleValue ((point 4 cut 1024 931+point 4 cut 1024 932)/2)
    have hp : middlePayment 931 = (662400700108:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 931+point 4 cut 1024 932)/2 = (84848939:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84848939:ℝ)/21094400) = (6794240:ℝ)/4228241 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84848939:ℝ)/21094400)-4 = (471339:ℝ)/21094400 by norm_num]
    exact paid_middle_931
  · change middlePayment 932 ≤ middleValue ((point 4 cut 1024 932+point 4 cut 1024 933)/2)
    have hp : middlePayment 932 = (662441013226:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 932+point 4 cut 1024 933)/2 = (16969889:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16969889:ℝ)/4218880) = (33971200:ℝ)/21140699 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16969889:ℝ)/4218880)-4 = (94369:ℝ)/4218880 by norm_num]
    exact paid_middle_932
  · change middlePayment 933 ≤ middleValue ((point 4 cut 1024 933+point 4 cut 1024 934)/2)
    have hp : middlePayment 933 = (662481327920:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 933+point 4 cut 1024 934)/2 = (84849951:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84849951:ℝ)/21094400) = (33971200:ℝ)/21140193 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84849951:ℝ)/21094400)-4 = (472351:ℝ)/21094400 by norm_num]
    exact paid_middle_933
  · change middlePayment 934 ≤ middleValue ((point 4 cut 1024 934+point 4 cut 1024 935)/2)
    have hp : middlePayment 934 = (662521644189:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 934+point 4 cut 1024 935)/2 = (84850457:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84850457:ℝ)/21094400) = (33971200:ℝ)/21139687 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84850457:ℝ)/21094400)-4 = (472857:ℝ)/21094400 by norm_num]
    exact paid_middle_934
  · change middlePayment 935 ≤ middleValue ((point 4 cut 1024 935+point 4 cut 1024 936)/2)
    have hp : middlePayment 935 = (662561962033:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 935+point 4 cut 1024 936)/2 = (84850963:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84850963:ℝ)/21094400) = (33971200:ℝ)/21139181 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84850963:ℝ)/21094400)-4 = (473363:ℝ)/21094400 by norm_num]
    exact paid_middle_935
  · change middlePayment 936 ≤ middleValue ((point 4 cut 1024 936+point 4 cut 1024 937)/2)
    have hp : middlePayment 936 = (662602281454:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 936+point 4 cut 1024 937)/2 = (84851469:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84851469:ℝ)/21094400) = (1358848:ℝ)/845547 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84851469:ℝ)/21094400)-4 = (473869:ℝ)/21094400 by norm_num]
    exact paid_middle_936
  · change middlePayment 937 ≤ middleValue ((point 4 cut 1024 937+point 4 cut 1024 938)/2)
    have hp : middlePayment 937 = (662642602450:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 937+point 4 cut 1024 938)/2 = (3394079:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3394079:ℝ)/843776) = (33971200:ℝ)/21138169 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3394079:ℝ)/843776)-4 = (18975:ℝ)/843776 by norm_num]
    exact paid_middle_937
  · change middlePayment 938 ≤ middleValue ((point 4 cut 1024 938+point 4 cut 1024 939)/2)
    have hp : middlePayment 938 = (662682925022:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 938+point 4 cut 1024 939)/2 = (84852481:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84852481:ℝ)/21094400) = (33971200:ℝ)/21137663 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84852481:ℝ)/21094400)-4 = (474881:ℝ)/21094400 by norm_num]
    exact paid_middle_938
  · change middlePayment 939 ≤ middleValue ((point 4 cut 1024 939+point 4 cut 1024 940)/2)
    have hp : middlePayment 939 = (662723249169:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 939+point 4 cut 1024 940)/2 = (84852987:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84852987:ℝ)/21094400) = (33971200:ℝ)/21137157 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84852987:ℝ)/21094400)-4 = (475387:ℝ)/21094400 by norm_num]
    exact paid_middle_939
  · change middlePayment 940 ≤ middleValue ((point 4 cut 1024 940+point 4 cut 1024 941)/2)
    have hp : middlePayment 940 = (662763574893:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 940+point 4 cut 1024 941)/2 = (84853493:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84853493:ℝ)/21094400) = (33971200:ℝ)/21136651 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84853493:ℝ)/21094400)-4 = (475893:ℝ)/21094400 by norm_num]
    exact paid_middle_940
  · change middlePayment 941 ≤ middleValue ((point 4 cut 1024 941+point 4 cut 1024 942)/2)
    have hp : middlePayment 941 = (662803902193:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 941+point 4 cut 1024 942)/2 = (84853999:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84853999:ℝ)/21094400) = (6794240:ℝ)/4227229 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84853999:ℝ)/21094400)-4 = (476399:ℝ)/21094400 by norm_num]
    exact paid_middle_941
  · change middlePayment 942 ≤ middleValue ((point 4 cut 1024 942+point 4 cut 1024 943)/2)
    have hp : middlePayment 942 = (662844231069:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 942+point 4 cut 1024 943)/2 = (16970901:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16970901:ℝ)/4218880) = (33971200:ℝ)/21135639 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16970901:ℝ)/4218880)-4 = (95381:ℝ)/4218880 by norm_num]
    exact paid_middle_942
  · change middlePayment 943 ≤ middleValue ((point 4 cut 1024 943+point 4 cut 1024 944)/2)
    have hp : middlePayment 943 = (662884561521:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 943+point 4 cut 1024 944)/2 = (84855011:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84855011:ℝ)/21094400) = (33971200:ℝ)/21135133 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84855011:ℝ)/21094400)-4 = (477411:ℝ)/21094400 by norm_num]
    exact paid_middle_943
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_058
