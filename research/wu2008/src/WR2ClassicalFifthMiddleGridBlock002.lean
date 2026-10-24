import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints002
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_002 (j : Fin 16) : middlePayment (16*2+j.val) ≤
    middleValue ((point 4 cut 1024 (16*2+j.val)+point 4 cut 1024 (16*2+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 32 ≤ middleValue ((point 4 cut 1024 32+point 4 cut 1024 33)/2)
    have hp : middlePayment 32 = (626786934538:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 32+point 4 cut 1024 33)/2 = (16878809:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16878809:ℝ)/4218880) = (33971200:ℝ)/21596099 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16878809:ℝ)/4218880)-4 = (3289:ℝ)/4218880 by norm_num]
    exact paid_middle_32
  · change middlePayment 33 ≤ middleValue ((point 4 cut 1024 33+point 4 cut 1024 34)/2)
    have hp : middlePayment 33 = (626825863165:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 33+point 4 cut 1024 34)/2 = (84394551:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84394551:ℝ)/21094400) = (33971200:ℝ)/21595593 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84394551:ℝ)/21094400)-4 = (16951:ℝ)/21094400 by norm_num]
    exact paid_middle_33
  · change middlePayment 34 ≤ middleValue ((point 4 cut 1024 34+point 4 cut 1024 35)/2)
    have hp : middlePayment 34 = (626864793298:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 34+point 4 cut 1024 35)/2 = (84395057:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84395057:ℝ)/21094400) = (33971200:ℝ)/21595087 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84395057:ℝ)/21094400)-4 = (17457:ℝ)/21094400 by norm_num]
    exact paid_middle_34
  · change middlePayment 35 ≤ middleValue ((point 4 cut 1024 35+point 4 cut 1024 36)/2)
    have hp : middlePayment 35 = (626903724936:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 35+point 4 cut 1024 36)/2 = (84395563:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84395563:ℝ)/21094400) = (33971200:ℝ)/21594581 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84395563:ℝ)/21094400)-4 = (17963:ℝ)/21094400 by norm_num]
    exact paid_middle_35
  · change middlePayment 36 ≤ middleValue ((point 4 cut 1024 36+point 4 cut 1024 37)/2)
    have hp : middlePayment 36 = (626942658080:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 36+point 4 cut 1024 37)/2 = (84396069:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84396069:ℝ)/21094400) = (1358848:ℝ)/863763 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84396069:ℝ)/21094400)-4 = (18469:ℝ)/21094400 by norm_num]
    exact paid_middle_36
  · change middlePayment 37 ≤ middleValue ((point 4 cut 1024 37+point 4 cut 1024 38)/2)
    have hp : middlePayment 37 = (626981592730:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 37+point 4 cut 1024 38)/2 = (3375863:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3375863:ℝ)/843776) = (33971200:ℝ)/21593569 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3375863:ℝ)/843776)-4 = (759:ℝ)/843776 by norm_num]
    exact paid_middle_37
  · change middlePayment 38 ≤ middleValue ((point 4 cut 1024 38+point 4 cut 1024 39)/2)
    have hp : middlePayment 38 = (627020528886:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 38+point 4 cut 1024 39)/2 = (84397081:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84397081:ℝ)/21094400) = (33971200:ℝ)/21593063 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84397081:ℝ)/21094400)-4 = (19481:ℝ)/21094400 by norm_num]
    exact paid_middle_38
  · change middlePayment 39 ≤ middleValue ((point 4 cut 1024 39+point 4 cut 1024 40)/2)
    have hp : middlePayment 39 = (627059466547:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 39+point 4 cut 1024 40)/2 = (84397587:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84397587:ℝ)/21094400) = (33971200:ℝ)/21592557 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84397587:ℝ)/21094400)-4 = (19987:ℝ)/21094400 by norm_num]
    exact paid_middle_39
  · change middlePayment 40 ≤ middleValue ((point 4 cut 1024 40+point 4 cut 1024 41)/2)
    have hp : middlePayment 40 = (627098405715:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 40+point 4 cut 1024 41)/2 = (84398093:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84398093:ℝ)/21094400) = (33971200:ℝ)/21592051 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84398093:ℝ)/21094400)-4 = (20493:ℝ)/21094400 by norm_num]
    exact paid_middle_40
  · change middlePayment 41 ≤ middleValue ((point 4 cut 1024 41+point 4 cut 1024 42)/2)
    have hp : middlePayment 41 = (627137346388:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 41+point 4 cut 1024 42)/2 = (84398599:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84398599:ℝ)/21094400) = (6794240:ℝ)/4318309 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84398599:ℝ)/21094400)-4 = (20999:ℝ)/21094400 by norm_num]
    exact paid_middle_41
  · change middlePayment 42 ≤ middleValue ((point 4 cut 1024 42+point 4 cut 1024 43)/2)
    have hp : middlePayment 42 = (627176288568:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 42+point 4 cut 1024 43)/2 = (16879821:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16879821:ℝ)/4218880) = (33971200:ℝ)/21591039 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16879821:ℝ)/4218880)-4 = (4301:ℝ)/4218880 by norm_num]
    exact paid_middle_42
  · change middlePayment 43 ≤ middleValue ((point 4 cut 1024 43+point 4 cut 1024 44)/2)
    have hp : middlePayment 43 = (627215232254:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 43+point 4 cut 1024 44)/2 = (84399611:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84399611:ℝ)/21094400) = (33971200:ℝ)/21590533 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84399611:ℝ)/21094400)-4 = (22011:ℝ)/21094400 by norm_num]
    exact paid_middle_43
  · change middlePayment 44 ≤ middleValue ((point 4 cut 1024 44+point 4 cut 1024 45)/2)
    have hp : middlePayment 44 = (627254177446:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 44+point 4 cut 1024 45)/2 = (84400117:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84400117:ℝ)/21094400) = (33971200:ℝ)/21590027 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84400117:ℝ)/21094400)-4 = (22517:ℝ)/21094400 by norm_num]
    exact paid_middle_44
  · change middlePayment 45 ≤ middleValue ((point 4 cut 1024 45+point 4 cut 1024 46)/2)
    have hp : middlePayment 45 = (627293124144:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 45+point 4 cut 1024 46)/2 = (84400623:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84400623:ℝ)/21094400) = (33971200:ℝ)/21589521 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84400623:ℝ)/21094400)-4 = (23023:ℝ)/21094400 by norm_num]
    exact paid_middle_45
  · change middlePayment 46 ≤ middleValue ((point 4 cut 1024 46+point 4 cut 1024 47)/2)
    have hp : middlePayment 46 = (627332072349:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 46+point 4 cut 1024 47)/2 = (84401129:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84401129:ℝ)/21094400) = (6794240:ℝ)/4317803 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84401129:ℝ)/21094400)-4 = (23529:ℝ)/21094400 by norm_num]
    exact paid_middle_46
  · change middlePayment 47 ≤ middleValue ((point 4 cut 1024 47+point 4 cut 1024 48)/2)
    have hp : middlePayment 47 = (627371022060:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 47+point 4 cut 1024 48)/2 = (16880327:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16880327:ℝ)/4218880) = (33971200:ℝ)/21588509 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16880327:ℝ)/4218880)-4 = (4807:ℝ)/4218880 by norm_num]
    exact paid_middle_47
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_002
