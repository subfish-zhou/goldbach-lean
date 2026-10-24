import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints063
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_063 (j : Fin 16) : initialPayment (16*63+j.val) ≤
    initialValue ((point lo 4 1024 (16*63+j.val)+point lo 4 1024 (16*63+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 1008 ≤ initialValue ((point lo 4 1024 1008+point lo 4 1024 1009)/2)
    have hp : initialPayment 1008 = (611251009338:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 1008+point lo 4 1024 1009)/2 = (168381061:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((168381061:ℝ)/42188800) = (67942400:ℝ)/43599227 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_1008
  · change initialPayment 1009 ≤ initialValue ((point lo 4 1024 1009+point lo 4 1024 1010)/2)
    have hp : initialPayment 1009 = (612165628024:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 1009+point lo 4 1024 1010)/2 = (168405199:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((168405199:ℝ)/42188800) = (67942400:ℝ)/43575089 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_1009
  · change initialPayment 1010 ≤ initialValue ((point lo 4 1024 1010+point lo 4 1024 1011)/2)
    have hp : initialPayment 1010 = (613081087445:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 1010+point lo 4 1024 1011)/2 = (168429337:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((168429337:ℝ)/42188800) = (67942400:ℝ)/43550951 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_1010
  · change initialPayment 1011 ≤ initialValue ((point lo 4 1024 1011+point lo 4 1024 1012)/2)
    have hp : initialPayment 1011 = (613997388578:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 1011+point lo 4 1024 1012)/2 = (6738139:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((6738139:ℝ)/1687552) = (67942400:ℝ)/43526813 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_1011
  · change initialPayment 1012 ≤ initialValue ((point lo 4 1024 1012+point lo 4 1024 1013)/2)
    have hp : initialPayment 1012 = (614914532402:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 1012+point lo 4 1024 1013)/2 = (168477613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((168477613:ℝ)/42188800) = (2717696:ℝ)/1740107 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_1012
  · change initialPayment 1013 ≤ initialValue ((point lo 4 1024 1013+point lo 4 1024 1014)/2)
    have hp : initialPayment 1013 = (615832519898:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 1013+point lo 4 1024 1014)/2 = (168501751:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((168501751:ℝ)/42188800) = (67942400:ℝ)/43478537 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_1013
  · change initialPayment 1014 ≤ initialValue ((point lo 4 1024 1014+point lo 4 1024 1015)/2)
    have hp : initialPayment 1014 = (616751352046:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 1014+point lo 4 1024 1015)/2 = (168525889:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((168525889:ℝ)/42188800) = (67942400:ℝ)/43454399 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_1014
  · change initialPayment 1015 ≤ initialValue ((point lo 4 1024 1015+point lo 4 1024 1016)/2)
    have hp : initialPayment 1015 = (617671029831:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 1015+point lo 4 1024 1016)/2 = (168550027:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((168550027:ℝ)/42188800) = (67942400:ℝ)/43430261 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_1015
  · change initialPayment 1016 ≤ initialValue ((point lo 4 1024 1016+point lo 4 1024 1017)/2)
    have hp : initialPayment 1016 = (618591554237:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 1016+point lo 4 1024 1017)/2 = (33714833:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((33714833:ℝ)/8437760) = (67942400:ℝ)/43406123 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_1016
  · change initialPayment 1017 ≤ initialValue ((point lo 4 1024 1017+point lo 4 1024 1018)/2)
    have hp : initialPayment 1017 = (619512926252:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 1017+point lo 4 1024 1018)/2 = (168598303:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((168598303:ℝ)/42188800) = (13588480:ℝ)/8676397 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_1017
  · change initialPayment 1018 ≤ initialValue ((point lo 4 1024 1018+point lo 4 1024 1019)/2)
    have hp : initialPayment 1018 = (620435146864:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 1018+point lo 4 1024 1019)/2 = (168622441:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((168622441:ℝ)/42188800) = (67942400:ℝ)/43357847 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_1018
  · change initialPayment 1019 ≤ initialValue ((point lo 4 1024 1019+point lo 4 1024 1020)/2)
    have hp : initialPayment 1019 = (621358217064:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 1019+point lo 4 1024 1020)/2 = (168646579:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((168646579:ℝ)/42188800) = (67942400:ℝ)/43333709 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_1019
  · change initialPayment 1020 ≤ initialValue ((point lo 4 1024 1020+point lo 4 1024 1021)/2)
    have hp : initialPayment 1020 = (622282137843:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 1020+point lo 4 1024 1021)/2 = (168670717:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((168670717:ℝ)/42188800) = (67942400:ℝ)/43309571 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_1020
  · change initialPayment 1021 ≤ initialValue ((point lo 4 1024 1021+point lo 4 1024 1022)/2)
    have hp : initialPayment 1021 = (623206910194:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 1021+point lo 4 1024 1022)/2 = (33738971:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((33738971:ℝ)/8437760) = (67942400:ℝ)/43285433 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_1021
  · change initialPayment 1022 ≤ initialValue ((point lo 4 1024 1022+point lo 4 1024 1023)/2)
    have hp : initialPayment 1022 = (624132535114:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 1022+point lo 4 1024 1023)/2 = (168718993:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((168718993:ℝ)/42188800) = (13588480:ℝ)/8652259 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_1022
  · change initialPayment 1023 ≤ initialValue ((point lo 4 1024 1023+point lo 4 1024 1024)/2)
    have hp : initialPayment 1023 = (625059013600:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 1023+point lo 4 1024 1024)/2 = (168743131:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((168743131:ℝ)/42188800) = (67942400:ℝ)/43237157 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_1023
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_063
