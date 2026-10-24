import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints010
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_010 (j : Fin 16) : initialPayment (16*10+j.val) ≤
    initialValue ((point lo 4 1024 (16*10+j.val)+point lo 4 1024 (16*10+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 160 ≤ initialValue ((point lo 4 1024 160+point lo 4 1024 161)/2)
    have hp : initialPayment 160 = (65243063559:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 160+point lo 4 1024 161)/2 = (147912037:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147912037:ℝ)/42188800) = (67942400:ℝ)/64068251 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_160
  · change initialPayment 161 ≤ initialValue ((point lo 4 1024 161+point lo 4 1024 162)/2)
    have hp : initialPayment 161 = (65679421162:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 161+point lo 4 1024 162)/2 = (5917447:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((5917447:ℝ)/1687552) = (67942400:ℝ)/64044113 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_161
  · change initialPayment 162 ≤ initialValue ((point lo 4 1024 162+point lo 4 1024 163)/2)
    have hp : initialPayment 162 = (66116162207:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 162+point lo 4 1024 163)/2 = (147960313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147960313:ℝ)/42188800) = (2717696:ℝ)/2560799 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_162
  · change initialPayment 163 ≤ initialValue ((point lo 4 1024 163+point lo 4 1024 164)/2)
    have hp : initialPayment 163 = (66553286963:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 163+point lo 4 1024 164)/2 = (147984451:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147984451:ℝ)/42188800) = (67942400:ℝ)/63995837 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_163
  · change initialPayment 164 ≤ initialValue ((point lo 4 1024 164+point lo 4 1024 165)/2)
    have hp : initialPayment 164 = (66990795698:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 164+point lo 4 1024 165)/2 = (148008589:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148008589:ℝ)/42188800) = (67942400:ℝ)/63971699 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_164
  · change initialPayment 165 ≤ initialValue ((point lo 4 1024 165+point lo 4 1024 166)/2)
    have hp : initialPayment 165 = (67428688682:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 165+point lo 4 1024 166)/2 = (148032727:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148032727:ℝ)/42188800) = (67942400:ℝ)/63947561 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_165
  · change initialPayment 166 ≤ initialValue ((point lo 4 1024 166+point lo 4 1024 167)/2)
    have hp : initialPayment 166 = (67866966183:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 166+point lo 4 1024 167)/2 = (29611373:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29611373:ℝ)/8437760) = (67942400:ℝ)/63923423 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_166
  · change initialPayment 167 ≤ initialValue ((point lo 4 1024 167+point lo 4 1024 168)/2)
    have hp : initialPayment 167 = (68305628471:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 167+point lo 4 1024 168)/2 = (148081003:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148081003:ℝ)/42188800) = (13588480:ℝ)/12779857 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_167
  · change initialPayment 168 ≤ initialValue ((point lo 4 1024 168+point lo 4 1024 169)/2)
    have hp : initialPayment 168 = (68744675817:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 168+point lo 4 1024 169)/2 = (148105141:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148105141:ℝ)/42188800) = (67942400:ℝ)/63875147 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_168
  · change initialPayment 169 ≤ initialValue ((point lo 4 1024 169+point lo 4 1024 170)/2)
    have hp : initialPayment 169 = (69184108490:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 169+point lo 4 1024 170)/2 = (148129279:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148129279:ℝ)/42188800) = (67942400:ℝ)/63851009 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_169
  · change initialPayment 170 ≤ initialValue ((point lo 4 1024 170+point lo 4 1024 171)/2)
    have hp : initialPayment 170 = (69623926763:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 170+point lo 4 1024 171)/2 = (148153417:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148153417:ℝ)/42188800) = (67942400:ℝ)/63826871 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_170
  · change initialPayment 171 ≤ initialValue ((point lo 4 1024 171+point lo 4 1024 172)/2)
    have hp : initialPayment 171 = (70064130906:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 171+point lo 4 1024 172)/2 = (29635511:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29635511:ℝ)/8437760) = (67942400:ℝ)/63802733 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_171
  · change initialPayment 172 ≤ initialValue ((point lo 4 1024 172+point lo 4 1024 173)/2)
    have hp : initialPayment 172 = (70504721192:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 172+point lo 4 1024 173)/2 = (148201693:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148201693:ℝ)/42188800) = (13588480:ℝ)/12755719 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_172
  · change initialPayment 173 ≤ initialValue ((point lo 4 1024 173+point lo 4 1024 174)/2)
    have hp : initialPayment 173 = (70945697892:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 173+point lo 4 1024 174)/2 = (148225831:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148225831:ℝ)/42188800) = (67942400:ℝ)/63754457 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_173
  · change initialPayment 174 ≤ initialValue ((point lo 4 1024 174+point lo 4 1024 175)/2)
    have hp : initialPayment 174 = (71387061278:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 174+point lo 4 1024 175)/2 = (148249969:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148249969:ℝ)/42188800) = (67942400:ℝ)/63730319 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_174
  · change initialPayment 175 ≤ initialValue ((point lo 4 1024 175+point lo 4 1024 176)/2)
    have hp : initialPayment 175 = (71828811625:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 175+point lo 4 1024 176)/2 = (148274107:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148274107:ℝ)/42188800) = (67942400:ℝ)/63706181 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_175
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_010
