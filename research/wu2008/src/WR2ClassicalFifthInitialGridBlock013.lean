import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints013
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_013 (j : Fin 16) : initialPayment (16*13+j.val) ≤
    initialValue ((point lo 4 1024 (16*13+j.val)+point lo 4 1024 (16*13+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 208 ≤ initialValue ((point lo 4 1024 208+point lo 4 1024 209)/2)
    have hp : initialPayment 208 = (86625468583:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 208+point lo 4 1024 209)/2 = (149070661:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149070661:ℝ)/42188800) = (67942400:ℝ)/62909627 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_208
  · change initialPayment 209 ≤ initialValue ((point lo 4 1024 209+point lo 4 1024 210)/2)
    have hp : initialPayment 209 = (87080540940:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 209+point lo 4 1024 210)/2 = (149094799:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149094799:ℝ)/42188800) = (67942400:ℝ)/62885489 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_209
  · change initialPayment 210 ≤ initialValue ((point lo 4 1024 210+point lo 4 1024 211)/2)
    have hp : initialPayment 210 = (87536010073:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 210+point lo 4 1024 211)/2 = (149118937:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149118937:ℝ)/42188800) = (67942400:ℝ)/62861351 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_210
  · change initialPayment 211 ≤ initialValue ((point lo 4 1024 211+point lo 4 1024 212)/2)
    have hp : initialPayment 211 = (87991876268:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 211+point lo 4 1024 212)/2 = (5965723:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((5965723:ℝ)/1687552) = (67942400:ℝ)/62837213 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_211
  · change initialPayment 212 ≤ initialValue ((point lo 4 1024 212+point lo 4 1024 213)/2)
    have hp : initialPayment 212 = (88448139815:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 212+point lo 4 1024 213)/2 = (149167213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149167213:ℝ)/42188800) = (2717696:ℝ)/2512523 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_212
  · change initialPayment 213 ≤ initialValue ((point lo 4 1024 213+point lo 4 1024 214)/2)
    have hp : initialPayment 213 = (88904801002:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 213+point lo 4 1024 214)/2 = (149191351:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149191351:ℝ)/42188800) = (67942400:ℝ)/62788937 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_213
  · change initialPayment 214 ≤ initialValue ((point lo 4 1024 214+point lo 4 1024 215)/2)
    have hp : initialPayment 214 = (89361860119:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 214+point lo 4 1024 215)/2 = (149215489:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149215489:ℝ)/42188800) = (67942400:ℝ)/62764799 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_214
  · change initialPayment 215 ≤ initialValue ((point lo 4 1024 215+point lo 4 1024 216)/2)
    have hp : initialPayment 215 = (89819317454:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 215+point lo 4 1024 216)/2 = (149239627:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149239627:ℝ)/42188800) = (67942400:ℝ)/62740661 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_215
  · change initialPayment 216 ≤ initialValue ((point lo 4 1024 216+point lo 4 1024 217)/2)
    have hp : initialPayment 216 = (90277173299:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 216+point lo 4 1024 217)/2 = (29852753:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29852753:ℝ)/8437760) = (67942400:ℝ)/62716523 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_216
  · change initialPayment 217 ≤ initialValue ((point lo 4 1024 217+point lo 4 1024 218)/2)
    have hp : initialPayment 217 = (90735427943:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 217+point lo 4 1024 218)/2 = (149287903:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149287903:ℝ)/42188800) = (13588480:ℝ)/12538477 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_217
  · change initialPayment 218 ≤ initialValue ((point lo 4 1024 218+point lo 4 1024 219)/2)
    have hp : initialPayment 218 = (91194081679:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 218+point lo 4 1024 219)/2 = (149312041:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149312041:ℝ)/42188800) = (67942400:ℝ)/62668247 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_218
  · change initialPayment 219 ≤ initialValue ((point lo 4 1024 219+point lo 4 1024 220)/2)
    have hp : initialPayment 219 = (91653134796:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 219+point lo 4 1024 220)/2 = (149336179:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149336179:ℝ)/42188800) = (67942400:ℝ)/62644109 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_219
  · change initialPayment 220 ≤ initialValue ((point lo 4 1024 220+point lo 4 1024 221)/2)
    have hp : initialPayment 220 = (92112587587:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 220+point lo 4 1024 221)/2 = (149360317:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149360317:ℝ)/42188800) = (67942400:ℝ)/62619971 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_220
  · change initialPayment 221 ≤ initialValue ((point lo 4 1024 221+point lo 4 1024 222)/2)
    have hp : initialPayment 221 = (92572440345:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 221+point lo 4 1024 222)/2 = (29876891:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29876891:ℝ)/8437760) = (67942400:ℝ)/62595833 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_221
  · change initialPayment 222 ≤ initialValue ((point lo 4 1024 222+point lo 4 1024 223)/2)
    have hp : initialPayment 222 = (93032693361:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 222+point lo 4 1024 223)/2 = (149408593:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149408593:ℝ)/42188800) = (13588480:ℝ)/12514339 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_222
  · change initialPayment 223 ≤ initialValue ((point lo 4 1024 223+point lo 4 1024 224)/2)
    have hp : initialPayment 223 = (93493346930:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 223+point lo 4 1024 224)/2 = (149432731:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149432731:ℝ)/42188800) = (67942400:ℝ)/62547557 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_223
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_013
