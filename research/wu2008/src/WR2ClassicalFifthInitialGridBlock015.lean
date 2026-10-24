import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints015
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_015 (j : Fin 16) : initialPayment (16*15+j.val) ≤
    initialValue ((point lo 4 1024 (16*15+j.val)+point lo 4 1024 (16*15+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 240 ≤ initialValue ((point lo 4 1024 240+point lo 4 1024 241)/2)
    have hp : initialPayment 240 = (101386028191:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 240+point lo 4 1024 241)/2 = (149843077:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149843077:ℝ)/42188800) = (67942400:ℝ)/62137211 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_240
  · change initialPayment 241 ≤ initialValue ((point lo 4 1024 241+point lo 4 1024 242)/2)
    have hp : initialPayment 241 = (101853942316:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 241+point lo 4 1024 242)/2 = (29973443:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29973443:ℝ)/8437760) = (67942400:ℝ)/62113073 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_241
  · change initialPayment 242 ≤ initialValue ((point lo 4 1024 242+point lo 4 1024 243)/2)
    have hp : initialPayment 242 = (102322262644:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 242+point lo 4 1024 243)/2 = (149891353:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149891353:ℝ)/42188800) = (13588480:ℝ)/12417787 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_242
  · change initialPayment 243 ≤ initialValue ((point lo 4 1024 243+point lo 4 1024 244)/2)
    have hp : initialPayment 243 = (102790989479:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 243+point lo 4 1024 244)/2 = (149915491:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149915491:ℝ)/42188800) = (67942400:ℝ)/62064797 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_243
  · change initialPayment 244 ≤ initialValue ((point lo 4 1024 244+point lo 4 1024 245)/2)
    have hp : initialPayment 244 = (103260123122:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 244+point lo 4 1024 245)/2 = (149939629:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149939629:ℝ)/42188800) = (67942400:ℝ)/62040659 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_244
  · change initialPayment 245 ≤ initialValue ((point lo 4 1024 245+point lo 4 1024 246)/2)
    have hp : initialPayment 245 = (103729663877:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 245+point lo 4 1024 246)/2 = (149963767:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149963767:ℝ)/42188800) = (67942400:ℝ)/62016521 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_245
  · change initialPayment 246 ≤ initialValue ((point lo 4 1024 246+point lo 4 1024 247)/2)
    have hp : initialPayment 246 = (104199612045:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 246+point lo 4 1024 247)/2 = (29997581:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29997581:ℝ)/8437760) = (67942400:ℝ)/61992383 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_246
  · change initialPayment 247 ≤ initialValue ((point lo 4 1024 247+point lo 4 1024 248)/2)
    have hp : initialPayment 247 = (104669967932:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 247+point lo 4 1024 248)/2 = (150012043:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150012043:ℝ)/42188800) = (13588480:ℝ)/12393649 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_247
  · change initialPayment 248 ≤ initialValue ((point lo 4 1024 248+point lo 4 1024 249)/2)
    have hp : initialPayment 248 = (105140731841:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 248+point lo 4 1024 249)/2 = (150036181:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150036181:ℝ)/42188800) = (67942400:ℝ)/61944107 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_248
  · change initialPayment 249 ≤ initialValue ((point lo 4 1024 249+point lo 4 1024 250)/2)
    have hp : initialPayment 249 = (105611904077:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 249+point lo 4 1024 250)/2 = (150060319:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150060319:ℝ)/42188800) = (67942400:ℝ)/61919969 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_249
  · change initialPayment 250 ≤ initialValue ((point lo 4 1024 250+point lo 4 1024 251)/2)
    have hp : initialPayment 250 = (106083484944:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 250+point lo 4 1024 251)/2 = (150084457:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150084457:ℝ)/42188800) = (67942400:ℝ)/61895831 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_250
  · change initialPayment 251 ≤ initialValue ((point lo 4 1024 251+point lo 4 1024 252)/2)
    have hp : initialPayment 251 = (106555474749:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 251+point lo 4 1024 252)/2 = (291473:ℝ)/81920 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((291473:ℝ)/81920) = (67942400:ℝ)/61871693 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_251
  · change initialPayment 252 ≤ initialValue ((point lo 4 1024 252+point lo 4 1024 253)/2)
    have hp : initialPayment 252 = (107027873796:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 252+point lo 4 1024 253)/2 = (150132733:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150132733:ℝ)/42188800) = (13588480:ℝ)/12369511 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_252
  · change initialPayment 253 ≤ initialValue ((point lo 4 1024 253+point lo 4 1024 254)/2)
    have hp : initialPayment 253 = (107500682394:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 253+point lo 4 1024 254)/2 = (150156871:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150156871:ℝ)/42188800) = (67942400:ℝ)/61823417 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_253
  · change initialPayment 254 ≤ initialValue ((point lo 4 1024 254+point lo 4 1024 255)/2)
    have hp : initialPayment 254 = (107973900847:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 254+point lo 4 1024 255)/2 = (150181009:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150181009:ℝ)/42188800) = (67942400:ℝ)/61799279 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_254
  · change initialPayment 255 ≤ initialValue ((point lo 4 1024 255+point lo 4 1024 256)/2)
    have hp : initialPayment 255 = (108447529464:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 255+point lo 4 1024 256)/2 = (150205147:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150205147:ℝ)/42188800) = (67942400:ℝ)/61775141 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_255
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_015
