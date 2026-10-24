import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints018
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_018 (j : Fin 16) : initialPayment (16*18+j.val) ≤
    initialValue ((point lo 4 1024 (16*18+j.val)+point lo 4 1024 (16*18+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 288 ≤ initialValue ((point lo 4 1024 288+point lo 4 1024 289)/2)
    have hp : initialPayment 288 = (124309413418:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 288+point lo 4 1024 289)/2 = (151001701:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151001701:ℝ)/42188800) = (67942400:ℝ)/60978587 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_288
  · change initialPayment 289 ≤ initialValue ((point lo 4 1024 289+point lo 4 1024 290)/2)
    have hp : initialPayment 289 = (124797173676:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 289+point lo 4 1024 290)/2 = (151025839:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151025839:ℝ)/42188800) = (67942400:ℝ)/60954449 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_289
  · change initialPayment 290 ≤ initialValue ((point lo 4 1024 290+point lo 4 1024 291)/2)
    have hp : initialPayment 290 = (125285355141:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 290+point lo 4 1024 291)/2 = (151049977:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151049977:ℝ)/42188800) = (67942400:ℝ)/60930311 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_290
  · change initialPayment 291 ≤ initialValue ((point lo 4 1024 291+point lo 4 1024 292)/2)
    have hp : initialPayment 291 = (125773958136:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 291+point lo 4 1024 292)/2 = (30214823:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30214823:ℝ)/8437760) = (67942400:ℝ)/60906173 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_291
  · change initialPayment 292 ≤ initialValue ((point lo 4 1024 292+point lo 4 1024 293)/2)
    have hp : initialPayment 292 = (126262982986:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 292+point lo 4 1024 293)/2 = (151098253:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151098253:ℝ)/42188800) = (13588480:ℝ)/12176407 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_292
  · change initialPayment 293 ≤ initialValue ((point lo 4 1024 293+point lo 4 1024 294)/2)
    have hp : initialPayment 293 = (126752430016:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 293+point lo 4 1024 294)/2 = (151122391:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151122391:ℝ)/42188800) = (67942400:ℝ)/60857897 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_293
  · change initialPayment 294 ≤ initialValue ((point lo 4 1024 294+point lo 4 1024 295)/2)
    have hp : initialPayment 294 = (127242299552:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 294+point lo 4 1024 295)/2 = (151146529:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151146529:ℝ)/42188800) = (67942400:ℝ)/60833759 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_294
  · change initialPayment 295 ≤ initialValue ((point lo 4 1024 295+point lo 4 1024 296)/2)
    have hp : initialPayment 295 = (127732591918:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 295+point lo 4 1024 296)/2 = (151170667:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151170667:ℝ)/42188800) = (67942400:ℝ)/60809621 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_295
  · change initialPayment 296 ≤ initialValue ((point lo 4 1024 296+point lo 4 1024 297)/2)
    have hp : initialPayment 296 = (128223307441:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 296+point lo 4 1024 297)/2 = (30238961:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30238961:ℝ)/8437760) = (67942400:ℝ)/60785483 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_296
  · change initialPayment 297 ≤ initialValue ((point lo 4 1024 297+point lo 4 1024 298)/2)
    have hp : initialPayment 297 = (128714446449:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 297+point lo 4 1024 298)/2 = (151218943:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151218943:ℝ)/42188800) = (13588480:ℝ)/12152269 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_297
  · change initialPayment 298 ≤ initialValue ((point lo 4 1024 298+point lo 4 1024 299)/2)
    have hp : initialPayment 298 = (129206009267:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 298+point lo 4 1024 299)/2 = (151243081:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151243081:ℝ)/42188800) = (67942400:ℝ)/60737207 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_298
  · change initialPayment 299 ≤ initialValue ((point lo 4 1024 299+point lo 4 1024 300)/2)
    have hp : initialPayment 299 = (129697996225:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 299+point lo 4 1024 300)/2 = (151267219:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151267219:ℝ)/42188800) = (67942400:ℝ)/60713069 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_299
  · change initialPayment 300 ≤ initialValue ((point lo 4 1024 300+point lo 4 1024 301)/2)
    have hp : initialPayment 300 = (130190407650:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 300+point lo 4 1024 301)/2 = (151291357:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151291357:ℝ)/42188800) = (67942400:ℝ)/60688931 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_300
  · change initialPayment 301 ≤ initialValue ((point lo 4 1024 301+point lo 4 1024 302)/2)
    have hp : initialPayment 301 = (130683243871:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 301+point lo 4 1024 302)/2 = (30263099:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30263099:ℝ)/8437760) = (67942400:ℝ)/60664793 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_301
  · change initialPayment 302 ≤ initialValue ((point lo 4 1024 302+point lo 4 1024 303)/2)
    have hp : initialPayment 302 = (131176505217:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 302+point lo 4 1024 303)/2 = (151339633:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151339633:ℝ)/42188800) = (13588480:ℝ)/12128131 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_302
  · change initialPayment 303 ≤ initialValue ((point lo 4 1024 303+point lo 4 1024 304)/2)
    have hp : initialPayment 303 = (131670192018:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 303+point lo 4 1024 304)/2 = (151363771:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151363771:ℝ)/42188800) = (67942400:ℝ)/60616517 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_303
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_018
