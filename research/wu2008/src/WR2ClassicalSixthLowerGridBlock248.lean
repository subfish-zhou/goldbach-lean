import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints248
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_248 (j : Fin 16) : lowerPayment (16*248+j.val) ≤
    lowerValue ((point 2 split 4096 (16*248+j.val)+point 2 split 4096 (16*248+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3968 ≤ lowerValue ((point 2 split 4096 3968+point 2 split 4096 3969)/2)
    have hp : lowerPayment 3968 = (411378663331:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3968+point 2 split 4096 3969)/2 = (568723147:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((568723147:ℝ)/168755200)/ClassicalSixthBranch.v ((568723147:ℝ)/168755200) = (101439172287:ℝ)/46011831224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3968
  · change lowerPayment 3969 ≤ lowerValue ((point 2 split 4096 3969+point 2 split 4096 3970)/2)
    have hp : lowerPayment 3969 = (411478740271:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3969+point 2 split 4096 3970)/2 = (568781409:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((568781409:ℝ)/168755200)/ClassicalSixthBranch.v ((568781409:ℝ)/168755200) = (507118547761:ℝ)/230011148232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3969
  · change lowerPayment 3970 ≤ lowerValue ((point 2 split 4096 3970+point 2 split 4096 3971)/2)
    have hp : lowerPayment 3970 = (411578837136:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3970+point 2 split 4096 3971)/2 = (568839671:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((568839671:ℝ)/168755200)/ClassicalSixthBranch.v ((568839671:ℝ)/168755200) = (507041234087:ℝ)/229963140344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3970
  · change lowerPayment 3971 ≤ lowerValue ((point 2 split 4096 3971+point 2 split 4096 3972)/2)
    have hp : lowerPayment 3971 = (411678953946:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3971+point 2 split 4096 3972)/2 = (568897933:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((568897933:ℝ)/168755200)/ClassicalSixthBranch.v ((568897933:ℝ)/168755200) = (506963920413:ℝ)/229915132456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3971
  · change lowerPayment 3972 ≤ lowerValue ((point 2 split 4096 3972+point 2 split 4096 3973)/2)
    have hp : lowerPayment 3972 = (411779090718:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3972+point 2 split 4096 3973)/2 = (113791239:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((113791239:ℝ)/33751040)/ClassicalSixthBranch.v ((113791239:ℝ)/33751040) = (506886606739:ℝ)/229867124568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3972
  · change lowerPayment 3973 ≤ lowerValue ((point 2 split 4096 3973+point 2 split 4096 3974)/2)
    have hp : lowerPayment 3973 = (411879247473:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3973+point 2 split 4096 3974)/2 = (569014457:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((569014457:ℝ)/168755200)/ClassicalSixthBranch.v ((569014457:ℝ)/168755200) = (101361858613:ℝ)/45963823336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3973
  · change lowerPayment 3974 ≤ lowerValue ((point 2 split 4096 3974+point 2 split 4096 3975)/2)
    have hp : lowerPayment 3974 = (411979424228:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3974+point 2 split 4096 3975)/2 = (569072719:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((569072719:ℝ)/168755200)/ClassicalSixthBranch.v ((569072719:ℝ)/168755200) = (506731979391:ℝ)/229771108792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3974
  · change lowerPayment 3975 ≤ lowerValue ((point 2 split 4096 3975+point 2 split 4096 3976)/2)
    have hp : lowerPayment 3975 = (412079621002:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3975+point 2 split 4096 3976)/2 = (569130981:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((569130981:ℝ)/168755200)/ClassicalSixthBranch.v ((569130981:ℝ)/168755200) = (506654665717:ℝ)/229723100904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3975
  · change lowerPayment 3976 ≤ lowerValue ((point 2 split 4096 3976+point 2 split 4096 3977)/2)
    have hp : lowerPayment 3976 = (412179837814:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3976+point 2 split 4096 3977)/2 = (569189243:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((569189243:ℝ)/168755200)/ClassicalSixthBranch.v ((569189243:ℝ)/168755200) = (506577352043:ℝ)/229675093016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3976
  · change lowerPayment 3977 ≤ lowerValue ((point 2 split 4096 3977+point 2 split 4096 3978)/2)
    have hp : lowerPayment 3977 = (412280074682:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3977+point 2 split 4096 3978)/2 = (113849501:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((113849501:ℝ)/33751040)/ClassicalSixthBranch.v ((113849501:ℝ)/33751040) = (506500038369:ℝ)/229627085128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3977
  · change lowerPayment 3978 ≤ lowerValue ((point 2 split 4096 3978+point 2 split 4096 3979)/2)
    have hp : lowerPayment 3978 = (412380331625:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3978+point 2 split 4096 3979)/2 = (569305767:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((569305767:ℝ)/168755200)/ClassicalSixthBranch.v ((569305767:ℝ)/168755200) = (101284544939:ℝ)/45915815448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3978
  · change lowerPayment 3979 ≤ lowerValue ((point 2 split 4096 3979+point 2 split 4096 3980)/2)
    have hp : lowerPayment 3979 = (412480608662:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3979+point 2 split 4096 3980)/2 = (569364029:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((569364029:ℝ)/168755200)/ClassicalSixthBranch.v ((569364029:ℝ)/168755200) = (506345411021:ℝ)/229531069352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3979
  · change lowerPayment 3980 ≤ lowerValue ((point 2 split 4096 3980+point 2 split 4096 3981)/2)
    have hp : lowerPayment 3980 = (412580905812:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3980+point 2 split 4096 3981)/2 = (569422291:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((569422291:ℝ)/168755200)/ClassicalSixthBranch.v ((569422291:ℝ)/168755200) = (506268097347:ℝ)/229483061464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3980
  · change lowerPayment 3981 ≤ lowerValue ((point 2 split 4096 3981+point 2 split 4096 3982)/2)
    have hp : lowerPayment 3981 = (412681223092:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3981+point 2 split 4096 3982)/2 = (569480553:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((569480553:ℝ)/168755200)/ClassicalSixthBranch.v ((569480553:ℝ)/168755200) = (506190783673:ℝ)/229435053576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3981
  · change lowerPayment 3982 ≤ lowerValue ((point 2 split 4096 3982+point 2 split 4096 3983)/2)
    have hp : lowerPayment 3982 = (412781560523:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3982+point 2 split 4096 3983)/2 = (113907763:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((113907763:ℝ)/33751040)/ClassicalSixthBranch.v ((113907763:ℝ)/33751040) = (506113469999:ℝ)/229387045688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3982
  · change lowerPayment 3983 ≤ lowerValue ((point 2 split 4096 3983+point 2 split 4096 3984)/2)
    have hp : lowerPayment 3983 = (412881918123:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3983+point 2 split 4096 3984)/2 = (569597077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((569597077:ℝ)/168755200)/ClassicalSixthBranch.v ((569597077:ℝ)/168755200) = (20241446253:ℝ)/9173561512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3983
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_248
