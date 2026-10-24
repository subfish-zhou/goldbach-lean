import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints019
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_019 (j : Fin 16) : lowerPayment (16*19+j.val) ≤
    lowerValue ((point 2 split 4096 (16*19+j.val)+point 2 split 4096 (16*19+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 304 ≤ lowerValue ((point 2 split 4096 304+point 2 split 4096 305)/2)
    have hp : lowerPayment 304 = (46347369468:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 304+point 2 split 4096 305)/2 = (355251179:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((355251179:ℝ)/168755200)/ClassicalSixthBranch.v ((355251179:ℝ)/168755200) = (790473162971:ℝ)/405960057752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_304
  · change lowerPayment 305 ≤ lowerValue ((point 2 split 4096 305+point 2 split 4096 306)/2)
    have hp : lowerPayment 305 = (46489541211:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 305+point 2 split 4096 306)/2 = (355309441:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((355309441:ℝ)/168755200)/ClassicalSixthBranch.v ((355309441:ℝ)/168755200) = (790395849297:ℝ)/405912049864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_305
  · change lowerPayment 306 ≤ lowerValue ((point 2 split 4096 306+point 2 split 4096 307)/2)
    have hp : lowerPayment 306 = (46631653146:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 306+point 2 split 4096 307)/2 = (355367703:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((355367703:ℝ)/168755200)/ClassicalSixthBranch.v ((355367703:ℝ)/168755200) = (790318535623:ℝ)/405864041976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_306
  · change lowerPayment 307 ≤ lowerValue ((point 2 split 4096 307+point 2 split 4096 308)/2)
    have hp : lowerPayment 307 = (46773705328:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 307+point 2 split 4096 308)/2 = (71085193:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((71085193:ℝ)/33751040)/ClassicalSixthBranch.v ((71085193:ℝ)/33751040) = (790241221949:ℝ)/405816034088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_307
  · change lowerPayment 308 ≤ lowerValue ((point 2 split 4096 308+point 2 split 4096 309)/2)
    have hp : lowerPayment 308 = (46915697808:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 308+point 2 split 4096 309)/2 = (355484227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((355484227:ℝ)/168755200)/ClassicalSixthBranch.v ((355484227:ℝ)/168755200) = (31606556331:ℝ)/16230721048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_308
  · change lowerPayment 309 ≤ lowerValue ((point 2 split 4096 309+point 2 split 4096 310)/2)
    have hp : lowerPayment 309 = (47057630640:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 309+point 2 split 4096 310)/2 = (355542489:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((355542489:ℝ)/168755200)/ClassicalSixthBranch.v ((355542489:ℝ)/168755200) = (790086594601:ℝ)/405720018312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_309
  · change lowerPayment 310 ≤ lowerValue ((point 2 split 4096 310+point 2 split 4096 311)/2)
    have hp : lowerPayment 310 = (47199503878:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 310+point 2 split 4096 311)/2 = (355600751:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((355600751:ℝ)/168755200)/ClassicalSixthBranch.v ((355600751:ℝ)/168755200) = (790009280927:ℝ)/405672010424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_310
  · change lowerPayment 311 ≤ lowerValue ((point 2 split 4096 311+point 2 split 4096 312)/2)
    have hp : lowerPayment 311 = (47341317575:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 311+point 2 split 4096 312)/2 = (355659013:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((355659013:ℝ)/168755200)/ClassicalSixthBranch.v ((355659013:ℝ)/168755200) = (789931967253:ℝ)/405624002536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_311
  · change lowerPayment 312 ≤ lowerValue ((point 2 split 4096 312+point 2 split 4096 313)/2)
    have hp : lowerPayment 312 = (47483071784:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 312+point 2 split 4096 313)/2 = (14228691:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((14228691:ℝ)/6750208)/ClassicalSixthBranch.v ((14228691:ℝ)/6750208) = (789854653579:ℝ)/405575994648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_312
  · change lowerPayment 313 ≤ lowerValue ((point 2 split 4096 313+point 2 split 4096 314)/2)
    have hp : lowerPayment 313 = (47624766558:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 313+point 2 split 4096 314)/2 = (355775537:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((355775537:ℝ)/168755200)/ClassicalSixthBranch.v ((355775537:ℝ)/168755200) = (157955467981:ℝ)/81105597352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_313
  · change lowerPayment 314 ≤ lowerValue ((point 2 split 4096 314+point 2 split 4096 315)/2)
    have hp : lowerPayment 314 = (47766401951:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 314+point 2 split 4096 315)/2 = (355833799:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((355833799:ℝ)/168755200)/ClassicalSixthBranch.v ((355833799:ℝ)/168755200) = (789700026231:ℝ)/405479978872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_314
  · change lowerPayment 315 ≤ lowerValue ((point 2 split 4096 315+point 2 split 4096 316)/2)
    have hp : lowerPayment 315 = (47907978015:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 315+point 2 split 4096 316)/2 = (355892061:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((355892061:ℝ)/168755200)/ClassicalSixthBranch.v ((355892061:ℝ)/168755200) = (789622712557:ℝ)/405431970984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_315
  · change lowerPayment 316 ≤ lowerValue ((point 2 split 4096 316+point 2 split 4096 317)/2)
    have hp : lowerPayment 316 = (48049494803:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 316+point 2 split 4096 317)/2 = (355950323:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((355950323:ℝ)/168755200)/ClassicalSixthBranch.v ((355950323:ℝ)/168755200) = (789545398883:ℝ)/405383963096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_316
  · change lowerPayment 317 ≤ lowerValue ((point 2 split 4096 317+point 2 split 4096 318)/2)
    have hp : lowerPayment 317 = (48190952368:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 317+point 2 split 4096 318)/2 = (71201717:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((71201717:ℝ)/33751040)/ClassicalSixthBranch.v ((71201717:ℝ)/33751040) = (789468085209:ℝ)/405335955208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_317
  · change lowerPayment 318 ≤ lowerValue ((point 2 split 4096 318+point 2 split 4096 319)/2)
    have hp : lowerPayment 318 = (48332350764:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 318+point 2 split 4096 319)/2 = (356066847:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((356066847:ℝ)/168755200)/ClassicalSixthBranch.v ((356066847:ℝ)/168755200) = (157878154307:ℝ)/81057589464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_318
  · change lowerPayment 319 ≤ lowerValue ((point 2 split 4096 319+point 2 split 4096 320)/2)
    have hp : lowerPayment 319 = (48473690042:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 319+point 2 split 4096 320)/2 = (356125109:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((356125109:ℝ)/168755200)/ClassicalSixthBranch.v ((356125109:ℝ)/168755200) = (789313457861:ℝ)/405239939432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_319
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_019
