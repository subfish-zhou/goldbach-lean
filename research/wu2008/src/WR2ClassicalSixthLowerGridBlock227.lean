import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints227
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_227 (j : Fin 16) : lowerPayment (16*227+j.val) ≤
    lowerValue ((point 2 split 4096 (16*227+j.val)+point 2 split 4096 (16*227+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3632 ≤ lowerValue ((point 2 split 4096 3632+point 2 split 4096 3633)/2)
    have hp : lowerPayment 3632 = (378766582709:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3632+point 2 split 4096 3633)/2 = (109829423:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((109829423:ℝ)/33751040)/ClassicalSixthBranch.v ((109829423:ℝ)/33751040) = (533173255899:ℝ)/246189806488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3632
  · change lowerPayment 3633 ≤ lowerValue ((point 2 split 4096 3633+point 2 split 4096 3634)/2)
    have hp : lowerPayment 3633 = (378860967579:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3633+point 2 split 4096 3634)/2 = (549205377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((549205377:ℝ)/168755200)/ClassicalSixthBranch.v ((549205377:ℝ)/168755200) = (21323837689:ℝ)/9845671944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3633
  · change lowerPayment 3634 ≤ lowerValue ((point 2 split 4096 3634+point 2 split 4096 3635)/2)
    have hp : lowerPayment 3634 = (378955366557:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3634+point 2 split 4096 3635)/2 = (549263639:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((549263639:ℝ)/168755200)/ClassicalSixthBranch.v ((549263639:ℝ)/168755200) = (533018628551:ℝ)/246093790712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3634
  · change lowerPayment 3635 ≤ lowerValue ((point 2 split 4096 3635+point 2 split 4096 3636)/2)
    have hp : lowerPayment 3635 = (379049779661:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3635+point 2 split 4096 3636)/2 = (549321901:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((549321901:ℝ)/168755200)/ClassicalSixthBranch.v ((549321901:ℝ)/168755200) = (532941314877:ℝ)/246045782824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3635
  · change lowerPayment 3636 ≤ lowerValue ((point 2 split 4096 3636+point 2 split 4096 3637)/2)
    have hp : lowerPayment 3636 = (379144206905:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3636+point 2 split 4096 3637)/2 = (549380163:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((549380163:ℝ)/168755200)/ClassicalSixthBranch.v ((549380163:ℝ)/168755200) = (532864001203:ℝ)/245997774936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3636
  · change lowerPayment 3637 ≤ lowerValue ((point 2 split 4096 3637+point 2 split 4096 3638)/2)
    have hp : lowerPayment 3637 = (379238648307:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3637+point 2 split 4096 3638)/2 = (21977537:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((21977537:ℝ)/6750208)/ClassicalSixthBranch.v ((21977537:ℝ)/6750208) = (532786687529:ℝ)/245949767048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3637
  · change lowerPayment 3638 ≤ lowerValue ((point 2 split 4096 3638+point 2 split 4096 3639)/2)
    have hp : lowerPayment 3638 = (379333103882:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3638+point 2 split 4096 3639)/2 = (549496687:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((549496687:ℝ)/168755200)/ClassicalSixthBranch.v ((549496687:ℝ)/168755200) = (106541874771:ℝ)/49180351832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3638
  · change lowerPayment 3639 ≤ lowerValue ((point 2 split 4096 3639+point 2 split 4096 3640)/2)
    have hp : lowerPayment 3639 = (379427573647:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3639+point 2 split 4096 3640)/2 = (549554949:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((549554949:ℝ)/168755200)/ClassicalSixthBranch.v ((549554949:ℝ)/168755200) = (532632060181:ℝ)/245853751272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3639
  · change lowerPayment 3640 ≤ lowerValue ((point 2 split 4096 3640+point 2 split 4096 3641)/2)
    have hp : lowerPayment 3640 = (379522057618:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3640+point 2 split 4096 3641)/2 = (549613211:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((549613211:ℝ)/168755200)/ClassicalSixthBranch.v ((549613211:ℝ)/168755200) = (532554746507:ℝ)/245805743384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3640
  · change lowerPayment 3641 ≤ lowerValue ((point 2 split 4096 3641+point 2 split 4096 3642)/2)
    have hp : lowerPayment 3641 = (379616555811:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3641+point 2 split 4096 3642)/2 = (549671473:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((549671473:ℝ)/168755200)/ClassicalSixthBranch.v ((549671473:ℝ)/168755200) = (532477432833:ℝ)/245757735496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3641
  · change lowerPayment 3642 ≤ lowerValue ((point 2 split 4096 3642+point 2 split 4096 3643)/2)
    have hp : lowerPayment 3642 = (379711068243:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3642+point 2 split 4096 3643)/2 = (109945947:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((109945947:ℝ)/33751040)/ClassicalSixthBranch.v ((109945947:ℝ)/33751040) = (532400119159:ℝ)/245709727608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3642
  · change lowerPayment 3643 ≤ lowerValue ((point 2 split 4096 3643+point 2 split 4096 3644)/2)
    have hp : lowerPayment 3643 = (379805594929:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3643+point 2 split 4096 3644)/2 = (549787997:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((549787997:ℝ)/168755200)/ClassicalSixthBranch.v ((549787997:ℝ)/168755200) = (106464561097:ℝ)/49132343944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3643
  · change lowerPayment 3644 ≤ lowerValue ((point 2 split 4096 3644+point 2 split 4096 3645)/2)
    have hp : lowerPayment 3644 = (379900135886:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3644+point 2 split 4096 3645)/2 = (549846259:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((549846259:ℝ)/168755200)/ClassicalSixthBranch.v ((549846259:ℝ)/168755200) = (532245491811:ℝ)/245613711832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3644
  · change lowerPayment 3645 ≤ lowerValue ((point 2 split 4096 3645+point 2 split 4096 3646)/2)
    have hp : lowerPayment 3645 = (379994691130:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3645+point 2 split 4096 3646)/2 = (549904521:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((549904521:ℝ)/168755200)/ClassicalSixthBranch.v ((549904521:ℝ)/168755200) = (532168178137:ℝ)/245565703944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3645
  · change lowerPayment 3646 ≤ lowerValue ((point 2 split 4096 3646+point 2 split 4096 3647)/2)
    have hp : lowerPayment 3646 = (380089260678:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3646+point 2 split 4096 3647)/2 = (549962783:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((549962783:ℝ)/168755200)/ClassicalSixthBranch.v ((549962783:ℝ)/168755200) = (532090864463:ℝ)/245517696056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3646
  · change lowerPayment 3647 ≤ lowerValue ((point 2 split 4096 3647+point 2 split 4096 3648)/2)
    have hp : lowerPayment 3647 = (380183844545:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3647+point 2 split 4096 3648)/2 = (110004209:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((110004209:ℝ)/33751040)/ClassicalSixthBranch.v ((110004209:ℝ)/33751040) = (532013550789:ℝ)/245469688168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3647
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_227
