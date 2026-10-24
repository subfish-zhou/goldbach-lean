import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints240
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_240 (j : Fin 16) : lowerPayment (16*240+j.val) ≤
    lowerValue ((point 2 split 4096 (16*240+j.val)+point 2 split 4096 (16*240+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3840 ≤ lowerValue ((point 2 split 4096 3840+point 2 split 4096 3841)/2)
    have hp : lowerPayment 3840 = (398726761101:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3840+point 2 split 4096 3841)/2 = (561265611:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((561265611:ℝ)/168755200)/ClassicalSixthBranch.v ((561265611:ℝ)/168755200) = (517092011707:ℝ)/236204165784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3840
  · change lowerPayment 3841 ≤ lowerValue ((point 2 split 4096 3841+point 2 split 4096 3842)/2)
    have hp : lowerPayment 3841 = (398824438223:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3841+point 2 split 4096 3842)/2 = (561323873:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((561323873:ℝ)/168755200)/ClassicalSixthBranch.v ((561323873:ℝ)/168755200) = (517014698033:ℝ)/236156157896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3841
  · change lowerPayment 3842 ≤ lowerValue ((point 2 split 4096 3842+point 2 split 4096 3843)/2)
    have hp : lowerPayment 3842 = (398922132957:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3842+point 2 split 4096 3843)/2 = (112276427:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((112276427:ℝ)/33751040)/ClassicalSixthBranch.v ((112276427:ℝ)/33751040) = (516937384359:ℝ)/236108150008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3842
  · change lowerPayment 3843 ≤ lowerValue ((point 2 split 4096 3843+point 2 split 4096 3844)/2)
    have hp : lowerPayment 3843 = (399019845321:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3843+point 2 split 4096 3844)/2 = (561440397:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((561440397:ℝ)/168755200)/ClassicalSixthBranch.v ((561440397:ℝ)/168755200) = (103372014137:ℝ)/47212028424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3843
  · change lowerPayment 3844 ≤ lowerValue ((point 2 split 4096 3844+point 2 split 4096 3845)/2)
    have hp : lowerPayment 3844 = (399117575331:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3844+point 2 split 4096 3845)/2 = (561498659:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((561498659:ℝ)/168755200)/ClassicalSixthBranch.v ((561498659:ℝ)/168755200) = (516782757011:ℝ)/236012134232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3844
  · change lowerPayment 3845 ≤ lowerValue ((point 2 split 4096 3845+point 2 split 4096 3846)/2)
    have hp : lowerPayment 3845 = (399215323007:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3845+point 2 split 4096 3846)/2 = (561556921:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((561556921:ℝ)/168755200)/ClassicalSixthBranch.v ((561556921:ℝ)/168755200) = (516705443337:ℝ)/235964126344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3845
  · change lowerPayment 3846 ≤ lowerValue ((point 2 split 4096 3846+point 2 split 4096 3847)/2)
    have hp : lowerPayment 3846 = (399313088364:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3846+point 2 split 4096 3847)/2 = (561615183:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((561615183:ℝ)/168755200)/ClassicalSixthBranch.v ((561615183:ℝ)/168755200) = (516628129663:ℝ)/235916118456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3846
  · change lowerPayment 3847 ≤ lowerValue ((point 2 split 4096 3847+point 2 split 4096 3848)/2)
    have hp : lowerPayment 3847 = (399410871422:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3847+point 2 split 4096 3848)/2 = (112334689:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((112334689:ℝ)/33751040)/ClassicalSixthBranch.v ((112334689:ℝ)/33751040) = (516550815989:ℝ)/235868110568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3847
  · change lowerPayment 3848 ≤ lowerValue ((point 2 split 4096 3848+point 2 split 4096 3849)/2)
    have hp : lowerPayment 3848 = (399508672196:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3848+point 2 split 4096 3849)/2 = (561731707:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((561731707:ℝ)/168755200)/ClassicalSixthBranch.v ((561731707:ℝ)/168755200) = (103294700463:ℝ)/47164020536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3848
  · change lowerPayment 3849 ≤ lowerValue ((point 2 split 4096 3849+point 2 split 4096 3850)/2)
    have hp : lowerPayment 3849 = (399606490706:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3849+point 2 split 4096 3850)/2 = (561789969:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((561789969:ℝ)/168755200)/ClassicalSixthBranch.v ((561789969:ℝ)/168755200) = (516396188641:ℝ)/235772094792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3849
  · change lowerPayment 3850 ≤ lowerValue ((point 2 split 4096 3850+point 2 split 4096 3851)/2)
    have hp : lowerPayment 3850 = (399704326969:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3850+point 2 split 4096 3851)/2 = (561848231:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((561848231:ℝ)/168755200)/ClassicalSixthBranch.v ((561848231:ℝ)/168755200) = (516318874967:ℝ)/235724086904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3850
  · change lowerPayment 3851 ≤ lowerValue ((point 2 split 4096 3851+point 2 split 4096 3852)/2)
    have hp : lowerPayment 3851 = (399802181002:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3851+point 2 split 4096 3852)/2 = (561906493:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((561906493:ℝ)/168755200)/ClassicalSixthBranch.v ((561906493:ℝ)/168755200) = (516241561293:ℝ)/235676079016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3851
  · change lowerPayment 3852 ≤ lowerValue ((point 2 split 4096 3852+point 2 split 4096 3853)/2)
    have hp : lowerPayment 3852 = (399900052823:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3852+point 2 split 4096 3853)/2 = (112392951:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((112392951:ℝ)/33751040)/ClassicalSixthBranch.v ((112392951:ℝ)/33751040) = (516164247619:ℝ)/235628071128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3852
  · change lowerPayment 3853 ≤ lowerValue ((point 2 split 4096 3853+point 2 split 4096 3854)/2)
    have hp : lowerPayment 3853 = (399997942450:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3853+point 2 split 4096 3854)/2 = (562023017:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((562023017:ℝ)/168755200)/ClassicalSixthBranch.v ((562023017:ℝ)/168755200) = (103217386789:ℝ)/47116012648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3853
  · change lowerPayment 3854 ≤ lowerValue ((point 2 split 4096 3854+point 2 split 4096 3855)/2)
    have hp : lowerPayment 3854 = (400095849899:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3854+point 2 split 4096 3855)/2 = (562081279:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((562081279:ℝ)/168755200)/ClassicalSixthBranch.v ((562081279:ℝ)/168755200) = (516009620271:ℝ)/235532055352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3854
  · change lowerPayment 3855 ≤ lowerValue ((point 2 split 4096 3855+point 2 split 4096 3856)/2)
    have hp : lowerPayment 3855 = (400193775190:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3855+point 2 split 4096 3856)/2 = (562139541:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((562139541:ℝ)/168755200)/ClassicalSixthBranch.v ((562139541:ℝ)/168755200) = (515932306597:ℝ)/235484047464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3855
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_240
