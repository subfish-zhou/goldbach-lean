import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints115
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_115 (j : Fin 16) : lowerPayment (16*115+j.val) ≤
    lowerValue ((point 2 split 4096 (16*115+j.val)+point 2 split 4096 (16*115+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1840 ≤ lowerValue ((point 2 split 4096 1840+point 2 split 4096 1841)/2)
    have hp : lowerPayment 1840 = (217999197526:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1840+point 2 split 4096 1841)/2 = (444741611:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((444741611:ℝ)/168755200)/ClassicalSixthBranch.v ((444741611:ℝ)/168755200) = (671719359707:ℝ)/332219941784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1840
  · change lowerPayment 1841 ≤ lowerValue ((point 2 split 4096 1841+point 2 split 4096 1842)/2)
    have hp : lowerPayment 1841 = (218092112888:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1841+point 2 split 4096 1842)/2 = (444799873:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((444799873:ℝ)/168755200)/ClassicalSixthBranch.v ((444799873:ℝ)/168755200) = (671642046033:ℝ)/332171933896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1841
  · change lowerPayment 1842 ≤ lowerValue ((point 2 split 4096 1842+point 2 split 4096 1843)/2)
    have hp : lowerPayment 1842 = (218185015323:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1842+point 2 split 4096 1843)/2 = (88971627:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((88971627:ℝ)/33751040)/ClassicalSixthBranch.v ((88971627:ℝ)/33751040) = (671564732359:ℝ)/332123926008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1842
  · change lowerPayment 1843 ≤ lowerValue ((point 2 split 4096 1843+point 2 split 4096 1844)/2)
    have hp : lowerPayment 1843 = (218277904850:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1843+point 2 split 4096 1844)/2 = (444916397:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((444916397:ℝ)/168755200)/ClassicalSixthBranch.v ((444916397:ℝ)/168755200) = (134297483737:ℝ)/66415183624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1843
  · change lowerPayment 1844 ≤ lowerValue ((point 2 split 4096 1844+point 2 split 4096 1845)/2)
    have hp : lowerPayment 1844 = (218370781486:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1844+point 2 split 4096 1845)/2 = (444974659:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((444974659:ℝ)/168755200)/ClassicalSixthBranch.v ((444974659:ℝ)/168755200) = (671410105011:ℝ)/332027910232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1844
  · change lowerPayment 1845 ≤ lowerValue ((point 2 split 4096 1845+point 2 split 4096 1846)/2)
    have hp : lowerPayment 1845 = (218463645251:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1845+point 2 split 4096 1846)/2 = (445032921:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((445032921:ℝ)/168755200)/ClassicalSixthBranch.v ((445032921:ℝ)/168755200) = (671332791337:ℝ)/331979902344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1845
  · change lowerPayment 1846 ≤ lowerValue ((point 2 split 4096 1846+point 2 split 4096 1847)/2)
    have hp : lowerPayment 1846 = (218556496160:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1846+point 2 split 4096 1847)/2 = (445091183:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((445091183:ℝ)/168755200)/ClassicalSixthBranch.v ((445091183:ℝ)/168755200) = (671255477663:ℝ)/331931894456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1846
  · change lowerPayment 1847 ≤ lowerValue ((point 2 split 4096 1847+point 2 split 4096 1848)/2)
    have hp : lowerPayment 1847 = (218649334233:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1847+point 2 split 4096 1848)/2 = (89029889:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((89029889:ℝ)/33751040)/ClassicalSixthBranch.v ((89029889:ℝ)/33751040) = (671178163989:ℝ)/331883886568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1847
  · change lowerPayment 1848 ≤ lowerValue ((point 2 split 4096 1848+point 2 split 4096 1849)/2)
    have hp : lowerPayment 1848 = (218742159487:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1848+point 2 split 4096 1849)/2 = (445207707:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((445207707:ℝ)/168755200)/ClassicalSixthBranch.v ((445207707:ℝ)/168755200) = (134220170063:ℝ)/66367175736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1848
  · change lowerPayment 1849 ≤ lowerValue ((point 2 split 4096 1849+point 2 split 4096 1850)/2)
    have hp : lowerPayment 1849 = (218834971939:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1849+point 2 split 4096 1850)/2 = (445265969:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((445265969:ℝ)/168755200)/ClassicalSixthBranch.v ((445265969:ℝ)/168755200) = (671023536641:ℝ)/331787870792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1849
  · change lowerPayment 1850 ≤ lowerValue ((point 2 split 4096 1850+point 2 split 4096 1851)/2)
    have hp : lowerPayment 1850 = (218927771609:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1850+point 2 split 4096 1851)/2 = (445324231:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((445324231:ℝ)/168755200)/ClassicalSixthBranch.v ((445324231:ℝ)/168755200) = (670946222967:ℝ)/331739862904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1850
  · change lowerPayment 1851 ≤ lowerValue ((point 2 split 4096 1851+point 2 split 4096 1852)/2)
    have hp : lowerPayment 1851 = (219020558512:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1851+point 2 split 4096 1852)/2 = (445382493:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((445382493:ℝ)/168755200)/ClassicalSixthBranch.v ((445382493:ℝ)/168755200) = (670868909293:ℝ)/331691855016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1851
  · change lowerPayment 1852 ≤ lowerValue ((point 2 split 4096 1852+point 2 split 4096 1853)/2)
    have hp : lowerPayment 1852 = (219113332668:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1852+point 2 split 4096 1853)/2 = (89088151:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((89088151:ℝ)/33751040)/ClassicalSixthBranch.v ((89088151:ℝ)/33751040) = (670791595619:ℝ)/331643847128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1852
  · change lowerPayment 1853 ≤ lowerValue ((point 2 split 4096 1853+point 2 split 4096 1854)/2)
    have hp : lowerPayment 1853 = (219206094094:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1853+point 2 split 4096 1854)/2 = (445499017:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((445499017:ℝ)/168755200)/ClassicalSixthBranch.v ((445499017:ℝ)/168755200) = (134142856389:ℝ)/66319167848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1853
  · change lowerPayment 1854 ≤ lowerValue ((point 2 split 4096 1854+point 2 split 4096 1855)/2)
    have hp : lowerPayment 1854 = (219298842808:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1854+point 2 split 4096 1855)/2 = (445557279:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((445557279:ℝ)/168755200)/ClassicalSixthBranch.v ((445557279:ℝ)/168755200) = (670636968271:ℝ)/331547831352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1854
  · change lowerPayment 1855 ≤ lowerValue ((point 2 split 4096 1855+point 2 split 4096 1856)/2)
    have hp : lowerPayment 1855 = (219391578827:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1855+point 2 split 4096 1856)/2 = (445615541:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((445615541:ℝ)/168755200)/ClassicalSixthBranch.v ((445615541:ℝ)/168755200) = (670559654597:ℝ)/331499823464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1855
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_115
