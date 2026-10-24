import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints120
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_120 (j : Fin 16) : lowerPayment (16*120+j.val) ≤
    lowerValue ((point 2 split 4096 (16*120+j.val)+point 2 split 4096 (16*120+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1920 ≤ lowerValue ((point 2 split 4096 1920+point 2 split 4096 1921)/2)
    have hp : lowerPayment 1920 = (225393035091:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1920+point 2 split 4096 1921)/2 = (449402571:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((449402571:ℝ)/168755200)/ClassicalSixthBranch.v ((449402571:ℝ)/168755200) = (665534265787:ℝ)/328379310744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1920
  · change lowerPayment 1921 ≤ lowerValue ((point 2 split 4096 1921+point 2 split 4096 1922)/2)
    have hp : lowerPayment 1921 = (225484972163:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1921+point 2 split 4096 1922)/2 = (449460833:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((449460833:ℝ)/168755200)/ClassicalSixthBranch.v ((449460833:ℝ)/168755200) = (665456952113:ℝ)/328331302856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1921
  · change lowerPayment 1922 ≤ lowerValue ((point 2 split 4096 1922+point 2 split 4096 1923)/2)
    have hp : lowerPayment 1922 = (225576897714:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1922+point 2 split 4096 1923)/2 = (89903819:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((89903819:ℝ)/33751040)/ClassicalSixthBranch.v ((89903819:ℝ)/33751040) = (665379638439:ℝ)/328283294968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1922
  · change lowerPayment 1923 ≤ lowerValue ((point 2 split 4096 1923+point 2 split 4096 1924)/2)
    have hp : lowerPayment 1923 = (225668811760:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1923+point 2 split 4096 1924)/2 = (449577357:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((449577357:ℝ)/168755200)/ClassicalSixthBranch.v ((449577357:ℝ)/168755200) = (133060464953:ℝ)/65647057416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1923
  · change lowerPayment 1924 ≤ lowerValue ((point 2 split 4096 1924+point 2 split 4096 1925)/2)
    have hp : lowerPayment 1924 = (225760714319:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1924+point 2 split 4096 1925)/2 = (449635619:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((449635619:ℝ)/168755200)/ClassicalSixthBranch.v ((449635619:ℝ)/168755200) = (665225011091:ℝ)/328187279192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1924
  · change lowerPayment 1925 ≤ lowerValue ((point 2 split 4096 1925+point 2 split 4096 1926)/2)
    have hp : lowerPayment 1925 = (225852605407:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1925+point 2 split 4096 1926)/2 = (449693881:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((449693881:ℝ)/168755200)/ClassicalSixthBranch.v ((449693881:ℝ)/168755200) = (665147697417:ℝ)/328139271304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1925
  · change lowerPayment 1926 ≤ lowerValue ((point 2 split 4096 1926+point 2 split 4096 1927)/2)
    have hp : lowerPayment 1926 = (225944485043:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1926+point 2 split 4096 1927)/2 = (449752143:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((449752143:ℝ)/168755200)/ClassicalSixthBranch.v ((449752143:ℝ)/168755200) = (665070383743:ℝ)/328091263416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1926
  · change lowerPayment 1927 ≤ lowerValue ((point 2 split 4096 1927+point 2 split 4096 1928)/2)
    have hp : lowerPayment 1927 = (226036353244:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1927+point 2 split 4096 1928)/2 = (89962081:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((89962081:ℝ)/33751040)/ClassicalSixthBranch.v ((89962081:ℝ)/33751040) = (664993070069:ℝ)/328043255528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1927
  · change lowerPayment 1928 ≤ lowerValue ((point 2 split 4096 1928+point 2 split 4096 1929)/2)
    have hp : lowerPayment 1928 = (226128210026:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1928+point 2 split 4096 1929)/2 = (449868667:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((449868667:ℝ)/168755200)/ClassicalSixthBranch.v ((449868667:ℝ)/168755200) = (132983151279:ℝ)/65599049528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1928
  · change lowerPayment 1929 ≤ lowerValue ((point 2 split 4096 1929+point 2 split 4096 1930)/2)
    have hp : lowerPayment 1929 = (226220055406:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1929+point 2 split 4096 1930)/2 = (449926929:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((449926929:ℝ)/168755200)/ClassicalSixthBranch.v ((449926929:ℝ)/168755200) = (1321746407:ℝ)/651982584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1929
  · change lowerPayment 1930 ≤ lowerValue ((point 2 split 4096 1930+point 2 split 4096 1931)/2)
    have hp : lowerPayment 1930 = (226311889403:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1930+point 2 split 4096 1931)/2 = (449985191:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((449985191:ℝ)/168755200)/ClassicalSixthBranch.v ((449985191:ℝ)/168755200) = (664761129047:ℝ)/327899231864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1930
  · change lowerPayment 1931 ≤ lowerValue ((point 2 split 4096 1931+point 2 split 4096 1932)/2)
    have hp : lowerPayment 1931 = (226403712033:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1931+point 2 split 4096 1932)/2 = (450043453:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((450043453:ℝ)/168755200)/ClassicalSixthBranch.v ((450043453:ℝ)/168755200) = (664683815373:ℝ)/327851223976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1931
  · change lowerPayment 1932 ≤ lowerValue ((point 2 split 4096 1932+point 2 split 4096 1933)/2)
    have hp : lowerPayment 1932 = (226495523313:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1932+point 2 split 4096 1933)/2 = (90020343:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((90020343:ℝ)/33751040)/ClassicalSixthBranch.v ((90020343:ℝ)/33751040) = (664606501699:ℝ)/327803216088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1932
  · change lowerPayment 1933 ≤ lowerValue ((point 2 split 4096 1933+point 2 split 4096 1934)/2)
    have hp : lowerPayment 1933 = (226587323261:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1933+point 2 split 4096 1934)/2 = (450159977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((450159977:ℝ)/168755200)/ClassicalSixthBranch.v ((450159977:ℝ)/168755200) = (26581167521:ℝ)/13110208328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1933
  · change lowerPayment 1934 ≤ lowerValue ((point 2 split 4096 1934+point 2 split 4096 1935)/2)
    have hp : lowerPayment 1934 = (226679111894:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1934+point 2 split 4096 1935)/2 = (450218239:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((450218239:ℝ)/168755200)/ClassicalSixthBranch.v ((450218239:ℝ)/168755200) = (664451874351:ℝ)/327707200312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1934
  · change lowerPayment 1935 ≤ lowerValue ((point 2 split 4096 1935+point 2 split 4096 1936)/2)
    have hp : lowerPayment 1935 = (226770889229:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1935+point 2 split 4096 1936)/2 = (450276501:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((450276501:ℝ)/168755200)/ClassicalSixthBranch.v ((450276501:ℝ)/168755200) = (664374560677:ℝ)/327659192424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1935
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_120
