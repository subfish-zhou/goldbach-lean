import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints114
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_114 (j : Fin 16) : lowerPayment (16*114+j.val) ≤
    lowerValue ((point 2 split 4096 (16*114+j.val)+point 2 split 4096 (16*114+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1824 ≤ lowerValue ((point 2 split 4096 1824+point 2 split 4096 1825)/2)
    have hp : lowerPayment 1824 = (216510779206:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1824+point 2 split 4096 1825)/2 = (443809419:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((443809419:ℝ)/168755200)/ClassicalSixthBranch.v ((443809419:ℝ)/168755200) = (672956378491:ℝ)/332988067992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1824
  · change lowerPayment 1825 ≤ lowerValue ((point 2 split 4096 1825+point 2 split 4096 1826)/2)
    have hp : lowerPayment 1825 = (216603903819:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1825+point 2 split 4096 1826)/2 = (443867681:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((443867681:ℝ)/168755200)/ClassicalSixthBranch.v ((443867681:ℝ)/168755200) = (672879064817:ℝ)/332940060104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1825
  · change lowerPayment 1826 ≤ lowerValue ((point 2 split 4096 1826+point 2 split 4096 1827)/2)
    have hp : lowerPayment 1826 = (216697015219:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1826+point 2 split 4096 1827)/2 = (443925943:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((443925943:ℝ)/168755200)/ClassicalSixthBranch.v ((443925943:ℝ)/168755200) = (672801751143:ℝ)/332892052216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1826
  · change lowerPayment 1827 ≤ lowerValue ((point 2 split 4096 1827+point 2 split 4096 1828)/2)
    have hp : lowerPayment 1827 = (216790113424:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1827+point 2 split 4096 1828)/2 = (88796841:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((88796841:ℝ)/33751040)/ClassicalSixthBranch.v ((88796841:ℝ)/33751040) = (672724437469:ℝ)/332844044328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1827
  · change lowerPayment 1828 ≤ lowerValue ((point 2 split 4096 1828+point 2 split 4096 1829)/2)
    have hp : lowerPayment 1828 = (216883198452:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1828+point 2 split 4096 1829)/2 = (444042467:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((444042467:ℝ)/168755200)/ClassicalSixthBranch.v ((444042467:ℝ)/168755200) = (134529424759:ℝ)/66559207288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1828
  · change lowerPayment 1829 ≤ lowerValue ((point 2 split 4096 1829+point 2 split 4096 1830)/2)
    have hp : lowerPayment 1829 = (216976270321:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1829+point 2 split 4096 1830)/2 = (444100729:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((444100729:ℝ)/168755200)/ClassicalSixthBranch.v ((444100729:ℝ)/168755200) = (672569810121:ℝ)/332748028552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1829
  · change lowerPayment 1830 ≤ lowerValue ((point 2 split 4096 1830+point 2 split 4096 1831)/2)
    have hp : lowerPayment 1830 = (217069329050:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1830+point 2 split 4096 1831)/2 = (444158991:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((444158991:ℝ)/168755200)/ClassicalSixthBranch.v ((444158991:ℝ)/168755200) = (672492496447:ℝ)/332700020664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1830
  · change lowerPayment 1831 ≤ lowerValue ((point 2 split 4096 1831+point 2 split 4096 1832)/2)
    have hp : lowerPayment 1831 = (217162374655:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1831+point 2 split 4096 1832)/2 = (444217253:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((444217253:ℝ)/168755200)/ClassicalSixthBranch.v ((444217253:ℝ)/168755200) = (672415182773:ℝ)/332652012776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1831
  · change lowerPayment 1832 ≤ lowerValue ((point 2 split 4096 1832+point 2 split 4096 1833)/2)
    have hp : lowerPayment 1832 = (217255407155:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1832+point 2 split 4096 1833)/2 = (88855103:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((88855103:ℝ)/33751040)/ClassicalSixthBranch.v ((88855103:ℝ)/33751040) = (672337869099:ℝ)/332604004888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1832
  · change lowerPayment 1833 ≤ lowerValue ((point 2 split 4096 1833+point 2 split 4096 1834)/2)
    have hp : lowerPayment 1833 = (217348426568:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1833+point 2 split 4096 1834)/2 = (444333777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((444333777:ℝ)/168755200)/ClassicalSixthBranch.v ((444333777:ℝ)/168755200) = (26890422217:ℝ)/13302239880 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1833
  · change lowerPayment 1834 ≤ lowerValue ((point 2 split 4096 1834+point 2 split 4096 1835)/2)
    have hp : lowerPayment 1834 = (217441432912:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1834+point 2 split 4096 1835)/2 = (444392039:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((444392039:ℝ)/168755200)/ClassicalSixthBranch.v ((444392039:ℝ)/168755200) = (672183241751:ℝ)/332507989112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1834
  · change lowerPayment 1835 ≤ lowerValue ((point 2 split 4096 1835+point 2 split 4096 1836)/2)
    have hp : lowerPayment 1835 = (217534426205:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1835+point 2 split 4096 1836)/2 = (444450301:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((444450301:ℝ)/168755200)/ClassicalSixthBranch.v ((444450301:ℝ)/168755200) = (672105928077:ℝ)/332459981224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1835
  · change lowerPayment 1836 ≤ lowerValue ((point 2 split 4096 1836+point 2 split 4096 1837)/2)
    have hp : lowerPayment 1836 = (217627406464:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1836+point 2 split 4096 1837)/2 = (444508563:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((444508563:ℝ)/168755200)/ClassicalSixthBranch.v ((444508563:ℝ)/168755200) = (672028614403:ℝ)/332411973336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1836
  · change lowerPayment 1837 ≤ lowerValue ((point 2 split 4096 1837+point 2 split 4096 1838)/2)
    have hp : lowerPayment 1837 = (217720373708:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1837+point 2 split 4096 1838)/2 = (17782673:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((17782673:ℝ)/6750208)/ClassicalSixthBranch.v ((17782673:ℝ)/6750208) = (671951300729:ℝ)/332363965448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1837
  · change lowerPayment 1838 ≤ lowerValue ((point 2 split 4096 1838+point 2 split 4096 1839)/2)
    have hp : lowerPayment 1838 = (217813327955:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1838+point 2 split 4096 1839)/2 = (444625087:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((444625087:ℝ)/168755200)/ClassicalSixthBranch.v ((444625087:ℝ)/168755200) = (134374797411:ℝ)/66463191512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1838
  · change lowerPayment 1839 ≤ lowerValue ((point 2 split 4096 1839+point 2 split 4096 1840)/2)
    have hp : lowerPayment 1839 = (217906269221:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1839+point 2 split 4096 1840)/2 = (444683349:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((444683349:ℝ)/168755200)/ClassicalSixthBranch.v ((444683349:ℝ)/168755200) = (671796673381:ℝ)/332267949672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1839
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_114
