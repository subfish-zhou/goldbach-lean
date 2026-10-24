import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints118
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_118 (j : Fin 16) : lowerPayment (16*118+j.val) ≤
    lowerValue ((point 2 split 4096 (16*118+j.val)+point 2 split 4096 (16*118+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1888 ≤ lowerValue ((point 2 split 4096 1888+point 2 split 4096 1889)/2)
    have hp : lowerPayment 1888 = (222444861668:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1888+point 2 split 4096 1889)/2 = (447538187:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((447538187:ℝ)/168755200)/ClassicalSixthBranch.v ((447538187:ℝ)/168755200) = (133601660671:ℝ)/65983112632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1888
  · change lowerPayment 1889 ≤ lowerValue ((point 2 split 4096 1889+point 2 split 4096 1890)/2)
    have hp : lowerPayment 1889 = (222537176589:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1889+point 2 split 4096 1890)/2 = (447596449:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((447596449:ℝ)/168755200)/ClassicalSixthBranch.v ((447596449:ℝ)/168755200) = (667930989681:ℝ)/329867555272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1889
  · change lowerPayment 1890 ≤ lowerValue ((point 2 split 4096 1890+point 2 split 4096 1891)/2)
    have hp : lowerPayment 1890 = (222629479432:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1890+point 2 split 4096 1891)/2 = (447654711:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((447654711:ℝ)/168755200)/ClassicalSixthBranch.v ((447654711:ℝ)/168755200) = (667853676007:ℝ)/329819547384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1890
  · change lowerPayment 1891 ≤ lowerValue ((point 2 split 4096 1891+point 2 split 4096 1892)/2)
    have hp : lowerPayment 1891 = (222721770216:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1891+point 2 split 4096 1892)/2 = (447712973:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((447712973:ℝ)/168755200)/ClassicalSixthBranch.v ((447712973:ℝ)/168755200) = (667776362333:ℝ)/329771539496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1891
  · change lowerPayment 1892 ≤ lowerValue ((point 2 split 4096 1892+point 2 split 4096 1893)/2)
    have hp : lowerPayment 1892 = (222814048956:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1892+point 2 split 4096 1893)/2 = (89554247:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((89554247:ℝ)/33751040)/ClassicalSixthBranch.v ((89554247:ℝ)/33751040) = (667699048659:ℝ)/329723531608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1892
  · change lowerPayment 1893 ≤ lowerValue ((point 2 split 4096 1893+point 2 split 4096 1894)/2)
    have hp : lowerPayment 1893 = (222906315671:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1893+point 2 split 4096 1894)/2 = (447829497:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((447829497:ℝ)/168755200)/ClassicalSixthBranch.v ((447829497:ℝ)/168755200) = (133524346997:ℝ)/65935104744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1893
  · change lowerPayment 1894 ≤ lowerValue ((point 2 split 4096 1894+point 2 split 4096 1895)/2)
    have hp : lowerPayment 1894 = (222998570379:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1894+point 2 split 4096 1895)/2 = (447887759:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((447887759:ℝ)/168755200)/ClassicalSixthBranch.v ((447887759:ℝ)/168755200) = (667544421311:ℝ)/329627515832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1894
  · change lowerPayment 1895 ≤ lowerValue ((point 2 split 4096 1895+point 2 split 4096 1896)/2)
    have hp : lowerPayment 1895 = (223090813096:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1895+point 2 split 4096 1896)/2 = (447946021:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((447946021:ℝ)/168755200)/ClassicalSixthBranch.v ((447946021:ℝ)/168755200) = (667467107637:ℝ)/329579507944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1895
  · change lowerPayment 1896 ≤ lowerValue ((point 2 split 4096 1896+point 2 split 4096 1897)/2)
    have hp : lowerPayment 1896 = (223183043841:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1896+point 2 split 4096 1897)/2 = (448004283:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((448004283:ℝ)/168755200)/ClassicalSixthBranch.v ((448004283:ℝ)/168755200) = (667389793963:ℝ)/329531500056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1896
  · change lowerPayment 1897 ≤ lowerValue ((point 2 split 4096 1897+point 2 split 4096 1898)/2)
    have hp : lowerPayment 1897 = (223275262630:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1897+point 2 split 4096 1898)/2 = (89612509:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((89612509:ℝ)/33751040)/ClassicalSixthBranch.v ((89612509:ℝ)/33751040) = (667312480289:ℝ)/329483492168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1897
  · change lowerPayment 1898 ≤ lowerValue ((point 2 split 4096 1898+point 2 split 4096 1899)/2)
    have hp : lowerPayment 1898 = (223367469481:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1898+point 2 split 4096 1899)/2 = (448120807:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((448120807:ℝ)/168755200)/ClassicalSixthBranch.v ((448120807:ℝ)/168755200) = (133447033323:ℝ)/65887096856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1898
  · change lowerPayment 1899 ≤ lowerValue ((point 2 split 4096 1899+point 2 split 4096 1900)/2)
    have hp : lowerPayment 1899 = (223459664411:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1899+point 2 split 4096 1900)/2 = (448179069:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((448179069:ℝ)/168755200)/ClassicalSixthBranch.v ((448179069:ℝ)/168755200) = (667157852941:ℝ)/329387476392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1899
  · change lowerPayment 1900 ≤ lowerValue ((point 2 split 4096 1900+point 2 split 4096 1901)/2)
    have hp : lowerPayment 1900 = (223551847439:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1900+point 2 split 4096 1901)/2 = (448237331:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((448237331:ℝ)/168755200)/ClassicalSixthBranch.v ((448237331:ℝ)/168755200) = (667080539267:ℝ)/329339468504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1900
  · change lowerPayment 1901 ≤ lowerValue ((point 2 split 4096 1901+point 2 split 4096 1902)/2)
    have hp : lowerPayment 1901 = (223644018581:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1901+point 2 split 4096 1902)/2 = (448295593:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((448295593:ℝ)/168755200)/ClassicalSixthBranch.v ((448295593:ℝ)/168755200) = (667003225593:ℝ)/329291460616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1901
  · change lowerPayment 1902 ≤ lowerValue ((point 2 split 4096 1902+point 2 split 4096 1903)/2)
    have hp : lowerPayment 1902 = (223736177854:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1902+point 2 split 4096 1903)/2 = (89670771:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((89670771:ℝ)/33751040)/ClassicalSixthBranch.v ((89670771:ℝ)/33751040) = (666925911919:ℝ)/329243452728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1902
  · change lowerPayment 1903 ≤ lowerValue ((point 2 split 4096 1903+point 2 split 4096 1904)/2)
    have hp : lowerPayment 1903 = (223828325276:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1903+point 2 split 4096 1904)/2 = (448412117:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((448412117:ℝ)/168755200)/ClassicalSixthBranch.v ((448412117:ℝ)/168755200) = (133369719649:ℝ)/65839088968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1903
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_118
