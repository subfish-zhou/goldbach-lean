import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints121
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_121 (j : Fin 16) : lowerPayment (16*121+j.val) ≤
    lowerValue ((point 2 split 4096 (16*121+j.val)+point 2 split 4096 (16*121+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1936 ≤ lowerValue ((point 2 split 4096 1936+point 2 split 4096 1937)/2)
    have hp : lowerPayment 1936 = (226862655282:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1936+point 2 split 4096 1937)/2 = (450334763:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((450334763:ℝ)/168755200)/ClassicalSixthBranch.v ((450334763:ℝ)/168755200) = (664297247003:ℝ)/327611184536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1936
  · change lowerPayment 1937 ≤ lowerValue ((point 2 split 4096 1937+point 2 split 4096 1938)/2)
    have hp : lowerPayment 1937 = (226954410072:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1937+point 2 split 4096 1938)/2 = (18015721:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((18015721:ℝ)/6750208)/ClassicalSixthBranch.v ((18015721:ℝ)/6750208) = (664219933329:ℝ)/327563176648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1937
  · change lowerPayment 1938 ≤ lowerValue ((point 2 split 4096 1938+point 2 split 4096 1939)/2)
    have hp : lowerPayment 1938 = (227046153615:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1938+point 2 split 4096 1939)/2 = (450451287:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((450451287:ℝ)/168755200)/ClassicalSixthBranch.v ((450451287:ℝ)/168755200) = (132828523931:ℝ)/65503033752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1938
  · change lowerPayment 1939 ≤ lowerValue ((point 2 split 4096 1939+point 2 split 4096 1940)/2)
    have hp : lowerPayment 1939 = (227137885929:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1939+point 2 split 4096 1940)/2 = (450509549:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((450509549:ℝ)/168755200)/ClassicalSixthBranch.v ((450509549:ℝ)/168755200) = (664065305981:ℝ)/327467160872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1939
  · change lowerPayment 1940 ≤ lowerValue ((point 2 split 4096 1940+point 2 split 4096 1941)/2)
    have hp : lowerPayment 1940 = (227229607030:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1940+point 2 split 4096 1941)/2 = (450567811:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((450567811:ℝ)/168755200)/ClassicalSixthBranch.v ((450567811:ℝ)/168755200) = (663987992307:ℝ)/327419152984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1940
  · change lowerPayment 1941 ≤ lowerValue ((point 2 split 4096 1941+point 2 split 4096 1942)/2)
    have hp : lowerPayment 1941 = (227321316936:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1941+point 2 split 4096 1942)/2 = (450626073:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((450626073:ℝ)/168755200)/ClassicalSixthBranch.v ((450626073:ℝ)/168755200) = (663910678633:ℝ)/327371145096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1941
  · change lowerPayment 1942 ≤ lowerValue ((point 2 split 4096 1942+point 2 split 4096 1943)/2)
    have hp : lowerPayment 1942 = (227413015664:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1942+point 2 split 4096 1943)/2 = (90136867:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((90136867:ℝ)/33751040)/ClassicalSixthBranch.v ((90136867:ℝ)/33751040) = (663833364959:ℝ)/327323137208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1942
  · change lowerPayment 1943 ≤ lowerValue ((point 2 split 4096 1943+point 2 split 4096 1944)/2)
    have hp : lowerPayment 1943 = (227504703231:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1943+point 2 split 4096 1944)/2 = (450742597:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((450742597:ℝ)/168755200)/ClassicalSixthBranch.v ((450742597:ℝ)/168755200) = (132751210257:ℝ)/65455025864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1943
  · change lowerPayment 1944 ≤ lowerValue ((point 2 split 4096 1944+point 2 split 4096 1945)/2)
    have hp : lowerPayment 1944 = (227596379654:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1944+point 2 split 4096 1945)/2 = (450800859:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((450800859:ℝ)/168755200)/ClassicalSixthBranch.v ((450800859:ℝ)/168755200) = (663678737611:ℝ)/327227121432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1944
  · change lowerPayment 1945 ≤ lowerValue ((point 2 split 4096 1945+point 2 split 4096 1946)/2)
    have hp : lowerPayment 1945 = (227688044950:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1945+point 2 split 4096 1946)/2 = (450859121:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((450859121:ℝ)/168755200)/ClassicalSixthBranch.v ((450859121:ℝ)/168755200) = (663601423937:ℝ)/327179113544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1945
  · change lowerPayment 1946 ≤ lowerValue ((point 2 split 4096 1946+point 2 split 4096 1947)/2)
    have hp : lowerPayment 1946 = (227779699137:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1946+point 2 split 4096 1947)/2 = (450917383:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((450917383:ℝ)/168755200)/ClassicalSixthBranch.v ((450917383:ℝ)/168755200) = (663524110263:ℝ)/327131105656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1946
  · change lowerPayment 1947 ≤ lowerValue ((point 2 split 4096 1947+point 2 split 4096 1948)/2)
    have hp : lowerPayment 1947 = (227871342230:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1947+point 2 split 4096 1948)/2 = (90195129:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((90195129:ℝ)/33751040)/ClassicalSixthBranch.v ((90195129:ℝ)/33751040) = (663446796589:ℝ)/327083097768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1947
  · change lowerPayment 1948 ≤ lowerValue ((point 2 split 4096 1948+point 2 split 4096 1949)/2)
    have hp : lowerPayment 1948 = (227962974248:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1948+point 2 split 4096 1949)/2 = (451033907:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((451033907:ℝ)/168755200)/ClassicalSixthBranch.v ((451033907:ℝ)/168755200) = (132673896583:ℝ)/65407017976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1948
  · change lowerPayment 1949 ≤ lowerValue ((point 2 split 4096 1949+point 2 split 4096 1950)/2)
    have hp : lowerPayment 1949 = (228054595208:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1949+point 2 split 4096 1950)/2 = (451092169:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((451092169:ℝ)/168755200)/ClassicalSixthBranch.v ((451092169:ℝ)/168755200) = (663292169241:ℝ)/326987081992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1949
  · change lowerPayment 1950 ≤ lowerValue ((point 2 split 4096 1950+point 2 split 4096 1951)/2)
    have hp : lowerPayment 1950 = (228146205126:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1950+point 2 split 4096 1951)/2 = (451150431:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((451150431:ℝ)/168755200)/ClassicalSixthBranch.v ((451150431:ℝ)/168755200) = (663214855567:ℝ)/326939074104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1950
  · change lowerPayment 1951 ≤ lowerValue ((point 2 split 4096 1951+point 2 split 4096 1952)/2)
    have hp : lowerPayment 1951 = (228237804019:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1951+point 2 split 4096 1952)/2 = (451208693:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((451208693:ℝ)/168755200)/ClassicalSixthBranch.v ((451208693:ℝ)/168755200) = (663137541893:ℝ)/326891066216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1951
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_121
