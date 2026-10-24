import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints116
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_116 (j : Fin 16) : lowerPayment (16*116+j.val) ≤
    lowerValue ((point 2 split 4096 (16*116+j.val)+point 2 split 4096 (16*116+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1856 ≤ lowerValue ((point 2 split 4096 1856+point 2 split 4096 1857)/2)
    have hp : lowerPayment 1856 = (219484302170:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1856+point 2 split 4096 1857)/2 = (445673803:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((445673803:ℝ)/168755200)/ClassicalSixthBranch.v ((445673803:ℝ)/168755200) = (670482340923:ℝ)/331451815576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1856
  · change lowerPayment 1857 ≤ lowerValue ((point 2 split 4096 1857+point 2 split 4096 1858)/2)
    have hp : lowerPayment 1857 = (219577012853:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1857+point 2 split 4096 1858)/2 = (89146413:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((89146413:ℝ)/33751040)/ClassicalSixthBranch.v ((89146413:ℝ)/33751040) = (670405027249:ℝ)/331403807688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1857
  · change lowerPayment 1858 ≤ lowerValue ((point 2 split 4096 1858+point 2 split 4096 1859)/2)
    have hp : lowerPayment 1858 = (219669710895:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1858+point 2 split 4096 1859)/2 = (445790327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((445790327:ℝ)/168755200)/ClassicalSixthBranch.v ((445790327:ℝ)/168755200) = (26813108543:ℝ)/13254231992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1858
  · change lowerPayment 1859 ≤ lowerValue ((point 2 split 4096 1859+point 2 split 4096 1860)/2)
    have hp : lowerPayment 1859 = (219762396314:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1859+point 2 split 4096 1860)/2 = (445848589:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((445848589:ℝ)/168755200)/ClassicalSixthBranch.v ((445848589:ℝ)/168755200) = (670250399901:ℝ)/331307791912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1859
  · change lowerPayment 1860 ≤ lowerValue ((point 2 split 4096 1860+point 2 split 4096 1861)/2)
    have hp : lowerPayment 1860 = (219855069127:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1860+point 2 split 4096 1861)/2 = (445906851:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((445906851:ℝ)/168755200)/ClassicalSixthBranch.v ((445906851:ℝ)/168755200) = (670173086227:ℝ)/331259784024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1860
  · change lowerPayment 1861 ≤ lowerValue ((point 2 split 4096 1861+point 2 split 4096 1862)/2)
    have hp : lowerPayment 1861 = (219947729352:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1861+point 2 split 4096 1862)/2 = (445965113:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((445965113:ℝ)/168755200)/ClassicalSixthBranch.v ((445965113:ℝ)/168755200) = (670095772553:ℝ)/331211776136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1861
  · change lowerPayment 1862 ≤ lowerValue ((point 2 split 4096 1862+point 2 split 4096 1863)/2)
    have hp : lowerPayment 1862 = (220040377007:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1862+point 2 split 4096 1863)/2 = (17840935:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((17840935:ℝ)/6750208)/ClassicalSixthBranch.v ((17840935:ℝ)/6750208) = (670018458879:ℝ)/331163768248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1862
  · change lowerPayment 1863 ≤ lowerValue ((point 2 split 4096 1863+point 2 split 4096 1864)/2)
    have hp : lowerPayment 1863 = (220133012109:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1863+point 2 split 4096 1864)/2 = (446081637:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((446081637:ℝ)/168755200)/ClassicalSixthBranch.v ((446081637:ℝ)/168755200) = (133988229041:ℝ)/66223152072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1863
  · change lowerPayment 1864 ≤ lowerValue ((point 2 split 4096 1864+point 2 split 4096 1865)/2)
    have hp : lowerPayment 1864 = (220225634676:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1864+point 2 split 4096 1865)/2 = (446139899:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((446139899:ℝ)/168755200)/ClassicalSixthBranch.v ((446139899:ℝ)/168755200) = (669863831531:ℝ)/331067752472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1864
  · change lowerPayment 1865 ≤ lowerValue ((point 2 split 4096 1865+point 2 split 4096 1866)/2)
    have hp : lowerPayment 1865 = (220318244726:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1865+point 2 split 4096 1866)/2 = (446198161:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((446198161:ℝ)/168755200)/ClassicalSixthBranch.v ((446198161:ℝ)/168755200) = (669786517857:ℝ)/331019744584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1865
  · change lowerPayment 1866 ≤ lowerValue ((point 2 split 4096 1866+point 2 split 4096 1867)/2)
    have hp : lowerPayment 1866 = (220410842276:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1866+point 2 split 4096 1867)/2 = (446256423:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((446256423:ℝ)/168755200)/ClassicalSixthBranch.v ((446256423:ℝ)/168755200) = (669709204183:ℝ)/330971736696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1866
  · change lowerPayment 1867 ≤ lowerValue ((point 2 split 4096 1867+point 2 split 4096 1868)/2)
    have hp : lowerPayment 1867 = (220503427345:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1867+point 2 split 4096 1868)/2 = (89262937:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((89262937:ℝ)/33751040)/ClassicalSixthBranch.v ((89262937:ℝ)/33751040) = (669631890509:ℝ)/330923728808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1867
  · change lowerPayment 1868 ≤ lowerValue ((point 2 split 4096 1868+point 2 split 4096 1869)/2)
    have hp : lowerPayment 1868 = (220595999949:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1868+point 2 split 4096 1869)/2 = (446372947:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((446372947:ℝ)/168755200)/ClassicalSixthBranch.v ((446372947:ℝ)/168755200) = (133910915367:ℝ)/66175144184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1868
  · change lowerPayment 1869 ≤ lowerValue ((point 2 split 4096 1869+point 2 split 4096 1870)/2)
    have hp : lowerPayment 1869 = (220688560106:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1869+point 2 split 4096 1870)/2 = (446431209:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((446431209:ℝ)/168755200)/ClassicalSixthBranch.v ((446431209:ℝ)/168755200) = (669477263161:ℝ)/330827713032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1869
  · change lowerPayment 1870 ≤ lowerValue ((point 2 split 4096 1870+point 2 split 4096 1871)/2)
    have hp : lowerPayment 1870 = (220781107835:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1870+point 2 split 4096 1871)/2 = (446489471:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((446489471:ℝ)/168755200)/ClassicalSixthBranch.v ((446489471:ℝ)/168755200) = (669399949487:ℝ)/330779705144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1870
  · change lowerPayment 1871 ≤ lowerValue ((point 2 split 4096 1871+point 2 split 4096 1872)/2)
    have hp : lowerPayment 1871 = (220873643152:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1871+point 2 split 4096 1872)/2 = (446547733:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((446547733:ℝ)/168755200)/ClassicalSixthBranch.v ((446547733:ℝ)/168755200) = (669322635813:ℝ)/330731697256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1871
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_116
