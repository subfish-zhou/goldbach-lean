import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints121
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_121 (j : Fin 16) : upperPayment (16*121+j.val) ≤
    upperValue ((point split endpoint 4096 (16*121+j.val)+point split endpoint 4096 (16*121+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1936 ≤ upperValue ((point split endpoint 4096 1936+point split endpoint 4096 1937)/2)
    have hp : upperPayment 1936 = (280231282743:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1936+point split endpoint 4096 1937)/2 = (624854527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624854527:ℝ)/168755200)*ClassicalSixthBranch.v ((624854527:ℝ)/168755200)/ClassicalSixthBranch.r = (116380469957265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1936
  · change upperPayment 1937 ≤ upperValue ((point split endpoint 4096 1937+point split endpoint 4096 1938)/2)
    have hp : upperPayment 1937 = (280134407721:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1937+point split endpoint 4096 1938)/2 = (624879677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624879677:ℝ)/168755200)*ClassicalSixthBranch.v ((624879677:ℝ)/168755200)/ClassicalSixthBranch.r = (116358373267865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1937
  · change upperPayment 1938 ≤ upperValue ((point split endpoint 4096 1938+point split endpoint 4096 1939)/2)
    have hp : upperPayment 1938 = (280037506800:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1938+point split endpoint 4096 1939)/2 = (624904827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624904827:ℝ)/168755200)*ClassicalSixthBranch.v ((624904827:ℝ)/168755200)/ClassicalSixthBranch.r = (116336278602537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1938
  · change upperPayment 1939 ≤ upperValue ((point split endpoint 4096 1939+point split endpoint 4096 1940)/2)
    have hp : upperPayment 1939 = (279940579976:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1939+point split endpoint 4096 1940)/2 = (624929977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624929977:ℝ)/168755200)*ClassicalSixthBranch.v ((624929977:ℝ)/168755200)/ClassicalSixthBranch.r = (116314185961281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1939
  · change upperPayment 1940 ≤ upperValue ((point split endpoint 4096 1940+point split endpoint 4096 1941)/2)
    have hp : upperPayment 1940 = (279843627242:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1940+point split endpoint 4096 1941)/2 = (624955127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624955127:ℝ)/168755200)*ClassicalSixthBranch.v ((624955127:ℝ)/168755200)/ClassicalSixthBranch.r = (116292095344097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1940
  · change upperPayment 1941 ≤ upperValue ((point split endpoint 4096 1941+point split endpoint 4096 1942)/2)
    have hp : upperPayment 1941 = (279746648595:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1941+point split endpoint 4096 1942)/2 = (624980277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624980277:ℝ)/168755200)*ClassicalSixthBranch.v ((624980277:ℝ)/168755200)/ClassicalSixthBranch.r = (116270006750985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1941
  · change upperPayment 1942 ≤ upperValue ((point split endpoint 4096 1942+point split endpoint 4096 1943)/2)
    have hp : upperPayment 1942 = (279649644029:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1942+point split endpoint 4096 1943)/2 = (625005427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625005427:ℝ)/168755200)*ClassicalSixthBranch.v ((625005427:ℝ)/168755200)/ClassicalSixthBranch.r = (116247920181945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1942
  · change upperPayment 1943 ≤ upperValue ((point split endpoint 4096 1943+point split endpoint 4096 1944)/2)
    have hp : upperPayment 1943 = (279552613538:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1943+point split endpoint 4096 1944)/2 = (625030577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625030577:ℝ)/168755200)*ClassicalSixthBranch.v ((625030577:ℝ)/168755200)/ClassicalSixthBranch.r = (116225835636977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1943
  · change upperPayment 1944 ≤ upperValue ((point split endpoint 4096 1944+point split endpoint 4096 1945)/2)
    have hp : upperPayment 1944 = (279455557119:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1944+point split endpoint 4096 1945)/2 = (625055727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625055727:ℝ)/168755200)*ClassicalSixthBranch.v ((625055727:ℝ)/168755200)/ClassicalSixthBranch.r = (116203753116081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1944
  · change upperPayment 1945 ≤ upperValue ((point split endpoint 4096 1945+point split endpoint 4096 1946)/2)
    have hp : upperPayment 1945 = (279358474765:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1945+point split endpoint 4096 1946)/2 = (625080877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625080877:ℝ)/168755200)*ClassicalSixthBranch.v ((625080877:ℝ)/168755200)/ClassicalSixthBranch.r = (116181672619257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1945
  · change upperPayment 1946 ≤ upperValue ((point split endpoint 4096 1946+point split endpoint 4096 1947)/2)
    have hp : upperPayment 1946 = (279261366472:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1946+point split endpoint 4096 1947)/2 = (625106027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625106027:ℝ)/168755200)*ClassicalSixthBranch.v ((625106027:ℝ)/168755200)/ClassicalSixthBranch.r = (116159594146505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1946
  · change upperPayment 1947 ≤ upperValue ((point split endpoint 4096 1947+point split endpoint 4096 1948)/2)
    have hp : upperPayment 1947 = (279164232235:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1947+point split endpoint 4096 1948)/2 = (625131177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625131177:ℝ)/168755200)*ClassicalSixthBranch.v ((625131177:ℝ)/168755200)/ClassicalSixthBranch.r = (116137517697825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1947
  · change upperPayment 1948 ≤ upperValue ((point split endpoint 4096 1948+point split endpoint 4096 1949)/2)
    have hp : upperPayment 1948 = (279067072049:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1948+point split endpoint 4096 1949)/2 = (625156327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625156327:ℝ)/168755200)*ClassicalSixthBranch.v ((625156327:ℝ)/168755200)/ClassicalSixthBranch.r = (116115443273217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1948
  · change upperPayment 1949 ≤ upperValue ((point split endpoint 4096 1949+point split endpoint 4096 1950)/2)
    have hp : upperPayment 1949 = (278969885908:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1949+point split endpoint 4096 1950)/2 = (625181477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625181477:ℝ)/168755200)*ClassicalSixthBranch.v ((625181477:ℝ)/168755200)/ClassicalSixthBranch.r = (116093370872681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1949
  · change upperPayment 1950 ≤ upperValue ((point split endpoint 4096 1950+point split endpoint 4096 1951)/2)
    have hp : upperPayment 1950 = (278872673807:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1950+point split endpoint 4096 1951)/2 = (625206627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625206627:ℝ)/168755200)*ClassicalSixthBranch.v ((625206627:ℝ)/168755200)/ClassicalSixthBranch.r = (116071300496217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1950
  · change upperPayment 1951 ≤ upperValue ((point split endpoint 4096 1951+point split endpoint 4096 1952)/2)
    have hp : upperPayment 1951 = (278775435742:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1951+point split endpoint 4096 1952)/2 = (625231777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625231777:ℝ)/168755200)*ClassicalSixthBranch.v ((625231777:ℝ)/168755200)/ClassicalSixthBranch.r = (116049232143825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1951
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_121
