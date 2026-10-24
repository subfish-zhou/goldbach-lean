import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints119
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_119 (j : Fin 16) : lowerPayment (16*119+j.val) ≤
    lowerValue ((point 2 split 4096 (16*119+j.val)+point 2 split 4096 (16*119+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1904 ≤ lowerValue ((point 2 split 4096 1904+point 2 split 4096 1905)/2)
    have hp : lowerPayment 1904 = (223920460865:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1904+point 2 split 4096 1905)/2 = (448470379:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((448470379:ℝ)/168755200)/ClassicalSixthBranch.v ((448470379:ℝ)/168755200) = (666771284571:ℝ)/329147436952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1904
  · change lowerPayment 1905 ≤ lowerValue ((point 2 split 4096 1905+point 2 split 4096 1906)/2)
    have hp : lowerPayment 1905 = (224012584638:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1905+point 2 split 4096 1906)/2 = (4354647:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((4354647:ℝ)/1638400)/ClassicalSixthBranch.v ((4354647:ℝ)/1638400) = (6472756999:ℝ)/3195140088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1905
  · change lowerPayment 1906 ≤ lowerValue ((point 2 split 4096 1906+point 2 split 4096 1907)/2)
    have hp : lowerPayment 1906 = (224104696612:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1906+point 2 split 4096 1907)/2 = (448586903:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((448586903:ℝ)/168755200)/ClassicalSixthBranch.v ((448586903:ℝ)/168755200) = (666616657223:ℝ)/329051421176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1906
  · change lowerPayment 1907 ≤ lowerValue ((point 2 split 4096 1907+point 2 split 4096 1908)/2)
    have hp : lowerPayment 1907 = (224196796805:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1907+point 2 split 4096 1908)/2 = (89729033:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((89729033:ℝ)/33751040)/ClassicalSixthBranch.v ((89729033:ℝ)/33751040) = (666539343549:ℝ)/329003413288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1907
  · change lowerPayment 1908 ≤ lowerValue ((point 2 split 4096 1908+point 2 split 4096 1909)/2)
    have hp : lowerPayment 1908 = (224288885234:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1908+point 2 split 4096 1909)/2 = (448703427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((448703427:ℝ)/168755200)/ClassicalSixthBranch.v ((448703427:ℝ)/168755200) = (26658481195:ℝ)/13158216216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1908
  · change lowerPayment 1909 ≤ lowerValue ((point 2 split 4096 1909+point 2 split 4096 1910)/2)
    have hp : lowerPayment 1909 = (224380961916:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1909+point 2 split 4096 1910)/2 = (448761689:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((448761689:ℝ)/168755200)/ClassicalSixthBranch.v ((448761689:ℝ)/168755200) = (666384716201:ℝ)/328907397512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1909
  · change lowerPayment 1910 ≤ lowerValue ((point 2 split 4096 1910+point 2 split 4096 1911)/2)
    have hp : lowerPayment 1910 = (224473026868:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1910+point 2 split 4096 1911)/2 = (448819951:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((448819951:ℝ)/168755200)/ClassicalSixthBranch.v ((448819951:ℝ)/168755200) = (666307402527:ℝ)/328859389624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1910
  · change lowerPayment 1911 ≤ lowerValue ((point 2 split 4096 1911+point 2 split 4096 1912)/2)
    have hp : lowerPayment 1911 = (224565080109:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1911+point 2 split 4096 1912)/2 = (448878213:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((448878213:ℝ)/168755200)/ClassicalSixthBranch.v ((448878213:ℝ)/168755200) = (666230088853:ℝ)/328811381736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1911
  · change lowerPayment 1912 ≤ lowerValue ((point 2 split 4096 1912+point 2 split 4096 1913)/2)
    have hp : lowerPayment 1912 = (224657121655:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1912+point 2 split 4096 1913)/2 = (17957459:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((17957459:ℝ)/6750208)/ClassicalSixthBranch.v ((17957459:ℝ)/6750208) = (666152775179:ℝ)/328763373848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1912
  · change lowerPayment 1913 ≤ lowerValue ((point 2 split 4096 1913+point 2 split 4096 1914)/2)
    have hp : lowerPayment 1913 = (224749151523:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1913+point 2 split 4096 1914)/2 = (448994737:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((448994737:ℝ)/168755200)/ClassicalSixthBranch.v ((448994737:ℝ)/168755200) = (133215092301:ℝ)/65743073192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1913
  · change lowerPayment 1914 ≤ lowerValue ((point 2 split 4096 1914+point 2 split 4096 1915)/2)
    have hp : lowerPayment 1914 = (224841169732:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1914+point 2 split 4096 1915)/2 = (449052999:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((449052999:ℝ)/168755200)/ClassicalSixthBranch.v ((449052999:ℝ)/168755200) = (665998147831:ℝ)/328667358072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1914
  · change lowerPayment 1915 ≤ lowerValue ((point 2 split 4096 1915+point 2 split 4096 1916)/2)
    have hp : lowerPayment 1915 = (224933176297:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1915+point 2 split 4096 1916)/2 = (449111261:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((449111261:ℝ)/168755200)/ClassicalSixthBranch.v ((449111261:ℝ)/168755200) = (665920834157:ℝ)/328619350184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1915
  · change lowerPayment 1916 ≤ lowerValue ((point 2 split 4096 1916+point 2 split 4096 1917)/2)
    have hp : lowerPayment 1916 = (225025171238:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1916+point 2 split 4096 1917)/2 = (449169523:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((449169523:ℝ)/168755200)/ClassicalSixthBranch.v ((449169523:ℝ)/168755200) = (665843520483:ℝ)/328571342296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1916
  · change lowerPayment 1917 ≤ lowerValue ((point 2 split 4096 1917+point 2 split 4096 1918)/2)
    have hp : lowerPayment 1917 = (225117154570:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1917+point 2 split 4096 1918)/2 = (89845557:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((89845557:ℝ)/33751040)/ClassicalSixthBranch.v ((89845557:ℝ)/33751040) = (665766206809:ℝ)/328523334408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1917
  · change lowerPayment 1918 ≤ lowerValue ((point 2 split 4096 1918+point 2 split 4096 1919)/2)
    have hp : lowerPayment 1918 = (225209126311:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1918+point 2 split 4096 1919)/2 = (449286047:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((449286047:ℝ)/168755200)/ClassicalSixthBranch.v ((449286047:ℝ)/168755200) = (133137778627:ℝ)/65695065304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1918
  · change lowerPayment 1919 ≤ lowerValue ((point 2 split 4096 1919+point 2 split 4096 1920)/2)
    have hp : lowerPayment 1919 = (225301086479:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1919+point 2 split 4096 1920)/2 = (449344309:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((449344309:ℝ)/168755200)/ClassicalSixthBranch.v ((449344309:ℝ)/168755200) = (665611579461:ℝ)/328427318632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1919
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_119
