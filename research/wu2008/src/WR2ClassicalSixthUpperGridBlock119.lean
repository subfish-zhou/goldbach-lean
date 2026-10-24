import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints119
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_119 (j : Fin 16) : upperPayment (16*119+j.val) ≤
    upperValue ((point split endpoint 4096 (16*119+j.val)+point split endpoint 4096 (16*119+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1904 ≤ upperValue ((point split endpoint 4096 1904+point split endpoint 4096 1905)/2)
    have hp : upperPayment 1904 = (283317638967:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1904+point split endpoint 4096 1905)/2 = (624049727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624049727:ℝ)/168755200)*ClassicalSixthBranch.v ((624049727:ℝ)/168755200)/ClassicalSixthBranch.r = (117088632728081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1904
  · change upperPayment 1905 ≤ upperValue ((point split endpoint 4096 1905+point split endpoint 4096 1906)/2)
    have hp : upperPayment 1905 = (283221590055:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1905+point split endpoint 4096 1906)/2 = (624074877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624074877:ℝ)/168755200)*ClassicalSixthBranch.v ((624074877:ℝ)/168755200)/ClassicalSixthBranch.r = (117066471268377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1905
  · change upperPayment 1906 ≤ upperValue ((point split endpoint 4096 1906+point split endpoint 4096 1907)/2)
    have hp : upperPayment 1906 = (283125515404:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1906+point split endpoint 4096 1907)/2 = (624100027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624100027:ℝ)/168755200)*ClassicalSixthBranch.v ((624100027:ℝ)/168755200)/ClassicalSixthBranch.r = (117044311832745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1906
  · change upperPayment 1907 ≤ upperValue ((point split endpoint 4096 1907+point split endpoint 4096 1908)/2)
    have hp : upperPayment 1907 = (283029415009:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1907+point split endpoint 4096 1908)/2 = (624125177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624125177:ℝ)/168755200)*ClassicalSixthBranch.v ((624125177:ℝ)/168755200)/ClassicalSixthBranch.r = (117022154421185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1907
  · change upperPayment 1908 ≤ upperValue ((point split endpoint 4096 1908+point split endpoint 4096 1909)/2)
    have hp : upperPayment 1908 = (282933288867:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1908+point split endpoint 4096 1909)/2 = (624150327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624150327:ℝ)/168755200)*ClassicalSixthBranch.v ((624150327:ℝ)/168755200)/ClassicalSixthBranch.r = (116999999033697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1908
  · change upperPayment 1909 ≤ upperValue ((point split endpoint 4096 1909+point split endpoint 4096 1910)/2)
    have hp : upperPayment 1909 = (282837136971:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1909+point split endpoint 4096 1910)/2 = (624175477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624175477:ℝ)/168755200)*ClassicalSixthBranch.v ((624175477:ℝ)/168755200)/ClassicalSixthBranch.r = (116977845670281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1909
  · change upperPayment 1910 ≤ upperValue ((point split endpoint 4096 1910+point split endpoint 4096 1911)/2)
    have hp : upperPayment 1910 = (282740959316:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1910+point split endpoint 4096 1911)/2 = (624200627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624200627:ℝ)/168755200)*ClassicalSixthBranch.v ((624200627:ℝ)/168755200)/ClassicalSixthBranch.r = (116955694330937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1910
  · change upperPayment 1911 ≤ upperValue ((point split endpoint 4096 1911+point split endpoint 4096 1912)/2)
    have hp : upperPayment 1911 = (282644755899:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1911+point split endpoint 4096 1912)/2 = (624225777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624225777:ℝ)/168755200)*ClassicalSixthBranch.v ((624225777:ℝ)/168755200)/ClassicalSixthBranch.r = (116933545015665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1911
  · change upperPayment 1912 ≤ upperValue ((point split endpoint 4096 1912+point split endpoint 4096 1913)/2)
    have hp : upperPayment 1912 = (282548526713:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1912+point split endpoint 4096 1913)/2 = (624250927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624250927:ℝ)/168755200)*ClassicalSixthBranch.v ((624250927:ℝ)/168755200)/ClassicalSixthBranch.r = (116911397724465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1912
  · change upperPayment 1913 ≤ upperValue ((point split endpoint 4096 1913+point split endpoint 4096 1914)/2)
    have hp : upperPayment 1913 = (282452271753:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1913+point split endpoint 4096 1914)/2 = (624276077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624276077:ℝ)/168755200)*ClassicalSixthBranch.v ((624276077:ℝ)/168755200)/ClassicalSixthBranch.r = (116889252457337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1913
  · change upperPayment 1914 ≤ upperValue ((point split endpoint 4096 1914+point split endpoint 4096 1915)/2)
    have hp : upperPayment 1914 = (282355991016:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1914+point split endpoint 4096 1915)/2 = (624301227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624301227:ℝ)/168755200)*ClassicalSixthBranch.v ((624301227:ℝ)/168755200)/ClassicalSixthBranch.r = (116867109214281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1914
  · change upperPayment 1915 ≤ upperValue ((point split endpoint 4096 1915+point split endpoint 4096 1916)/2)
    have hp : upperPayment 1915 = (282259684495:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1915+point split endpoint 4096 1916)/2 = (624326377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624326377:ℝ)/168755200)*ClassicalSixthBranch.v ((624326377:ℝ)/168755200)/ClassicalSixthBranch.r = (116844967995297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1915
  · change upperPayment 1916 ≤ upperValue ((point split endpoint 4096 1916+point split endpoint 4096 1917)/2)
    have hp : upperPayment 1916 = (282163352186:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1916+point split endpoint 4096 1917)/2 = (624351527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624351527:ℝ)/168755200)*ClassicalSixthBranch.v ((624351527:ℝ)/168755200)/ClassicalSixthBranch.r = (116822828800385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1916
  · change upperPayment 1917 ≤ upperValue ((point split endpoint 4096 1917+point split endpoint 4096 1918)/2)
    have hp : upperPayment 1917 = (282066994083:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1917+point split endpoint 4096 1918)/2 = (624376677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624376677:ℝ)/168755200)*ClassicalSixthBranch.v ((624376677:ℝ)/168755200)/ClassicalSixthBranch.r = (116800691629545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1917
  · change upperPayment 1918 ≤ upperValue ((point split endpoint 4096 1918+point split endpoint 4096 1919)/2)
    have hp : upperPayment 1918 = (281970610183:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1918+point split endpoint 4096 1919)/2 = (624401827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624401827:ℝ)/168755200)*ClassicalSixthBranch.v ((624401827:ℝ)/168755200)/ClassicalSixthBranch.r = (116778556482777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1918
  · change upperPayment 1919 ≤ upperValue ((point split endpoint 4096 1919+point split endpoint 4096 1920)/2)
    have hp : upperPayment 1919 = (281874200478:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1919+point split endpoint 4096 1920)/2 = (624426977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624426977:ℝ)/168755200)*ClassicalSixthBranch.v ((624426977:ℝ)/168755200)/ClassicalSixthBranch.r = (116756423360081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1919
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_119
