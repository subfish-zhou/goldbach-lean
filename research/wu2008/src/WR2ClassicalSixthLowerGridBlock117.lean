import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints117
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_117 (j : Fin 16) : lowerPayment (16*117+j.val) ≤
    lowerValue ((point 2 split 4096 (16*117+j.val)+point 2 split 4096 (16*117+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1872 ≤ lowerValue ((point 2 split 4096 1872+point 2 split 4096 1873)/2)
    have hp : lowerPayment 1872 = (220966166075:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1872+point 2 split 4096 1873)/2 = (89321199:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((89321199:ℝ)/33751040)/ClassicalSixthBranch.v ((89321199:ℝ)/33751040) = (669245322139:ℝ)/330683689368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1872
  · change lowerPayment 1873 ≤ lowerValue ((point 2 split 4096 1873+point 2 split 4096 1874)/2)
    have hp : lowerPayment 1873 = (221058676623:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1873+point 2 split 4096 1874)/2 = (446664257:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((446664257:ℝ)/168755200)/ClassicalSixthBranch.v ((446664257:ℝ)/168755200) = (133833601693:ℝ)/66127136296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1873
  · change lowerPayment 1874 ≤ lowerValue ((point 2 split 4096 1874+point 2 split 4096 1875)/2)
    have hp : lowerPayment 1874 = (221151174812:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1874+point 2 split 4096 1875)/2 = (446722519:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((446722519:ℝ)/168755200)/ClassicalSixthBranch.v ((446722519:ℝ)/168755200) = (669090694791:ℝ)/330587673592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1874
  · change lowerPayment 1875 ≤ lowerValue ((point 2 split 4096 1875+point 2 split 4096 1876)/2)
    have hp : lowerPayment 1875 = (221243660660:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1875+point 2 split 4096 1876)/2 = (446780781:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((446780781:ℝ)/168755200)/ClassicalSixthBranch.v ((446780781:ℝ)/168755200) = (669013381117:ℝ)/330539665704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1875
  · change lowerPayment 1876 ≤ lowerValue ((point 2 split 4096 1876+point 2 split 4096 1877)/2)
    have hp : lowerPayment 1876 = (221336134185:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1876+point 2 split 4096 1877)/2 = (446839043:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((446839043:ℝ)/168755200)/ClassicalSixthBranch.v ((446839043:ℝ)/168755200) = (668936067443:ℝ)/330491657816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1876
  · change lowerPayment 1877 ≤ lowerValue ((point 2 split 4096 1877+point 2 split 4096 1878)/2)
    have hp : lowerPayment 1877 = (221428595404:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1877+point 2 split 4096 1878)/2 = (89379461:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((89379461:ℝ)/33751040)/ClassicalSixthBranch.v ((89379461:ℝ)/33751040) = (668858753769:ℝ)/330443649928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1877
  · change lowerPayment 1878 ≤ lowerValue ((point 2 split 4096 1878+point 2 split 4096 1879)/2)
    have hp : lowerPayment 1878 = (221521044336:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1878+point 2 split 4096 1879)/2 = (446955567:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((446955567:ℝ)/168755200)/ClassicalSixthBranch.v ((446955567:ℝ)/168755200) = (133756288019:ℝ)/66079128408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1878
  · change lowerPayment 1879 ≤ lowerValue ((point 2 split 4096 1879+point 2 split 4096 1880)/2)
    have hp : lowerPayment 1879 = (221613480996:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1879+point 2 split 4096 1880)/2 = (447013829:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((447013829:ℝ)/168755200)/ClassicalSixthBranch.v ((447013829:ℝ)/168755200) = (668704126421:ℝ)/330347634152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1879
  · change lowerPayment 1880 ≤ lowerValue ((point 2 split 4096 1880+point 2 split 4096 1881)/2)
    have hp : lowerPayment 1880 = (221705905404:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1880+point 2 split 4096 1881)/2 = (447072091:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((447072091:ℝ)/168755200)/ClassicalSixthBranch.v ((447072091:ℝ)/168755200) = (668626812747:ℝ)/330299626264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1880
  · change lowerPayment 1881 ≤ lowerValue ((point 2 split 4096 1881+point 2 split 4096 1882)/2)
    have hp : lowerPayment 1881 = (221798317577:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1881+point 2 split 4096 1882)/2 = (447130353:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((447130353:ℝ)/168755200)/ClassicalSixthBranch.v ((447130353:ℝ)/168755200) = (668549499073:ℝ)/330251618376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1881
  · change lowerPayment 1882 ≤ lowerValue ((point 2 split 4096 1882+point 2 split 4096 1883)/2)
    have hp : lowerPayment 1882 = (221890717532:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1882+point 2 split 4096 1883)/2 = (89437723:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((89437723:ℝ)/33751040)/ClassicalSixthBranch.v ((89437723:ℝ)/33751040) = (668472185399:ℝ)/330203610488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1882
  · change lowerPayment 1883 ≤ lowerValue ((point 2 split 4096 1883+point 2 split 4096 1884)/2)
    have hp : lowerPayment 1883 = (221983105286:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1883+point 2 split 4096 1884)/2 = (447246877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((447246877:ℝ)/168755200)/ClassicalSixthBranch.v ((447246877:ℝ)/168755200) = (26735794869:ℝ)/13206224104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1883
  · change lowerPayment 1884 ≤ lowerValue ((point 2 split 4096 1884+point 2 split 4096 1885)/2)
    have hp : lowerPayment 1884 = (222075480858:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1884+point 2 split 4096 1885)/2 = (447305139:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((447305139:ℝ)/168755200)/ClassicalSixthBranch.v ((447305139:ℝ)/168755200) = (668317558051:ℝ)/330107594712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1884
  · change lowerPayment 1885 ≤ lowerValue ((point 2 split 4096 1885+point 2 split 4096 1886)/2)
    have hp : lowerPayment 1885 = (222167844264:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1885+point 2 split 4096 1886)/2 = (447363401:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((447363401:ℝ)/168755200)/ClassicalSixthBranch.v ((447363401:ℝ)/168755200) = (668240244377:ℝ)/330059586824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1885
  · change lowerPayment 1886 ≤ lowerValue ((point 2 split 4096 1886+point 2 split 4096 1887)/2)
    have hp : lowerPayment 1886 = (222260195523:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1886+point 2 split 4096 1887)/2 = (447421663:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((447421663:ℝ)/168755200)/ClassicalSixthBranch.v ((447421663:ℝ)/168755200) = (668162930703:ℝ)/330011578936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1886
  · change lowerPayment 1887 ≤ lowerValue ((point 2 split 4096 1887+point 2 split 4096 1888)/2)
    have hp : lowerPayment 1887 = (222352534652:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1887+point 2 split 4096 1888)/2 = (17899197:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((17899197:ℝ)/6750208)/ClassicalSixthBranch.v ((17899197:ℝ)/6750208) = (668085617029:ℝ)/329963571048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1887
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_117
