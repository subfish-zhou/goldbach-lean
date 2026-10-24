import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints113
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_113 (j : Fin 16) : lowerPayment (16*113+j.val) ≤
    lowerValue ((point 2 split 4096 (16*113+j.val)+point 2 split 4096 (16*113+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1808 ≤ lowerValue ((point 2 split 4096 1808+point 2 split 4096 1809)/2)
    have hp : lowerPayment 1808 = (215018973739:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1808+point 2 split 4096 1809)/2 = (442877227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((442877227:ℝ)/168755200)/ClassicalSixthBranch.v ((442877227:ℝ)/168755200) = (26967735891:ℝ)/13350247768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1808
  · change lowerPayment 1809 ≤ lowerValue ((point 2 split 4096 1809+point 2 split 4096 1810)/2)
    have hp : lowerPayment 1809 = (215112312211:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1809+point 2 split 4096 1810)/2 = (442935489:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((442935489:ℝ)/168755200)/ClassicalSixthBranch.v ((442935489:ℝ)/168755200) = (674116083601:ℝ)/333708186312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1809
  · change lowerPayment 1810 ≤ lowerValue ((point 2 split 4096 1810+point 2 split 4096 1811)/2)
    have hp : lowerPayment 1810 = (215205637181:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1810+point 2 split 4096 1811)/2 = (442993751:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((442993751:ℝ)/168755200)/ClassicalSixthBranch.v ((442993751:ℝ)/168755200) = (674038769927:ℝ)/333660178424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1810
  · change lowerPayment 1811 ≤ lowerValue ((point 2 split 4096 1811+point 2 split 4096 1812)/2)
    have hp : lowerPayment 1811 = (215298948668:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1811+point 2 split 4096 1812)/2 = (443052013:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((443052013:ℝ)/168755200)/ClassicalSixthBranch.v ((443052013:ℝ)/168755200) = (673961456253:ℝ)/333612170536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1811
  · change lowerPayment 1812 ≤ lowerValue ((point 2 split 4096 1812+point 2 split 4096 1813)/2)
    have hp : lowerPayment 1812 = (215392246689:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1812+point 2 split 4096 1813)/2 = (17724411:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((17724411:ℝ)/6750208)/ClassicalSixthBranch.v ((17724411:ℝ)/6750208) = (673884142579:ℝ)/333564162648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1812
  · change lowerPayment 1813 ≤ lowerValue ((point 2 split 4096 1813+point 2 split 4096 1814)/2)
    have hp : lowerPayment 1813 = (215485531262:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1813+point 2 split 4096 1814)/2 = (443168537:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((443168537:ℝ)/168755200)/ClassicalSixthBranch.v ((443168537:ℝ)/168755200) = (134761365781:ℝ)/66703230952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1813
  · change lowerPayment 1814 ≤ lowerValue ((point 2 split 4096 1814+point 2 split 4096 1815)/2)
    have hp : lowerPayment 1814 = (215578802406:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1814+point 2 split 4096 1815)/2 = (443226799:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((443226799:ℝ)/168755200)/ClassicalSixthBranch.v ((443226799:ℝ)/168755200) = (673729515231:ℝ)/333468146872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1814
  · change lowerPayment 1815 ≤ lowerValue ((point 2 split 4096 1815+point 2 split 4096 1816)/2)
    have hp : lowerPayment 1815 = (215672060139:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1815+point 2 split 4096 1816)/2 = (443285061:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((443285061:ℝ)/168755200)/ClassicalSixthBranch.v ((443285061:ℝ)/168755200) = (673652201557:ℝ)/333420138984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1815
  · change lowerPayment 1816 ≤ lowerValue ((point 2 split 4096 1816+point 2 split 4096 1817)/2)
    have hp : lowerPayment 1816 = (215765304478:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1816+point 2 split 4096 1817)/2 = (443343323:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((443343323:ℝ)/168755200)/ClassicalSixthBranch.v ((443343323:ℝ)/168755200) = (673574887883:ℝ)/333372131096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1816
  · change lowerPayment 1817 ≤ lowerValue ((point 2 split 4096 1817+point 2 split 4096 1818)/2)
    have hp : lowerPayment 1817 = (215858535443:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1817+point 2 split 4096 1818)/2 = (88680317:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((88680317:ℝ)/33751040)/ClassicalSixthBranch.v ((88680317:ℝ)/33751040) = (673497574209:ℝ)/333324123208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1817
  · change lowerPayment 1818 ≤ lowerValue ((point 2 split 4096 1818+point 2 split 4096 1819)/2)
    have hp : lowerPayment 1818 = (215951753050:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1818+point 2 split 4096 1819)/2 = (443459847:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((443459847:ℝ)/168755200)/ClassicalSixthBranch.v ((443459847:ℝ)/168755200) = (134684052107:ℝ)/66655223064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1818
  · change lowerPayment 1819 ≤ lowerValue ((point 2 split 4096 1819+point 2 split 4096 1820)/2)
    have hp : lowerPayment 1819 = (216044957318:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1819+point 2 split 4096 1820)/2 = (443518109:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((443518109:ℝ)/168755200)/ClassicalSixthBranch.v ((443518109:ℝ)/168755200) = (673342946861:ℝ)/333228107432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1819
  · change lowerPayment 1820 ≤ lowerValue ((point 2 split 4096 1820+point 2 split 4096 1821)/2)
    have hp : lowerPayment 1820 = (216138148266:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1820+point 2 split 4096 1821)/2 = (443576371:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((443576371:ℝ)/168755200)/ClassicalSixthBranch.v ((443576371:ℝ)/168755200) = (673265633187:ℝ)/333180099544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1820
  · change lowerPayment 1821 ≤ lowerValue ((point 2 split 4096 1821+point 2 split 4096 1822)/2)
    have hp : lowerPayment 1821 = (216231325910:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1821+point 2 split 4096 1822)/2 = (443634633:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((443634633:ℝ)/168755200)/ClassicalSixthBranch.v ((443634633:ℝ)/168755200) = (673188319513:ℝ)/333132091656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1821
  · change lowerPayment 1822 ≤ lowerValue ((point 2 split 4096 1822+point 2 split 4096 1823)/2)
    have hp : lowerPayment 1822 = (216324490270:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1822+point 2 split 4096 1823)/2 = (88738579:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((88738579:ℝ)/33751040)/ClassicalSixthBranch.v ((88738579:ℝ)/33751040) = (673111005839:ℝ)/333084083768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1822
  · change lowerPayment 1823 ≤ lowerValue ((point 2 split 4096 1823+point 2 split 4096 1824)/2)
    have hp : lowerPayment 1823 = (216417641362:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1823+point 2 split 4096 1824)/2 = (443751157:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((443751157:ℝ)/168755200)/ClassicalSixthBranch.v ((443751157:ℝ)/168755200) = (134606738433:ℝ)/66607215176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1823
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_113
