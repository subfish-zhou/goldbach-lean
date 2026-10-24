import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints118
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_118 (j : Fin 16) : upperPayment (16*118+j.val) ≤
    upperValue ((point split endpoint 4096 (16*118+j.val)+point split endpoint 4096 (16*118+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1888 ≤ upperValue ((point split endpoint 4096 1888+point split endpoint 4096 1889)/2)
    have hp : upperPayment 1888 = (284850925203:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1888+point split endpoint 4096 1889)/2 = (623647327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623647327:ℝ)/168755200)*ClassicalSixthBranch.v ((623647327:ℝ)/168755200)/ClassicalSixthBranch.r = (117443491357137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1888
  · change upperPayment 1889 ≤ upperValue ((point split endpoint 4096 1889+point split endpoint 4096 1890)/2)
    have hp : upperPayment 1889 = (284755287429:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1889+point split endpoint 4096 1890)/2 = (623672477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623672477:ℝ)/168755200)*ClassicalSixthBranch.v ((623672477:ℝ)/168755200)/ClassicalSixthBranch.r = (117421297512281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1889
  · change upperPayment 1890 ≤ upperValue ((point split endpoint 4096 1890+point split endpoint 4096 1891)/2)
    have hp : upperPayment 1890 = (284659623996:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1890+point split endpoint 4096 1891)/2 = (623697627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623697627:ℝ)/168755200)*ClassicalSixthBranch.v ((623697627:ℝ)/168755200)/ClassicalSixthBranch.r = (117399105691497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1890
  · change upperPayment 1891 ≤ upperValue ((point split endpoint 4096 1891+point split endpoint 4096 1892)/2)
    have hp : upperPayment 1891 = (284563934899:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1891+point split endpoint 4096 1892)/2 = (623722777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623722777:ℝ)/168755200)*ClassicalSixthBranch.v ((623722777:ℝ)/168755200)/ClassicalSixthBranch.r = (117376915894785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1891
  · change upperPayment 1892 ≤ upperValue ((point split endpoint 4096 1892+point split endpoint 4096 1893)/2)
    have hp : upperPayment 1892 = (284468220133:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1892+point split endpoint 4096 1893)/2 = (623747927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623747927:ℝ)/168755200)*ClassicalSixthBranch.v ((623747927:ℝ)/168755200)/ClassicalSixthBranch.r = (117354728122145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1892
  · change upperPayment 1893 ≤ upperValue ((point split endpoint 4096 1893+point split endpoint 4096 1894)/2)
    have hp : upperPayment 1893 = (284372479693:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1893+point split endpoint 4096 1894)/2 = (623773077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623773077:ℝ)/168755200)*ClassicalSixthBranch.v ((623773077:ℝ)/168755200)/ClassicalSixthBranch.r = (117332542373577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1893
  · change upperPayment 1894 ≤ upperValue ((point split endpoint 4096 1894+point split endpoint 4096 1895)/2)
    have hp : upperPayment 1894 = (284276713575:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1894+point split endpoint 4096 1895)/2 = (623798227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623798227:ℝ)/168755200)*ClassicalSixthBranch.v ((623798227:ℝ)/168755200)/ClassicalSixthBranch.r = (117310358649081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1894
  · change upperPayment 1895 ≤ upperValue ((point split endpoint 4096 1895+point split endpoint 4096 1896)/2)
    have hp : upperPayment 1895 = (284180921773:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1895+point split endpoint 4096 1896)/2 = (623823377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623823377:ℝ)/168755200)*ClassicalSixthBranch.v ((623823377:ℝ)/168755200)/ClassicalSixthBranch.r = (117288176948657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1895
  · change upperPayment 1896 ≤ upperValue ((point split endpoint 4096 1896+point split endpoint 4096 1897)/2)
    have hp : upperPayment 1896 = (284085104282:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1896+point split endpoint 4096 1897)/2 = (623848527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623848527:ℝ)/168755200)*ClassicalSixthBranch.v ((623848527:ℝ)/168755200)/ClassicalSixthBranch.r = (117265997272305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1896
  · change upperPayment 1897 ≤ upperValue ((point split endpoint 4096 1897+point split endpoint 4096 1898)/2)
    have hp : upperPayment 1897 = (283989261098:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1897+point split endpoint 4096 1898)/2 = (623873677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623873677:ℝ)/168755200)*ClassicalSixthBranch.v ((623873677:ℝ)/168755200)/ClassicalSixthBranch.r = (117243819620025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1897
  · change upperPayment 1898 ≤ upperValue ((point split endpoint 4096 1898+point split endpoint 4096 1899)/2)
    have hp : upperPayment 1898 = (283893392215:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1898+point split endpoint 4096 1899)/2 = (623898827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623898827:ℝ)/168755200)*ClassicalSixthBranch.v ((623898827:ℝ)/168755200)/ClassicalSixthBranch.r = (117221643991817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1898
  · change upperPayment 1899 ≤ upperValue ((point split endpoint 4096 1899+point split endpoint 4096 1900)/2)
    have hp : upperPayment 1899 = (283797497628:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1899+point split endpoint 4096 1900)/2 = (623923977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623923977:ℝ)/168755200)*ClassicalSixthBranch.v ((623923977:ℝ)/168755200)/ClassicalSixthBranch.r = (117199470387681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1899
  · change upperPayment 1900 ≤ upperValue ((point split endpoint 4096 1900+point split endpoint 4096 1901)/2)
    have hp : upperPayment 1900 = (283701577333:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1900+point split endpoint 4096 1901)/2 = (623949127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623949127:ℝ)/168755200)*ClassicalSixthBranch.v ((623949127:ℝ)/168755200)/ClassicalSixthBranch.r = (117177298807617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1900
  · change upperPayment 1901 ≤ upperValue ((point split endpoint 4096 1901+point split endpoint 4096 1902)/2)
    have hp : upperPayment 1901 = (283605631324:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1901+point split endpoint 4096 1902)/2 = (623974277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623974277:ℝ)/168755200)*ClassicalSixthBranch.v ((623974277:ℝ)/168755200)/ClassicalSixthBranch.r = (117155129251625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1901
  · change upperPayment 1902 ≤ upperValue ((point split endpoint 4096 1902+point split endpoint 4096 1903)/2)
    have hp : upperPayment 1902 = (283509659597:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1902+point split endpoint 4096 1903)/2 = (623999427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623999427:ℝ)/168755200)*ClassicalSixthBranch.v ((623999427:ℝ)/168755200)/ClassicalSixthBranch.r = (117132961719705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1902
  · change upperPayment 1903 ≤ upperValue ((point split endpoint 4096 1903+point split endpoint 4096 1904)/2)
    have hp : upperPayment 1903 = (283413662146:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1903+point split endpoint 4096 1904)/2 = (624024577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((624024577:ℝ)/168755200)*ClassicalSixthBranch.v ((624024577:ℝ)/168755200)/ClassicalSixthBranch.r = (117110796211857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1903
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_118
