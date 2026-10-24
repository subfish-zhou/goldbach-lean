import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints117
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_117 (j : Fin 16) : upperPayment (16*117+j.val) ≤
    upperValue ((point split endpoint 4096 (16*117+j.val)+point split endpoint 4096 (16*117+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1872 ≤ upperValue ((point split endpoint 4096 1872+point split endpoint 4096 1873)/2)
    have hp : upperPayment 1872 = (286377643997:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1872+point split endpoint 4096 1873)/2 = (623244927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623244927:ℝ)/168755200)*ClassicalSixthBranch.v ((623244927:ℝ)/168755200)/ClassicalSixthBranch.r = (117798868148625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1872
  · change upperPayment 1873 ≤ upperValue ((point split endpoint 4096 1873+point split endpoint 4096 1874)/2)
    have hp : upperPayment 1873 = (286282416095:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1873+point split endpoint 4096 1874)/2 = (623270077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623270077:ℝ)/168755200)*ClassicalSixthBranch.v ((623270077:ℝ)/168755200)/ClassicalSixthBranch.r = (117776641918617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1873
  · change upperPayment 1874 ≤ upperValue ((point split endpoint 4096 1874+point split endpoint 4096 1875)/2)
    have hp : upperPayment 1874 = (286187162613:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1874+point split endpoint 4096 1875)/2 = (623295227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623295227:ℝ)/168755200)*ClassicalSixthBranch.v ((623295227:ℝ)/168755200)/ClassicalSixthBranch.r = (117754417712681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1874
  · change upperPayment 1875 ≤ upperValue ((point split endpoint 4096 1875+point split endpoint 4096 1876)/2)
    have hp : upperPayment 1875 = (286091883546:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1875+point split endpoint 4096 1876)/2 = (623320377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623320377:ℝ)/168755200)*ClassicalSixthBranch.v ((623320377:ℝ)/168755200)/ClassicalSixthBranch.r = (117732195530817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1875
  · change upperPayment 1876 ≤ upperValue ((point split endpoint 4096 1876+point split endpoint 4096 1877)/2)
    have hp : upperPayment 1876 = (285996578890:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1876+point split endpoint 4096 1877)/2 = (623345527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623345527:ℝ)/168755200)*ClassicalSixthBranch.v ((623345527:ℝ)/168755200)/ClassicalSixthBranch.r = (117709975373025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1876
  · change upperPayment 1877 ≤ upperValue ((point split endpoint 4096 1877+point split endpoint 4096 1878)/2)
    have hp : upperPayment 1877 = (285901248638:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1877+point split endpoint 4096 1878)/2 = (623370677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623370677:ℝ)/168755200)*ClassicalSixthBranch.v ((623370677:ℝ)/168755200)/ClassicalSixthBranch.r = (117687757239305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1877
  · change upperPayment 1878 ≤ upperValue ((point split endpoint 4096 1878+point split endpoint 4096 1879)/2)
    have hp : upperPayment 1878 = (285805892787:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1878+point split endpoint 4096 1879)/2 = (623395827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623395827:ℝ)/168755200)*ClassicalSixthBranch.v ((623395827:ℝ)/168755200)/ClassicalSixthBranch.r = (117665541129657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1878
  · change upperPayment 1879 ≤ upperValue ((point split endpoint 4096 1879+point split endpoint 4096 1880)/2)
    have hp : upperPayment 1879 = (285710511330:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1879+point split endpoint 4096 1880)/2 = (623420977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623420977:ℝ)/168755200)*ClassicalSixthBranch.v ((623420977:ℝ)/168755200)/ClassicalSixthBranch.r = (117643327044081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1879
  · change upperPayment 1880 ≤ upperValue ((point split endpoint 4096 1880+point split endpoint 4096 1881)/2)
    have hp : upperPayment 1880 = (285615104265:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1880+point split endpoint 4096 1881)/2 = (623446127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623446127:ℝ)/168755200)*ClassicalSixthBranch.v ((623446127:ℝ)/168755200)/ClassicalSixthBranch.r = (117621114982577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1880
  · change upperPayment 1881 ≤ upperValue ((point split endpoint 4096 1881+point split endpoint 4096 1882)/2)
    have hp : upperPayment 1881 = (285519671585:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1881+point split endpoint 4096 1882)/2 = (623471277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623471277:ℝ)/168755200)*ClassicalSixthBranch.v ((623471277:ℝ)/168755200)/ClassicalSixthBranch.r = (1141736941215:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1881
  · change upperPayment 1882 ≤ upperValue ((point split endpoint 4096 1882+point split endpoint 4096 1883)/2)
    have hp : upperPayment 1882 = (285424213285:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1882+point split endpoint 4096 1883)/2 = (623496427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623496427:ℝ)/168755200)*ClassicalSixthBranch.v ((623496427:ℝ)/168755200)/ClassicalSixthBranch.r = (117576696931785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1882
  · change upperPayment 1883 ≤ upperValue ((point split endpoint 4096 1883+point split endpoint 4096 1884)/2)
    have hp : upperPayment 1883 = (285328729361:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1883+point split endpoint 4096 1884)/2 = (623521577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623521577:ℝ)/168755200)*ClassicalSixthBranch.v ((623521577:ℝ)/168755200)/ClassicalSixthBranch.r = (117554490942497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1883
  · change upperPayment 1884 ≤ upperValue ((point split endpoint 4096 1884+point split endpoint 4096 1885)/2)
    have hp : upperPayment 1884 = (285233219808:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1884+point split endpoint 4096 1885)/2 = (623546727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623546727:ℝ)/168755200)*ClassicalSixthBranch.v ((623546727:ℝ)/168755200)/ClassicalSixthBranch.r = (117532286977281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1884
  · change upperPayment 1885 ≤ upperValue ((point split endpoint 4096 1885+point split endpoint 4096 1886)/2)
    have hp : upperPayment 1885 = (285137684620:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1885+point split endpoint 4096 1886)/2 = (623571877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623571877:ℝ)/168755200)*ClassicalSixthBranch.v ((623571877:ℝ)/168755200)/ClassicalSixthBranch.r = (117510085036137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1885
  · change upperPayment 1886 ≤ upperValue ((point split endpoint 4096 1886+point split endpoint 4096 1887)/2)
    have hp : upperPayment 1886 = (285042123793:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1886+point split endpoint 4096 1887)/2 = (623597027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623597027:ℝ)/168755200)*ClassicalSixthBranch.v ((623597027:ℝ)/168755200)/ClassicalSixthBranch.r = (117487885119065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1886
  · change upperPayment 1887 ≤ upperValue ((point split endpoint 4096 1887+point split endpoint 4096 1888)/2)
    have hp : upperPayment 1887 = (284946537323:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1887+point split endpoint 4096 1888)/2 = (623622177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((623622177:ℝ)/168755200)*ClassicalSixthBranch.v ((623622177:ℝ)/168755200)/ClassicalSixthBranch.r = (117465687226065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1887
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_117
