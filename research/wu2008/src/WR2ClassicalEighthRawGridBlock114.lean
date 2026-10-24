import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints114
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_114 (j : Fin 16) : upperValue ((point (16*114+j.val)+point ((16*114+j.val)+1))/2) ≤ payment (16*114+j.val) := by
  fin_cases j
  · change upperValue ((point (1824)+point ((1824)+1))/2) ≤ payment (1824)
    have hp : payment 1824 = (382378036576:ℝ)/1000000000000 := rfl
    have hx : (point 1824+point 1825)/2 = (4976323:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1824
  · change upperValue ((point (1825)+point ((1825)+1))/2) ≤ payment (1825)
    have hp : payment 1825 = (380646331660:ℝ)/1000000000000 := rfl
    have hx : (point 1825+point 1826)/2 = (1659459:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1825
  · change upperValue ((point (1826)+point ((1826)+1))/2) ≤ payment (1826)
    have hp : payment 1826 = (378914911671:ℝ)/1000000000000 := rfl
    have hx : (point 1826+point 1827)/2 = (4980431:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1826
  · change upperValue ((point (1827)+point ((1827)+1))/2) ≤ payment (1827)
    have hp : payment 1827 = (377183775236:ℝ)/1000000000000 := rfl
    have hx : (point 1827+point 1828)/2 = (4982485:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1827
  · change upperValue ((point (1828)+point ((1828)+1))/2) ≤ payment (1828)
    have hp : payment 1828 = (375452920981:ℝ)/1000000000000 := rfl
    have hx : (point 1828+point 1829)/2 = (1661513:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1828
  · change upperValue ((point (1829)+point ((1829)+1))/2) ≤ payment (1829)
    have hp : payment 1829 = (373722347535:ℝ)/1000000000000 := rfl
    have hx : (point 1829+point 1830)/2 = (4986593:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1829
  · change upperValue ((point (1830)+point ((1830)+1))/2) ≤ payment (1830)
    have hp : payment 1830 = (371992053529:ℝ)/1000000000000 := rfl
    have hx : (point 1830+point 1831)/2 = (4988647:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1830
  · change upperValue ((point (1831)+point ((1831)+1))/2) ≤ payment (1831)
    have hp : payment 1831 = (370262037591:ℝ)/1000000000000 := rfl
    have hx : (point 1831+point 1832)/2 = (1663567:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1831
  · change upperValue ((point (1832)+point ((1832)+1))/2) ≤ payment (1832)
    have hp : payment 1832 = (368532298354:ℝ)/1000000000000 := rfl
    have hx : (point 1832+point 1833)/2 = (4992755:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1832
  · change upperValue ((point (1833)+point ((1833)+1))/2) ≤ payment (1833)
    have hp : payment 1833 = (366802834451:ℝ)/1000000000000 := rfl
    have hx : (point 1833+point 1834)/2 = (4994809:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1833
  · change upperValue ((point (1834)+point ((1834)+1))/2) ≤ payment (1834)
    have hp : payment 1834 = (365073644516:ℝ)/1000000000000 := rfl
    have hx : (point 1834+point 1835)/2 = (1665621:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1834
  · change upperValue ((point (1835)+point ((1835)+1))/2) ≤ payment (1835)
    have hp : payment 1835 = (363344727183:ℝ)/1000000000000 := rfl
    have hx : (point 1835+point 1836)/2 = (4998917:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1835
  · change upperValue ((point (1836)+point ((1836)+1))/2) ≤ payment (1836)
    have hp : payment 1836 = (361616081089:ℝ)/1000000000000 := rfl
    have hx : (point 1836+point 1837)/2 = (5000971:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1836
  · change upperValue ((point (1837)+point ((1837)+1))/2) ≤ payment (1837)
    have hp : payment 1837 = (359887704870:ℝ)/1000000000000 := rfl
    have hx : (point 1837+point 1838)/2 = (1667675:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1837
  · change upperValue ((point (1838)+point ((1838)+1))/2) ≤ payment (1838)
    have hp : payment 1838 = (358159597166:ℝ)/1000000000000 := rfl
    have hx : (point 1838+point 1839)/2 = (5005079:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1838
  · change upperValue ((point (1839)+point ((1839)+1))/2) ≤ payment (1839)
    have hp : payment 1839 = (356431756614:ℝ)/1000000000000 := rfl
    have hx : (point 1839+point 1840)/2 = (5007133:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1839
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_114
