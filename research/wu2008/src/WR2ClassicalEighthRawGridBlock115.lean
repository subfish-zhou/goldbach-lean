import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints115
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_115 (j : Fin 16) : upperValue ((point (16*115+j.val)+point ((16*115+j.val)+1))/2) ≤ payment (16*115+j.val) := by
  fin_cases j
  · change upperValue ((point (1840)+point ((1840)+1))/2) ≤ payment (1840)
    have hp : payment 1840 = (354704181856:ℝ)/1000000000000 := rfl
    have hx : (point 1840+point 1841)/2 = (1669729:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1840
  · change upperValue ((point (1841)+point ((1841)+1))/2) ≤ payment (1841)
    have hp : payment 1841 = (352976871533:ℝ)/1000000000000 := rfl
    have hx : (point 1841+point 1842)/2 = (5011241:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1841
  · change upperValue ((point (1842)+point ((1842)+1))/2) ≤ payment (1842)
    have hp : payment 1842 = (351249824286:ℝ)/1000000000000 := rfl
    have hx : (point 1842+point 1843)/2 = (5013295:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1842
  · change upperValue ((point (1843)+point ((1843)+1))/2) ≤ payment (1843)
    have hp : payment 1843 = (349523038761:ℝ)/1000000000000 := rfl
    have hx : (point 1843+point 1844)/2 = (1671783:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1843
  · change upperValue ((point (1844)+point ((1844)+1))/2) ≤ payment (1844)
    have hp : payment 1844 = (347796513600:ℝ)/1000000000000 := rfl
    have hx : (point 1844+point 1845)/2 = (5017403:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1844
  · change upperValue ((point (1845)+point ((1845)+1))/2) ≤ payment (1845)
    have hp : payment 1845 = (346070247450:ℝ)/1000000000000 := rfl
    have hx : (point 1845+point 1846)/2 = (5019457:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1845
  · change upperValue ((point (1846)+point ((1846)+1))/2) ≤ payment (1846)
    have hp : payment 1846 = (344344238957:ℝ)/1000000000000 := rfl
    have hx : (point 1846+point 1847)/2 = (1673837:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1846
  · change upperValue ((point (1847)+point ((1847)+1))/2) ≤ payment (1847)
    have hp : payment 1847 = (342618486769:ℝ)/1000000000000 := rfl
    have hx : (point 1847+point 1848)/2 = (5023565:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1847
  · change upperValue ((point (1848)+point ((1848)+1))/2) ≤ payment (1848)
    have hp : payment 1848 = (340892989534:ℝ)/1000000000000 := rfl
    have hx : (point 1848+point 1849)/2 = (5025619:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1848
  · change upperValue ((point (1849)+point ((1849)+1))/2) ≤ payment (1849)
    have hp : payment 1849 = (339167745902:ℝ)/1000000000000 := rfl
    have hx : (point 1849+point 1850)/2 = (1675891:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1849
  · change upperValue ((point (1850)+point ((1850)+1))/2) ≤ payment (1850)
    have hp : payment 1850 = (337442754524:ℝ)/1000000000000 := rfl
    have hx : (point 1850+point 1851)/2 = (5029727:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1850
  · change upperValue ((point (1851)+point ((1851)+1))/2) ≤ payment (1851)
    have hp : payment 1851 = (335718014051:ℝ)/1000000000000 := rfl
    have hx : (point 1851+point 1852)/2 = (5031781:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1851
  · change upperValue ((point (1852)+point ((1852)+1))/2) ≤ payment (1852)
    have hp : payment 1852 = (333993523136:ℝ)/1000000000000 := rfl
    have hx : (point 1852+point 1853)/2 = (1677945:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1852
  · change upperValue ((point (1853)+point ((1853)+1))/2) ≤ payment (1853)
    have hp : payment 1853 = (332269280433:ℝ)/1000000000000 := rfl
    have hx : (point 1853+point 1854)/2 = (5035889:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1853
  · change upperValue ((point (1854)+point ((1854)+1))/2) ≤ payment (1854)
    have hp : payment 1854 = (330545284597:ℝ)/1000000000000 := rfl
    have hx : (point 1854+point 1855)/2 = (5037943:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1854
  · change upperValue ((point (1855)+point ((1855)+1))/2) ≤ payment (1855)
    have hp : payment 1855 = (328821534283:ℝ)/1000000000000 := rfl
    have hx : (point 1855+point 1856)/2 = (1679999:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1855
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_115
