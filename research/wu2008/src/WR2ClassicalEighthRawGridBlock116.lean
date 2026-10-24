import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints116
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_116 (j : Fin 16) : upperValue ((point (16*116+j.val)+point ((16*116+j.val)+1))/2) ≤ payment (16*116+j.val) := by
  fin_cases j
  · change upperValue ((point (1856)+point ((1856)+1))/2) ≤ payment (1856)
    have hp : payment 1856 = (327098028147:ℝ)/1000000000000 := rfl
    have hx : (point 1856+point 1857)/2 = (5042051:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1856
  · change upperValue ((point (1857)+point ((1857)+1))/2) ≤ payment (1857)
    have hp : payment 1857 = (325374764848:ℝ)/1000000000000 := rfl
    have hx : (point 1857+point 1858)/2 = (5044105:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1857
  · change upperValue ((point (1858)+point ((1858)+1))/2) ≤ payment (1858)
    have hp : payment 1858 = (323651743045:ℝ)/1000000000000 := rfl
    have hx : (point 1858+point 1859)/2 = (1682053:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1858
  · change upperValue ((point (1859)+point ((1859)+1))/2) ≤ payment (1859)
    have hp : payment 1859 = (321928961396:ℝ)/1000000000000 := rfl
    have hx : (point 1859+point 1860)/2 = (5048213:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1859
  · change upperValue ((point (1860)+point ((1860)+1))/2) ≤ payment (1860)
    have hp : payment 1860 = (320206418563:ℝ)/1000000000000 := rfl
    have hx : (point 1860+point 1861)/2 = (5050267:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1860
  · change upperValue ((point (1861)+point ((1861)+1))/2) ≤ payment (1861)
    have hp : payment 1861 = (318484113208:ℝ)/1000000000000 := rfl
    have hx : (point 1861+point 1862)/2 = (1684107:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1861
  · change upperValue ((point (1862)+point ((1862)+1))/2) ≤ payment (1862)
    have hp : payment 1862 = (316762043992:ℝ)/1000000000000 := rfl
    have hx : (point 1862+point 1863)/2 = (5054375:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1862
  · change upperValue ((point (1863)+point ((1863)+1))/2) ≤ payment (1863)
    have hp : payment 1863 = (315040209580:ℝ)/1000000000000 := rfl
    have hx : (point 1863+point 1864)/2 = (5056429:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1863
  · change upperValue ((point (1864)+point ((1864)+1))/2) ≤ payment (1864)
    have hp : payment 1864 = (313318608636:ℝ)/1000000000000 := rfl
    have hx : (point 1864+point 1865)/2 = (1686161:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1864
  · change upperValue ((point (1865)+point ((1865)+1))/2) ≤ payment (1865)
    have hp : payment 1865 = (311597239826:ℝ)/1000000000000 := rfl
    have hx : (point 1865+point 1866)/2 = (5060537:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1865
  · change upperValue ((point (1866)+point ((1866)+1))/2) ≤ payment (1866)
    have hp : payment 1866 = (309876101816:ℝ)/1000000000000 := rfl
    have hx : (point 1866+point 1867)/2 = (5062591:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1866
  · change upperValue ((point (1867)+point ((1867)+1))/2) ≤ payment (1867)
    have hp : payment 1867 = (308155193273:ℝ)/1000000000000 := rfl
    have hx : (point 1867+point 1868)/2 = (1688215:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1867
  · change upperValue ((point (1868)+point ((1868)+1))/2) ≤ payment (1868)
    have hp : payment 1868 = (306434512867:ℝ)/1000000000000 := rfl
    have hx : (point 1868+point 1869)/2 = (5066699:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1868
  · change upperValue ((point (1869)+point ((1869)+1))/2) ≤ payment (1869)
    have hp : payment 1869 = (304714059266:ℝ)/1000000000000 := rfl
    have hx : (point 1869+point 1870)/2 = (5068753:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1869
  · change upperValue ((point (1870)+point ((1870)+1))/2) ≤ payment (1870)
    have hp : payment 1870 = (302993831140:ℝ)/1000000000000 := rfl
    have hx : (point 1870+point 1871)/2 = (1690269:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1870
  · change upperValue ((point (1871)+point ((1871)+1))/2) ≤ payment (1871)
    have hp : payment 1871 = (301273827162:ℝ)/1000000000000 := rfl
    have hx : (point 1871+point 1872)/2 = (5072861:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1871
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_116
