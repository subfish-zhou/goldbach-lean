import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints119
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_119 (j : Fin 16) : upperValue ((point (16*119+j.val)+point ((16*119+j.val)+1))/2) ≤ payment (16*119+j.val) := by
  fin_cases j
  · change upperValue ((point (1904)+point ((1904)+1))/2) ≤ payment (1904)
    have hp : payment 1904 = (244630799605:ℝ)/1000000000000 := rfl
    have hx : (point 1904+point 1905)/2 = (5140643:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1904
  · change upperValue ((point (1905)+point ((1905)+1))/2) ≤ payment (1905)
    have hp : payment 1905 = (242917632511:ℝ)/1000000000000 := rfl
    have hx : (point 1905+point 1906)/2 = (5142697:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1905
  · change upperValue ((point (1906)+point ((1906)+1))/2) ≤ payment (1906)
    have hp : payment 1906 = (241204643625:ℝ)/1000000000000 := rfl
    have hx : (point 1906+point 1907)/2 = (1714917:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1906
  · change upperValue ((point (1907)+point ((1907)+1))/2) ≤ payment (1907)
    have hp : payment 1907 = (239491831648:ℝ)/1000000000000 := rfl
    have hx : (point 1907+point 1908)/2 = (5146805:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1907
  · change upperValue ((point (1908)+point ((1908)+1))/2) ≤ payment (1908)
    have hp : payment 1908 = (237779195284:ℝ)/1000000000000 := rfl
    have hx : (point 1908+point 1909)/2 = (5148859:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1908
  · change upperValue ((point (1909)+point ((1909)+1))/2) ≤ payment (1909)
    have hp : payment 1909 = (236066733239:ℝ)/1000000000000 := rfl
    have hx : (point 1909+point 1910)/2 = (1716971:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1909
  · change upperValue ((point (1910)+point ((1910)+1))/2) ≤ payment (1910)
    have hp : payment 1910 = (234354444216:ℝ)/1000000000000 := rfl
    have hx : (point 1910+point 1911)/2 = (5152967:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1910
  · change upperValue ((point (1911)+point ((1911)+1))/2) ≤ payment (1911)
    have hp : payment 1911 = (232642326923:ℝ)/1000000000000 := rfl
    have hx : (point 1911+point 1912)/2 = (5155021:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1911
  · change upperValue ((point (1912)+point ((1912)+1))/2) ≤ payment (1912)
    have hp : payment 1912 = (230930380066:ℝ)/1000000000000 := rfl
    have hx : (point 1912+point 1913)/2 = (1719025:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1912
  · change upperValue ((point (1913)+point ((1913)+1))/2) ≤ payment (1913)
    have hp : payment 1913 = (229218602352:ℝ)/1000000000000 := rfl
    have hx : (point 1913+point 1914)/2 = (5159129:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1913
  · change upperValue ((point (1914)+point ((1914)+1))/2) ≤ payment (1914)
    have hp : payment 1914 = (227506992491:ℝ)/1000000000000 := rfl
    have hx : (point 1914+point 1915)/2 = (5161183:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1914
  · change upperValue ((point (1915)+point ((1915)+1))/2) ≤ payment (1915)
    have hp : payment 1915 = (225795549191:ℝ)/1000000000000 := rfl
    have hx : (point 1915+point 1916)/2 = (1721079:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1915
  · change upperValue ((point (1916)+point ((1916)+1))/2) ≤ payment (1916)
    have hp : payment 1916 = (224084271162:ℝ)/1000000000000 := rfl
    have hx : (point 1916+point 1917)/2 = (5165291:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1916
  · change upperValue ((point (1917)+point ((1917)+1))/2) ≤ payment (1917)
    have hp : payment 1917 = (222373157115:ℝ)/1000000000000 := rfl
    have hx : (point 1917+point 1918)/2 = (5167345:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1917
  · change upperValue ((point (1918)+point ((1918)+1))/2) ≤ payment (1918)
    have hp : payment 1918 = (220662205762:ℝ)/1000000000000 := rfl
    have hx : (point 1918+point 1919)/2 = (1723133:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1918
  · change upperValue ((point (1919)+point ((1919)+1))/2) ≤ payment (1919)
    have hp : payment 1919 = (218951415816:ℝ)/1000000000000 := rfl
    have hx : (point 1919+point 1920)/2 = (5171453:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1919
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_119
