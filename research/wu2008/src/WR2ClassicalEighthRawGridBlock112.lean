import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints112
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_112 (j : Fin 16) : upperValue ((point (16*112+j.val)+point ((16*112+j.val)+1))/2) ≤ payment (16*112+j.val) := by
  fin_cases j
  · change upperValue ((point (1792)+point ((1792)+1))/2) ≤ payment (1792)
    have hp : payment 1792 = (437951315496:ℝ)/1000000000000 := rfl
    have hx : (point 1792+point 1793)/2 = (1636865:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1792
  · change upperValue ((point (1793)+point ((1793)+1))/2) ≤ payment (1793)
    have hp : payment 1793 = (436209760732:ℝ)/1000000000000 := rfl
    have hx : (point 1793+point 1794)/2 = (4912649:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1793
  · change upperValue ((point (1794)+point ((1794)+1))/2) ≤ payment (1794)
    have hp : payment 1794 = (434468535464:ℝ)/1000000000000 := rfl
    have hx : (point 1794+point 1795)/2 = (4914703:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1794
  · change upperValue ((point (1795)+point ((1795)+1))/2) ≤ payment (1795)
    have hp : payment 1795 = (432727638280:ℝ)/1000000000000 := rfl
    have hx : (point 1795+point 1796)/2 = (1638919:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1795
  · change upperValue ((point (1796)+point ((1796)+1))/2) ≤ payment (1796)
    have hp : payment 1796 = (430987067771:ℝ)/1000000000000 := rfl
    have hx : (point 1796+point 1797)/2 = (4918811:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1796
  · change upperValue ((point (1797)+point ((1797)+1))/2) ≤ payment (1797)
    have hp : payment 1797 = (429246822527:ℝ)/1000000000000 := rfl
    have hx : (point 1797+point 1798)/2 = (4920865:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1797
  · change upperValue ((point (1798)+point ((1798)+1))/2) ≤ payment (1798)
    have hp : payment 1798 = (427506901142:ℝ)/1000000000000 := rfl
    have hx : (point 1798+point 1799)/2 = (1640973:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1798
  · change upperValue ((point (1799)+point ((1799)+1))/2) ≤ payment (1799)
    have hp : payment 1799 = (425767302207:ℝ)/1000000000000 := rfl
    have hx : (point 1799+point 1800)/2 = (4924973:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1799
  · change upperValue ((point (1800)+point ((1800)+1))/2) ≤ payment (1800)
    have hp : payment 1800 = (424028024319:ℝ)/1000000000000 := rfl
    have hx : (point 1800+point 1801)/2 = (4927027:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1800
  · change upperValue ((point (1801)+point ((1801)+1))/2) ≤ payment (1801)
    have hp : payment 1801 = (422289066074:ℝ)/1000000000000 := rfl
    have hx : (point 1801+point 1802)/2 = (1643027:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1801
  · change upperValue ((point (1802)+point ((1802)+1))/2) ≤ payment (1802)
    have hp : payment 1802 = (420550426069:ℝ)/1000000000000 := rfl
    have hx : (point 1802+point 1803)/2 = (4931135:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1802
  · change upperValue ((point (1803)+point ((1803)+1))/2) ≤ payment (1803)
    have hp : payment 1803 = (418812102902:ℝ)/1000000000000 := rfl
    have hx : (point 1803+point 1804)/2 = (4933189:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1803
  · change upperValue ((point (1804)+point ((1804)+1))/2) ≤ payment (1804)
    have hp : payment 1804 = (417074095173:ℝ)/1000000000000 := rfl
    have hx : (point 1804+point 1805)/2 = (1645081:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1804
  · change upperValue ((point (1805)+point ((1805)+1))/2) ≤ payment (1805)
    have hp : payment 1805 = (415336401483:ℝ)/1000000000000 := rfl
    have hx : (point 1805+point 1806)/2 = (4937297:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1805
  · change upperValue ((point (1806)+point ((1806)+1))/2) ≤ payment (1806)
    have hp : payment 1806 = (413599020433:ℝ)/1000000000000 := rfl
    have hx : (point 1806+point 1807)/2 = (4939351:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1806
  · change upperValue ((point (1807)+point ((1807)+1))/2) ≤ payment (1807)
    have hp : payment 1807 = (411861950629:ℝ)/1000000000000 := rfl
    have hx : (point 1807+point 1808)/2 = (1647135:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1807
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_112
