import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints111
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_111 (j : Fin 16) : upperValue ((point (16*111+j.val)+point ((16*111+j.val)+1))/2) ≤ payment (16*111+j.val) := by
  fin_cases j
  · change upperValue ((point (1776)+point ((1776)+1))/2) ≤ payment (1776)
    have hp : payment 1776 = (465862159559:ℝ)/1000000000000 := rfl
    have hx : (point 1776+point 1777)/2 = (4877731:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1776
  · change upperValue ((point (1777)+point ((1777)+1))/2) ≤ payment (1777)
    have hp : payment 1777 = (464115139910:ℝ)/1000000000000 := rfl
    have hx : (point 1777+point 1778)/2 = (1626595:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1777
  · change upperValue ((point (1778)+point ((1778)+1))/2) ≤ payment (1778)
    have hp : payment 1778 = (462368472508:ℝ)/1000000000000 := rfl
    have hx : (point 1778+point 1779)/2 = (4881839:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1778
  · change upperValue ((point (1779)+point ((1779)+1))/2) ≤ payment (1779)
    have hp : payment 1779 = (460622155922:ℝ)/1000000000000 := rfl
    have hx : (point 1779+point 1780)/2 = (4883893:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1779
  · change upperValue ((point (1780)+point ((1780)+1))/2) ≤ payment (1780)
    have hp : payment 1780 = (458876188721:ℝ)/1000000000000 := rfl
    have hx : (point 1780+point 1781)/2 = (1628649:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1780
  · change upperValue ((point (1781)+point ((1781)+1))/2) ≤ payment (1781)
    have hp : payment 1781 = (457130569476:ℝ)/1000000000000 := rfl
    have hx : (point 1781+point 1782)/2 = (4888001:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1781
  · change upperValue ((point (1782)+point ((1782)+1))/2) ≤ payment (1782)
    have hp : payment 1782 = (455385296760:ℝ)/1000000000000 := rfl
    have hx : (point 1782+point 1783)/2 = (4890055:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1782
  · change upperValue ((point (1783)+point ((1783)+1))/2) ≤ payment (1783)
    have hp : payment 1783 = (453640369146:ℝ)/1000000000000 := rfl
    have hx : (point 1783+point 1784)/2 = (1630703:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1783
  · change upperValue ((point (1784)+point ((1784)+1))/2) ≤ payment (1784)
    have hp : payment 1784 = (451895785209:ℝ)/1000000000000 := rfl
    have hx : (point 1784+point 1785)/2 = (4894163:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1784
  · change upperValue ((point (1785)+point ((1785)+1))/2) ≤ payment (1785)
    have hp : payment 1785 = (450151543526:ℝ)/1000000000000 := rfl
    have hx : (point 1785+point 1786)/2 = (4896217:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1785
  · change upperValue ((point (1786)+point ((1786)+1))/2) ≤ payment (1786)
    have hp : payment 1786 = (448407642673:ℝ)/1000000000000 := rfl
    have hx : (point 1786+point 1787)/2 = (1632757:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1786
  · change upperValue ((point (1787)+point ((1787)+1))/2) ≤ payment (1787)
    have hp : payment 1787 = (446664081229:ℝ)/1000000000000 := rfl
    have hx : (point 1787+point 1788)/2 = (4900325:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1787
  · change upperValue ((point (1788)+point ((1788)+1))/2) ≤ payment (1788)
    have hp : payment 1788 = (444920857775:ℝ)/1000000000000 := rfl
    have hx : (point 1788+point 1789)/2 = (4902379:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1788
  · change upperValue ((point (1789)+point ((1789)+1))/2) ≤ payment (1789)
    have hp : payment 1789 = (443177970892:ℝ)/1000000000000 := rfl
    have hx : (point 1789+point 1790)/2 = (1634811:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1789
  · change upperValue ((point (1790)+point ((1790)+1))/2) ≤ payment (1790)
    have hp : payment 1790 = (441435419161:ℝ)/1000000000000 := rfl
    have hx : (point 1790+point 1791)/2 = (4906487:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1790
  · change upperValue ((point (1791)+point ((1791)+1))/2) ≤ payment (1791)
    have hp : payment 1791 = (439693201167:ℝ)/1000000000000 := rfl
    have hx : (point 1791+point 1792)/2 = (4908541:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1791
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_111
