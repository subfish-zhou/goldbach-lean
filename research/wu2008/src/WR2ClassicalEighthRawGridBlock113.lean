import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints113
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_113 (j : Fin 16) : upperValue ((point (16*113+j.val)+point ((16*113+j.val)+1))/2) ≤ payment (16*113+j.val) := by
  fin_cases j
  · change upperValue ((point (1808)+point ((1808)+1))/2) ≤ payment (1808)
    have hp : payment 1808 = (410125190672:ℝ)/1000000000000 := rfl
    have hx : (point 1808+point 1809)/2 = (4943459:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1808
  · change upperValue ((point (1809)+point ((1809)+1))/2) ≤ payment (1809)
    have hp : payment 1809 = (408388739171:ℝ)/1000000000000 := rfl
    have hx : (point 1809+point 1810)/2 = (4945513:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1809
  · change upperValue ((point (1810)+point ((1810)+1))/2) ≤ payment (1810)
    have hp : payment 1810 = (406652594730:ℝ)/1000000000000 := rfl
    have hx : (point 1810+point 1811)/2 = (1649189:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1810
  · change upperValue ((point (1811)+point ((1811)+1))/2) ≤ payment (1811)
    have hp : payment 1811 = (404916755959:ℝ)/1000000000000 := rfl
    have hx : (point 1811+point 1812)/2 = (4949621:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1811
  · change upperValue ((point (1812)+point ((1812)+1))/2) ≤ payment (1812)
    have hp : payment 1812 = (403181221466:ℝ)/1000000000000 := rfl
    have hx : (point 1812+point 1813)/2 = (4951675:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1812
  · change upperValue ((point (1813)+point ((1813)+1))/2) ≤ payment (1813)
    have hp : payment 1813 = (401445989862:ℝ)/1000000000000 := rfl
    have hx : (point 1813+point 1814)/2 = (1651243:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1813
  · change upperValue ((point (1814)+point ((1814)+1))/2) ≤ payment (1814)
    have hp : payment 1814 = (399711059757:ℝ)/1000000000000 := rfl
    have hx : (point 1814+point 1815)/2 = (4955783:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1814
  · change upperValue ((point (1815)+point ((1815)+1))/2) ≤ payment (1815)
    have hp : payment 1815 = (397976429766:ℝ)/1000000000000 := rfl
    have hx : (point 1815+point 1816)/2 = (4957837:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1815
  · change upperValue ((point (1816)+point ((1816)+1))/2) ≤ payment (1816)
    have hp : payment 1816 = (396242098502:ℝ)/1000000000000 := rfl
    have hx : (point 1816+point 1817)/2 = (1653297:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1816
  · change upperValue ((point (1817)+point ((1817)+1))/2) ≤ payment (1817)
    have hp : payment 1817 = (394508064578:ℝ)/1000000000000 := rfl
    have hx : (point 1817+point 1818)/2 = (4961945:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1817
  · change upperValue ((point (1818)+point ((1818)+1))/2) ≤ payment (1818)
    have hp : payment 1818 = (392774326613:ℝ)/1000000000000 := rfl
    have hx : (point 1818+point 1819)/2 = (4963999:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1818
  · change upperValue ((point (1819)+point ((1819)+1))/2) ≤ payment (1819)
    have hp : payment 1819 = (391040883222:ℝ)/1000000000000 := rfl
    have hx : (point 1819+point 1820)/2 = (1655351:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1819
  · change upperValue ((point (1820)+point ((1820)+1))/2) ≤ payment (1820)
    have hp : payment 1820 = (389307733025:ℝ)/1000000000000 := rfl
    have hx : (point 1820+point 1821)/2 = (4968107:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1820
  · change upperValue ((point (1821)+point ((1821)+1))/2) ≤ payment (1821)
    have hp : payment 1821 = (387574874641:ℝ)/1000000000000 := rfl
    have hx : (point 1821+point 1822)/2 = (4970161:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1821
  · change upperValue ((point (1822)+point ((1822)+1))/2) ≤ payment (1822)
    have hp : payment 1822 = (385842306690:ℝ)/1000000000000 := rfl
    have hx : (point 1822+point 1823)/2 = (1657405:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1822
  · change upperValue ((point (1823)+point ((1823)+1))/2) ≤ payment (1823)
    have hp : payment 1823 = (384110027794:ℝ)/1000000000000 := rfl
    have hx : (point 1823+point 1824)/2 = (4974269:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1823
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_113
