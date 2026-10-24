import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints108
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_108 (j : Fin 16) : upperValue ((point (16*108+j.val)+point ((16*108+j.val)+1))/2) ≤ payment (16*108+j.val) := by
  fin_cases j
  · change upperValue ((point (1728)+point ((1728)+1))/2) ≤ payment (1728)
    have hp : payment 1728 = (550161741064:ℝ)/1000000000000 := rfl
    have hx : (point 1728+point 1729)/2 = (4779139:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1728
  · change upperValue ((point (1729)+point ((1729)+1))/2) ≤ payment (1729)
    have hp : payment 1729 = (548396103402:ℝ)/1000000000000 := rfl
    have hx : (point 1729+point 1730)/2 = (1593731:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1729
  · change upperValue ((point (1730)+point ((1730)+1))/2) ≤ payment (1730)
    have hp : payment 1730 = (546630888319:ℝ)/1000000000000 := rfl
    have hx : (point 1730+point 1731)/2 = (4783247:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1730
  · change upperValue ((point (1731)+point ((1731)+1))/2) ≤ payment (1731)
    have hp : payment 1731 = (544866094317:ℝ)/1000000000000 := rfl
    have hx : (point 1731+point 1732)/2 = (4785301:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1731
  · change upperValue ((point (1732)+point ((1732)+1))/2) ≤ payment (1732)
    have hp : payment 1732 = (543101719899:ℝ)/1000000000000 := rfl
    have hx : (point 1732+point 1733)/2 = (1595785:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1732
  · change upperValue ((point (1733)+point ((1733)+1))/2) ≤ payment (1733)
    have hp : payment 1733 = (541337763567:ℝ)/1000000000000 := rfl
    have hx : (point 1733+point 1734)/2 = (4789409:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1733
  · change upperValue ((point (1734)+point ((1734)+1))/2) ≤ payment (1734)
    have hp : payment 1734 = (539574223827:ℝ)/1000000000000 := rfl
    have hx : (point 1734+point 1735)/2 = (4791463:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1734
  · change upperValue ((point (1735)+point ((1735)+1))/2) ≤ payment (1735)
    have hp : payment 1735 = (537811099187:ℝ)/1000000000000 := rfl
    have hx : (point 1735+point 1736)/2 = (1597839:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1735
  · change upperValue ((point (1736)+point ((1736)+1))/2) ≤ payment (1736)
    have hp : payment 1736 = (536048388153:ℝ)/1000000000000 := rfl
    have hx : (point 1736+point 1737)/2 = (4795571:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1736
  · change upperValue ((point (1737)+point ((1737)+1))/2) ≤ payment (1737)
    have hp : payment 1737 = (534286089236:ℝ)/1000000000000 := rfl
    have hx : (point 1737+point 1738)/2 = (4797625:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1737
  · change upperValue ((point (1738)+point ((1738)+1))/2) ≤ payment (1738)
    have hp : payment 1738 = (532524200948:ℝ)/1000000000000 := rfl
    have hx : (point 1738+point 1739)/2 = (1599893:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1738
  · change upperValue ((point (1739)+point ((1739)+1))/2) ≤ payment (1739)
    have hp : payment 1739 = (530762721800:ℝ)/1000000000000 := rfl
    have hx : (point 1739+point 1740)/2 = (4801733:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1739
  · change upperValue ((point (1740)+point ((1740)+1))/2) ≤ payment (1740)
    have hp : payment 1740 = (529001650308:ℝ)/1000000000000 := rfl
    have hx : (point 1740+point 1741)/2 = (4803787:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1740
  · change upperValue ((point (1741)+point ((1741)+1))/2) ≤ payment (1741)
    have hp : payment 1741 = (527240984986:ℝ)/1000000000000 := rfl
    have hx : (point 1741+point 1742)/2 = (1601947:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1741
  · change upperValue ((point (1742)+point ((1742)+1))/2) ≤ payment (1742)
    have hp : payment 1742 = (525480724352:ℝ)/1000000000000 := rfl
    have hx : (point 1742+point 1743)/2 = (4807895:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1742
  · change upperValue ((point (1743)+point ((1743)+1))/2) ≤ payment (1743)
    have hp : payment 1743 = (523720866925:ℝ)/1000000000000 := rfl
    have hx : (point 1743+point 1744)/2 = (4809949:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1743
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_108
