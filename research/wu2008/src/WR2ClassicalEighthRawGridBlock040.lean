import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints040
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_040 (j : Fin 16) : upperValue ((point (16*40+j.val)+point ((16*40+j.val)+1))/2) ≤ payment (16*40+j.val) := by
  fin_cases j
  · change upperValue ((point (640)+point ((640)+1))/2) ≤ payment (640)
    have hp : payment 640 = (3238652826200:ℝ)/1000000000000 := rfl
    have hx : (point 640+point 641)/2 = (848129:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_640
  · change upperValue ((point (641)+point ((641)+1))/2) ≤ payment (641)
    have hp : payment 641 = (3234651318179:ℝ)/1000000000000 := rfl
    have hx : (point 641+point 642)/2 = (2546441:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_641
  · change upperValue ((point (642)+point ((642)+1))/2) ≤ payment (642)
    have hp : payment 642 = (3230655384134:ℝ)/1000000000000 := rfl
    have hx : (point 642+point 643)/2 = (2548495:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_642
  · change upperValue ((point (643)+point ((643)+1))/2) ≤ payment (643)
    have hp : payment 643 = (3226665009979:ℝ)/1000000000000 := rfl
    have hx : (point 643+point 644)/2 = (850183:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_643
  · change upperValue ((point (644)+point ((644)+1))/2) ≤ payment (644)
    have hp : payment 644 = (3222680181672:ℝ)/1000000000000 := rfl
    have hx : (point 644+point 645)/2 = (2552603:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_644
  · change upperValue ((point (645)+point ((645)+1))/2) ≤ payment (645)
    have hp : payment 645 = (3218700885217:ℝ)/1000000000000 := rfl
    have hx : (point 645+point 646)/2 = (2554657:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_645
  · change upperValue ((point (646)+point ((646)+1))/2) ≤ payment (646)
    have hp : payment 646 = (3214727106661:ℝ)/1000000000000 := rfl
    have hx : (point 646+point 647)/2 = (852237:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_646
  · change upperValue ((point (647)+point ((647)+1))/2) ≤ payment (647)
    have hp : payment 647 = (3210758832094:ℝ)/1000000000000 := rfl
    have hx : (point 647+point 648)/2 = (2558765:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_647
  · change upperValue ((point (648)+point ((648)+1))/2) ≤ payment (648)
    have hp : payment 648 = (3206796047655:ℝ)/1000000000000 := rfl
    have hx : (point 648+point 649)/2 = (2560819:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_648
  · change upperValue ((point (649)+point ((649)+1))/2) ≤ payment (649)
    have hp : payment 649 = (3202838739521:ℝ)/1000000000000 := rfl
    have hx : (point 649+point 650)/2 = (854291:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_649
  · change upperValue ((point (650)+point ((650)+1))/2) ≤ payment (650)
    have hp : payment 650 = (3198886893916:ℝ)/1000000000000 := rfl
    have hx : (point 650+point 651)/2 = (2564927:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_650
  · change upperValue ((point (651)+point ((651)+1))/2) ≤ payment (651)
    have hp : payment 651 = (3194940497108:ℝ)/1000000000000 := rfl
    have hx : (point 651+point 652)/2 = (2566981:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_651
  · change upperValue ((point (652)+point ((652)+1))/2) ≤ payment (652)
    have hp : payment 652 = (3190999535406:ℝ)/1000000000000 := rfl
    have hx : (point 652+point 653)/2 = (856345:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_652
  · change upperValue ((point (653)+point ((653)+1))/2) ≤ payment (653)
    have hp : payment 653 = (3187063995165:ℝ)/1000000000000 := rfl
    have hx : (point 653+point 654)/2 = (2571089:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_653
  · change upperValue ((point (654)+point ((654)+1))/2) ≤ payment (654)
    have hp : payment 654 = (3183133862781:ℝ)/1000000000000 := rfl
    have hx : (point 654+point 655)/2 = (2573143:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_654
  · change upperValue ((point (655)+point ((655)+1))/2) ≤ payment (655)
    have hp : payment 655 = (3179209124692:ℝ)/1000000000000 := rfl
    have hx : (point 655+point 656)/2 = (858399:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_655
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_040
