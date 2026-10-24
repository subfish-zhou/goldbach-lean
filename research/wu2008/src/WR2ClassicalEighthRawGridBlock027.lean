import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints027
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_027 (j : Fin 16) : upperValue ((point (16*27+j.val)+point ((16*27+j.val)+1))/2) ≤ payment (16*27+j.val) := by
  fin_cases j
  · change upperValue ((point (432)+point ((432)+1))/2) ≤ payment (432)
    have hp : payment 432 = (4217892735151:ℝ)/1000000000000 := rfl
    have hx : (point 432+point 433)/2 = (2117155:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_432
  · change upperValue ((point (433)+point ((433)+1))/2) ≤ payment (433)
    have hp : payment 433 = (4212339295486:ℝ)/1000000000000 := rfl
    have hx : (point 433+point 434)/2 = (706403:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_433
  · change upperValue ((point (434)+point ((434)+1))/2) ≤ payment (434)
    have hp : payment 434 = (4206795699802:ℝ)/1000000000000 := rfl
    have hx : (point 434+point 435)/2 = (2121263:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_434
  · change upperValue ((point (435)+point ((435)+1))/2) ≤ payment (435)
    have hp : payment 435 = (4201261918907:ℝ)/1000000000000 := rfl
    have hx : (point 435+point 436)/2 = (2123317:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_435
  · change upperValue ((point (436)+point ((436)+1))/2) ≤ payment (436)
    have hp : payment 436 = (4195737923722:ℝ)/1000000000000 := rfl
    have hx : (point 436+point 437)/2 = (708457:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_436
  · change upperValue ((point (437)+point ((437)+1))/2) ≤ payment (437)
    have hp : payment 437 = (4190223685281:ℝ)/1000000000000 := rfl
    have hx : (point 437+point 438)/2 = (2127425:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_437
  · change upperValue ((point (438)+point ((438)+1))/2) ≤ payment (438)
    have hp : payment 438 = (4184719174726:ℝ)/1000000000000 := rfl
    have hx : (point 438+point 439)/2 = (2129479:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_438
  · change upperValue ((point (439)+point ((439)+1))/2) ≤ payment (439)
    have hp : payment 439 = (4179224363312:ℝ)/1000000000000 := rfl
    have hx : (point 439+point 440)/2 = (710511:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_439
  · change upperValue ((point (440)+point ((440)+1))/2) ≤ payment (440)
    have hp : payment 440 = (4173739222405:ℝ)/1000000000000 := rfl
    have hx : (point 440+point 441)/2 = (2133587:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_440
  · change upperValue ((point (441)+point ((441)+1))/2) ≤ payment (441)
    have hp : payment 441 = (4168263723477:ℝ)/1000000000000 := rfl
    have hx : (point 441+point 442)/2 = (2135641:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_441
  · change upperValue ((point (442)+point ((442)+1))/2) ≤ payment (442)
    have hp : payment 442 = (4162797838113:ℝ)/1000000000000 := rfl
    have hx : (point 442+point 443)/2 = (712565:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_442
  · change upperValue ((point (443)+point ((443)+1))/2) ≤ payment (443)
    have hp : payment 443 = (4157341538005:ℝ)/1000000000000 := rfl
    have hx : (point 443+point 444)/2 = (2139749:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_443
  · change upperValue ((point (444)+point ((444)+1))/2) ≤ payment (444)
    have hp : payment 444 = (4151894794953:ℝ)/1000000000000 := rfl
    have hx : (point 444+point 445)/2 = (2141803:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_444
  · change upperValue ((point (445)+point ((445)+1))/2) ≤ payment (445)
    have hp : payment 445 = (4146457580865:ℝ)/1000000000000 := rfl
    have hx : (point 445+point 446)/2 = (714619:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_445
  · change upperValue ((point (446)+point ((446)+1))/2) ≤ payment (446)
    have hp : payment 446 = (4141029867754:ℝ)/1000000000000 := rfl
    have hx : (point 446+point 447)/2 = (2145911:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_446
  · change upperValue ((point (447)+point ((447)+1))/2) ≤ payment (447)
    have hp : payment 447 = (4135611627743:ℝ)/1000000000000 := rfl
    have hx : (point 447+point 448)/2 = (2147965:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_447
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_027
