import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints017
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_017 (j : Fin 16) : upperValue ((point (16*17+j.val)+point ((16*17+j.val)+1))/2) ≤ payment (16*17+j.val) := by
  fin_cases j
  · change upperValue ((point (272)+point ((272)+1))/2) ≤ payment (272)
    have hp : payment 272 = (5257320522797:ℝ)/1000000000000 := rfl
    have hx : (point 272+point 273)/2 = (1788515:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_272
  · change upperValue ((point (273)+point ((273)+1))/2) ≤ payment (273)
    have hp : payment 273 = (5249718971291:ℝ)/1000000000000 := rfl
    have hx : (point 273+point 274)/2 = (1790569:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_273
  · change upperValue ((point (274)+point ((274)+1))/2) ≤ payment (274)
    have hp : payment 274 = (5242133872580:ℝ)/1000000000000 := rfl
    have hx : (point 274+point 275)/2 = (597541:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_274
  · change upperValue ((point (275)+point ((275)+1))/2) ≤ payment (275)
    have hp : payment 275 = (5234565169526:ℝ)/1000000000000 := rfl
    have hx : (point 275+point 276)/2 = (1794677:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_275
  · change upperValue ((point (276)+point ((276)+1))/2) ≤ payment (276)
    have hp : payment 276 = (5227012805253:ℝ)/1000000000000 := rfl
    have hx : (point 276+point 277)/2 = (1796731:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_276
  · change upperValue ((point (277)+point ((277)+1))/2) ≤ payment (277)
    have hp : payment 277 = (5219476723144:ℝ)/1000000000000 := rfl
    have hx : (point 277+point 278)/2 = (599595:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_277
  · change upperValue ((point (278)+point ((278)+1))/2) ≤ payment (278)
    have hp : payment 278 = (5211956866841:ℝ)/1000000000000 := rfl
    have hx : (point 278+point 279)/2 = (1800839:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_278
  · change upperValue ((point (279)+point ((279)+1))/2) ≤ payment (279)
    have hp : payment 279 = (5204453180239:ℝ)/1000000000000 := rfl
    have hx : (point 279+point 280)/2 = (1802893:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_279
  · change upperValue ((point (280)+point ((280)+1))/2) ≤ payment (280)
    have hp : payment 280 = (5196965607491:ℝ)/1000000000000 := rfl
    have hx : (point 280+point 281)/2 = (601649:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_280
  · change upperValue ((point (281)+point ((281)+1))/2) ≤ payment (281)
    have hp : payment 281 = (5189494093003:ℝ)/1000000000000 := rfl
    have hx : (point 281+point 282)/2 = (1807001:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_281
  · change upperValue ((point (282)+point ((282)+1))/2) ≤ payment (282)
    have hp : payment 282 = (5182038581431:ℝ)/1000000000000 := rfl
    have hx : (point 282+point 283)/2 = (1809055:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_282
  · change upperValue ((point (283)+point ((283)+1))/2) ≤ payment (283)
    have hp : payment 283 = (5174599017684:ℝ)/1000000000000 := rfl
    have hx : (point 283+point 284)/2 = (603703:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_283
  · change upperValue ((point (284)+point ((284)+1))/2) ≤ payment (284)
    have hp : payment 284 = (5167175346917:ℝ)/1000000000000 := rfl
    have hx : (point 284+point 285)/2 = (1813163:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_284
  · change upperValue ((point (285)+point ((285)+1))/2) ≤ payment (285)
    have hp : payment 285 = (5159767514537:ℝ)/1000000000000 := rfl
    have hx : (point 285+point 286)/2 = (1815217:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_285
  · change upperValue ((point (286)+point ((286)+1))/2) ≤ payment (286)
    have hp : payment 286 = (5152375466193:ℝ)/1000000000000 := rfl
    have hx : (point 286+point 287)/2 = (605757:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_286
  · change upperValue ((point (287)+point ((287)+1))/2) ≤ payment (287)
    have hp : payment 287 = (5144999147782:ℝ)/1000000000000 := rfl
    have hx : (point 287+point 288)/2 = (1819325:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_287
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_017
