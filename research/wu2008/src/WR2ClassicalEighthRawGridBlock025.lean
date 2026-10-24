import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints025
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_025 (j : Fin 16) : upperValue ((point (16*25+j.val)+point ((16*25+j.val)+1))/2) ≤ payment (16*25+j.val) := by
  fin_cases j
  · change upperValue ((point (400)+point ((400)+1))/2) ≤ payment (400)
    have hp : payment 400 = (4400981201945:ℝ)/1000000000000 := rfl
    have hx : (point 400+point 401)/2 = (683809:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_400
  · change upperValue ((point (401)+point ((401)+1))/2) ≤ payment (401)
    have hp : payment 401 = (4395096639965:ℝ)/1000000000000 := rfl
    have hx : (point 401+point 402)/2 = (2053481:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_401
  · change upperValue ((point (402)+point ((402)+1))/2) ≤ payment (402)
    have hp : payment 402 = (4389222918823:ℝ)/1000000000000 := rfl
    have hx : (point 402+point 403)/2 = (2055535:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_402
  · change upperValue ((point (403)+point ((403)+1))/2) ≤ payment (403)
    have hp : payment 403 = (4383360005426:ℝ)/1000000000000 := rfl
    have hx : (point 403+point 404)/2 = (685863:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_403
  · change upperValue ((point (404)+point ((404)+1))/2) ≤ payment (404)
    have hp : payment 404 = (4377507866812:ℝ)/1000000000000 := rfl
    have hx : (point 404+point 405)/2 = (2059643:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_404
  · change upperValue ((point (405)+point ((405)+1))/2) ≤ payment (405)
    have hp : payment 405 = (4371666470152:ℝ)/1000000000000 := rfl
    have hx : (point 405+point 406)/2 = (2061697:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_405
  · change upperValue ((point (406)+point ((406)+1))/2) ≤ payment (406)
    have hp : payment 406 = (4365835782746:ℝ)/1000000000000 := rfl
    have hx : (point 406+point 407)/2 = (687917:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_406
  · change upperValue ((point (407)+point ((407)+1))/2) ≤ payment (407)
    have hp : payment 407 = (4360015772023:ℝ)/1000000000000 := rfl
    have hx : (point 407+point 408)/2 = (2065805:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_407
  · change upperValue ((point (408)+point ((408)+1))/2) ≤ payment (408)
    have hp : payment 408 = (4354206405542:ℝ)/1000000000000 := rfl
    have hx : (point 408+point 409)/2 = (2067859:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_408
  · change upperValue ((point (409)+point ((409)+1))/2) ≤ payment (409)
    have hp : payment 409 = (4348407650990:ℝ)/1000000000000 := rfl
    have hx : (point 409+point 410)/2 = (689971:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_409
  · change upperValue ((point (410)+point ((410)+1))/2) ≤ payment (410)
    have hp : payment 410 = (4342619476181:ℝ)/1000000000000 := rfl
    have hx : (point 410+point 411)/2 = (2071967:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_410
  · change upperValue ((point (411)+point ((411)+1))/2) ≤ payment (411)
    have hp : payment 411 = (4336841849056:ℝ)/1000000000000 := rfl
    have hx : (point 411+point 412)/2 = (2074021:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_411
  · change upperValue ((point (412)+point ((412)+1))/2) ≤ payment (412)
    have hp : payment 412 = (4331074737684:ℝ)/1000000000000 := rfl
    have hx : (point 412+point 413)/2 = (692025:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_412
  · change upperValue ((point (413)+point ((413)+1))/2) ≤ payment (413)
    have hp : payment 413 = (4325318110257:ℝ)/1000000000000 := rfl
    have hx : (point 413+point 414)/2 = (2078129:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_413
  · change upperValue ((point (414)+point ((414)+1))/2) ≤ payment (414)
    have hp : payment 414 = (4319571935093:ℝ)/1000000000000 := rfl
    have hx : (point 414+point 415)/2 = (2080183:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_414
  · change upperValue ((point (415)+point ((415)+1))/2) ≤ payment (415)
    have hp : payment 415 = (4313836180637:ℝ)/1000000000000 := rfl
    have hx : (point 415+point 416)/2 = (694079:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_415
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_025
