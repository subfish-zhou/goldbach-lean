import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints015
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_015 (j : Fin 16) : upperValue ((point (16*15+j.val)+point ((16*15+j.val)+1))/2) ≤ payment (16*15+j.val) := by
  fin_cases j
  · change upperValue ((point (240)+point ((240)+1))/2) ≤ payment (240)
    have hp : payment 240 = (5509613393495:ℝ)/1000000000000 := rfl
    have hx : (point 240+point 241)/2 = (1722787:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_240
  · change upperValue ((point (241)+point ((241)+1))/2) ≤ payment (241)
    have hp : payment 241 = (5501453541877:ℝ)/1000000000000 := rfl
    have hx : (point 241+point 242)/2 = (574947:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_241
  · change upperValue ((point (242)+point ((242)+1))/2) ≤ payment (242)
    have hp : payment 242 = (5493312118591:ℝ)/1000000000000 := rfl
    have hx : (point 242+point 243)/2 = (1726895:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_242
  · change upperValue ((point (243)+point ((243)+1))/2) ≤ payment (243)
    have hp : payment 243 = (5485189057305:ℝ)/1000000000000 := rfl
    have hx : (point 243+point 244)/2 = (1728949:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_243
  · change upperValue ((point (244)+point ((244)+1))/2) ≤ payment (244)
    have hp : payment 244 = (5477084291999:ℝ)/1000000000000 := rfl
    have hx : (point 244+point 245)/2 = (577001:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_244
  · change upperValue ((point (245)+point ((245)+1))/2) ≤ payment (245)
    have hp : payment 245 = (5468997756967:ℝ)/1000000000000 := rfl
    have hx : (point 245+point 246)/2 = (1733057:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_245
  · change upperValue ((point (246)+point ((246)+1))/2) ≤ payment (246)
    have hp : payment 246 = (5460929386815:ℝ)/1000000000000 := rfl
    have hx : (point 246+point 247)/2 = (1735111:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_246
  · change upperValue ((point (247)+point ((247)+1))/2) ≤ payment (247)
    have hp : payment 247 = (5452879116456:ℝ)/1000000000000 := rfl
    have hx : (point 247+point 248)/2 = (579055:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_247
  · change upperValue ((point (248)+point ((248)+1))/2) ≤ payment (248)
    have hp : payment 248 = (5444846881109:ℝ)/1000000000000 := rfl
    have hx : (point 248+point 249)/2 = (1739219:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_248
  · change upperValue ((point (249)+point ((249)+1))/2) ≤ payment (249)
    have hp : payment 249 = (5436832616301:ℝ)/1000000000000 := rfl
    have hx : (point 249+point 250)/2 = (1741273:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_249
  · change upperValue ((point (250)+point ((250)+1))/2) ≤ payment (250)
    have hp : payment 250 = (5428836257859:ℝ)/1000000000000 := rfl
    have hx : (point 250+point 251)/2 = (581109:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_250
  · change upperValue ((point (251)+point ((251)+1))/2) ≤ payment (251)
    have hp : payment 251 = (5420857741915:ℝ)/1000000000000 := rfl
    have hx : (point 251+point 252)/2 = (1745381:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_251
  · change upperValue ((point (252)+point ((252)+1))/2) ≤ payment (252)
    have hp : payment 252 = (5412897004898:ℝ)/1000000000000 := rfl
    have hx : (point 252+point 253)/2 = (1747435:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_252
  · change upperValue ((point (253)+point ((253)+1))/2) ≤ payment (253)
    have hp : payment 253 = (5404953983536:ℝ)/1000000000000 := rfl
    have hx : (point 253+point 254)/2 = (583163:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_253
  · change upperValue ((point (254)+point ((254)+1))/2) ≤ payment (254)
    have hp : payment 254 = (5397028614853:ℝ)/1000000000000 := rfl
    have hx : (point 254+point 255)/2 = (1751543:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_254
  · change upperValue ((point (255)+point ((255)+1))/2) ≤ payment (255)
    have hp : payment 255 = (5389120836169:ℝ)/1000000000000 := rfl
    have hx : (point 255+point 256)/2 = (1753597:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_255
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_015
