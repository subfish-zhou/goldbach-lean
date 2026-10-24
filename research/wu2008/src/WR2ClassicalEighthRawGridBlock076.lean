import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints076
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_076 (j : Fin 16) : upperValue ((point (16*76+j.val)+point ((16*76+j.val)+1))/2) ≤ payment (16*76+j.val) := by
  fin_cases j
  · change upperValue ((point (1216)+point ((1216)+1))/2) ≤ payment (1216)
    have hp : payment 1216 = (1549530858095:ℝ)/1000000000000 := rfl
    have hx : (point 1216+point 1217)/2 = (1242497:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1216
  · change upperValue ((point (1217)+point ((1217)+1))/2) ≤ payment (1217)
    have hp : payment 1217 = (1547300172997:ℝ)/1000000000000 := rfl
    have hx : (point 1217+point 1218)/2 = (3729545:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1217
  · change upperValue ((point (1218)+point ((1218)+1))/2) ≤ payment (1218)
    have hp : payment 1218 = (1545071025106:ℝ)/1000000000000 := rfl
    have hx : (point 1218+point 1219)/2 = (3731599:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1218
  · change upperValue ((point (1219)+point ((1219)+1))/2) ≤ payment (1219)
    have hp : payment 1219 = (1542843411165:ℝ)/1000000000000 := rfl
    have hx : (point 1219+point 1220)/2 = (1244551:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1219
  · change upperValue ((point (1220)+point ((1220)+1))/2) ≤ payment (1220)
    have hp : payment 1220 = (1540617327924:ℝ)/1000000000000 := rfl
    have hx : (point 1220+point 1221)/2 = (3735707:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1220
  · change upperValue ((point (1221)+point ((1221)+1))/2) ≤ payment (1221)
    have hp : payment 1221 = (1538392772139:ℝ)/1000000000000 := rfl
    have hx : (point 1221+point 1222)/2 = (3737761:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1221
  · change upperValue ((point (1222)+point ((1222)+1))/2) ≤ payment (1222)
    have hp : payment 1222 = (1536169740573:ℝ)/1000000000000 := rfl
    have hx : (point 1222+point 1223)/2 = (1246605:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1222
  · change upperValue ((point (1223)+point ((1223)+1))/2) ≤ payment (1223)
    have hp : payment 1223 = (1533948229995:ℝ)/1000000000000 := rfl
    have hx : (point 1223+point 1224)/2 = (3741869:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1223
  · change upperValue ((point (1224)+point ((1224)+1))/2) ≤ payment (1224)
    have hp : payment 1224 = (1531728237180:ℝ)/1000000000000 := rfl
    have hx : (point 1224+point 1225)/2 = (3743923:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1224
  · change upperValue ((point (1225)+point ((1225)+1))/2) ≤ payment (1225)
    have hp : payment 1225 = (1529509758911:ℝ)/1000000000000 := rfl
    have hx : (point 1225+point 1226)/2 = (1248659:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1225
  · change upperValue ((point (1226)+point ((1226)+1))/2) ≤ payment (1226)
    have hp : payment 1226 = (1527292791975:ℝ)/1000000000000 := rfl
    have hx : (point 1226+point 1227)/2 = (3748031:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1226
  · change upperValue ((point (1227)+point ((1227)+1))/2) ≤ payment (1227)
    have hp : payment 1227 = (1525077333168:ℝ)/1000000000000 := rfl
    have hx : (point 1227+point 1228)/2 = (3750085:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1227
  · change upperValue ((point (1228)+point ((1228)+1))/2) ≤ payment (1228)
    have hp : payment 1228 = (1522863379290:ℝ)/1000000000000 := rfl
    have hx : (point 1228+point 1229)/2 = (1250713:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1228
  · change upperValue ((point (1229)+point ((1229)+1))/2) ≤ payment (1229)
    have hp : payment 1229 = (1520650927148:ℝ)/1000000000000 := rfl
    have hx : (point 1229+point 1230)/2 = (3754193:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1229
  · change upperValue ((point (1230)+point ((1230)+1))/2) ≤ payment (1230)
    have hp : payment 1230 = (1518439973556:ℝ)/1000000000000 := rfl
    have hx : (point 1230+point 1231)/2 = (3756247:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1230
  · change upperValue ((point (1231)+point ((1231)+1))/2) ≤ payment (1231)
    have hp : payment 1231 = (1516230515333:ℝ)/1000000000000 := rfl
    have hx : (point 1231+point 1232)/2 = (1252767:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1231
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_076
