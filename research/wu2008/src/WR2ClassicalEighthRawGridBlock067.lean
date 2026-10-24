import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints067
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_067 (j : Fin 16) : upperValue ((point (16*67+j.val)+point ((16*67+j.val)+1))/2) ≤ payment (16*67+j.val) := by
  fin_cases j
  · change upperValue ((point (1072)+point ((1072)+1))/2) ≤ payment (1072)
    have hp : payment 1072 = (1888584341654:ℝ)/1000000000000 := rfl
    have hx : (point 1072+point 1073)/2 = (1143905:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1072
  · change upperValue ((point (1073)+point ((1073)+1))/2) ≤ payment (1073)
    have hp : payment 1073 = (1886094634251:ℝ)/1000000000000 := rfl
    have hx : (point 1073+point 1074)/2 = (3433769:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1073
  · change upperValue ((point (1074)+point ((1074)+1))/2) ≤ payment (1074)
    have hp : payment 1074 = (1883607011151:ℝ)/1000000000000 := rfl
    have hx : (point 1074+point 1075)/2 = (3435823:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1074
  · change upperValue ((point (1075)+point ((1075)+1))/2) ≤ payment (1075)
    have hp : payment 1075 = (1881121467939:ℝ)/1000000000000 := rfl
    have hx : (point 1075+point 1076)/2 = (1145959:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1075
  · change upperValue ((point (1076)+point ((1076)+1))/2) ≤ payment (1076)
    have hp : payment 1076 = (1878638000206:ℝ)/1000000000000 := rfl
    have hx : (point 1076+point 1077)/2 = (3439931:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1076
  · change upperValue ((point (1077)+point ((1077)+1))/2) ≤ payment (1077)
    have hp : payment 1077 = (1876156603558:ℝ)/1000000000000 := rfl
    have hx : (point 1077+point 1078)/2 = (3441985:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1077
  · change upperValue ((point (1078)+point ((1078)+1))/2) ≤ payment (1078)
    have hp : payment 1078 = (1873677273606:ℝ)/1000000000000 := rfl
    have hx : (point 1078+point 1079)/2 = (1148013:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1078
  · change upperValue ((point (1079)+point ((1079)+1))/2) ≤ payment (1079)
    have hp : payment 1079 = (1871200005975:ℝ)/1000000000000 := rfl
    have hx : (point 1079+point 1080)/2 = (3446093:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1079
  · change upperValue ((point (1080)+point ((1080)+1))/2) ≤ payment (1080)
    have hp : payment 1080 = (1868724796297:ℝ)/1000000000000 := rfl
    have hx : (point 1080+point 1081)/2 = (3448147:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1080
  · change upperValue ((point (1081)+point ((1081)+1))/2) ≤ payment (1081)
    have hp : payment 1081 = (1866251640215:ℝ)/1000000000000 := rfl
    have hx : (point 1081+point 1082)/2 = (1150067:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1081
  · change upperValue ((point (1082)+point ((1082)+1))/2) ≤ payment (1082)
    have hp : payment 1082 = (1863780533380:ℝ)/1000000000000 := rfl
    have hx : (point 1082+point 1083)/2 = (3452255:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1082
  · change upperValue ((point (1083)+point ((1083)+1))/2) ≤ payment (1083)
    have hp : payment 1083 = (1861311471456:ℝ)/1000000000000 := rfl
    have hx : (point 1083+point 1084)/2 = (3454309:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1083
  · change upperValue ((point (1084)+point ((1084)+1))/2) ≤ payment (1084)
    have hp : payment 1084 = (1858844450114:ℝ)/1000000000000 := rfl
    have hx : (point 1084+point 1085)/2 = (1152121:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1084
  · change upperValue ((point (1085)+point ((1085)+1))/2) ≤ payment (1085)
    have hp : payment 1085 = (1856379465035:ℝ)/1000000000000 := rfl
    have hx : (point 1085+point 1086)/2 = (3458417:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1085
  · change upperValue ((point (1086)+point ((1086)+1))/2) ≤ payment (1086)
    have hp : payment 1086 = (1853916511910:ℝ)/1000000000000 := rfl
    have hx : (point 1086+point 1087)/2 = (3460471:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1086
  · change upperValue ((point (1087)+point ((1087)+1))/2) ≤ payment (1087)
    have hp : payment 1087 = (1851455586440:ℝ)/1000000000000 := rfl
    have hx : (point 1087+point 1088)/2 = (1154175:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1087
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_067
