import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay019
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_019 (j : Fin 64) (hj : 64*19+j.val < 10540) :
    BPay (64*19+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_1216
  · exact WuPaper.ClassicalFourthNat.BPay_1217
  · exact WuPaper.ClassicalFourthNat.BPay_1218
  · exact WuPaper.ClassicalFourthNat.BPay_1219
  · exact WuPaper.ClassicalFourthNat.BPay_1220
  · exact WuPaper.ClassicalFourthNat.BPay_1221
  · exact WuPaper.ClassicalFourthNat.BPay_1222
  · exact WuPaper.ClassicalFourthNat.BPay_1223
  · exact WuPaper.ClassicalFourthNat.BPay_1224
  · exact WuPaper.ClassicalFourthNat.BPay_1225
  · exact WuPaper.ClassicalFourthNat.BPay_1226
  · exact WuPaper.ClassicalFourthNat.BPay_1227
  · exact WuPaper.ClassicalFourthNat.BPay_1228
  · exact WuPaper.ClassicalFourthNat.BPay_1229
  · exact WuPaper.ClassicalFourthNat.BPay_1230
  · exact WuPaper.ClassicalFourthNat.BPay_1231
  · exact WuPaper.ClassicalFourthNat.BPay_1232
  · exact WuPaper.ClassicalFourthNat.BPay_1233
  · exact WuPaper.ClassicalFourthNat.BPay_1234
  · exact WuPaper.ClassicalFourthNat.BPay_1235
  · exact WuPaper.ClassicalFourthNat.BPay_1236
  · exact WuPaper.ClassicalFourthNat.BPay_1237
  · exact WuPaper.ClassicalFourthNat.BPay_1238
  · exact WuPaper.ClassicalFourthNat.BPay_1239
  · exact WuPaper.ClassicalFourthNat.BPay_1240
  · exact WuPaper.ClassicalFourthNat.BPay_1241
  · exact WuPaper.ClassicalFourthNat.BPay_1242
  · exact WuPaper.ClassicalFourthNat.BPay_1243
  · exact WuPaper.ClassicalFourthNat.BPay_1244
  · exact WuPaper.ClassicalFourthNat.BPay_1245
  · exact WuPaper.ClassicalFourthNat.BPay_1246
  · exact WuPaper.ClassicalFourthNat.BPay_1247
  · exact WuPaper.ClassicalFourthNat.BPay_1248
  · exact WuPaper.ClassicalFourthNat.BPay_1249
  · exact WuPaper.ClassicalFourthNat.BPay_1250
  · exact WuPaper.ClassicalFourthNat.BPay_1251
  · exact WuPaper.ClassicalFourthNat.BPay_1252
  · exact WuPaper.ClassicalFourthNat.BPay_1253
  · exact WuPaper.ClassicalFourthNat.BPay_1254
  · exact WuPaper.ClassicalFourthNat.BPay_1255
  · exact WuPaper.ClassicalFourthNat.BPay_1256
  · exact WuPaper.ClassicalFourthNat.BPay_1257
  · exact WuPaper.ClassicalFourthNat.BPay_1258
  · exact WuPaper.ClassicalFourthNat.BPay_1259
  · exact WuPaper.ClassicalFourthNat.BPay_1260
  · exact WuPaper.ClassicalFourthNat.BPay_1261
  · exact WuPaper.ClassicalFourthNat.BPay_1262
  · exact WuPaper.ClassicalFourthNat.BPay_1263
  · exact WuPaper.ClassicalFourthNat.BPay_1264
  · exact WuPaper.ClassicalFourthNat.BPay_1265
  · exact WuPaper.ClassicalFourthNat.BPay_1266
  · exact WuPaper.ClassicalFourthNat.BPay_1267
  · exact WuPaper.ClassicalFourthNat.BPay_1268
  · exact WuPaper.ClassicalFourthNat.BPay_1269
  · exact WuPaper.ClassicalFourthNat.BPay_1270
  · exact WuPaper.ClassicalFourthNat.BPay_1271
  · exact WuPaper.ClassicalFourthNat.BPay_1272
  · exact WuPaper.ClassicalFourthNat.BPay_1273
  · exact WuPaper.ClassicalFourthNat.BPay_1274
  · exact WuPaper.ClassicalFourthNat.BPay_1275
  · exact WuPaper.ClassicalFourthNat.BPay_1276
  · exact WuPaper.ClassicalFourthNat.BPay_1277
  · exact WuPaper.ClassicalFourthNat.BPay_1278
  · exact WuPaper.ClassicalFourthNat.BPay_1279
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_019
