import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay019
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_019 (j : Fin 64) (hj : 64*19+j.val < 2540) :
    DPay (64*19+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_1216
  · exact WuPaper.ClassicalFourthNat.DPay_1217
  · exact WuPaper.ClassicalFourthNat.DPay_1218
  · exact WuPaper.ClassicalFourthNat.DPay_1219
  · exact WuPaper.ClassicalFourthNat.DPay_1220
  · exact WuPaper.ClassicalFourthNat.DPay_1221
  · exact WuPaper.ClassicalFourthNat.DPay_1222
  · exact WuPaper.ClassicalFourthNat.DPay_1223
  · exact WuPaper.ClassicalFourthNat.DPay_1224
  · exact WuPaper.ClassicalFourthNat.DPay_1225
  · exact WuPaper.ClassicalFourthNat.DPay_1226
  · exact WuPaper.ClassicalFourthNat.DPay_1227
  · exact WuPaper.ClassicalFourthNat.DPay_1228
  · exact WuPaper.ClassicalFourthNat.DPay_1229
  · exact WuPaper.ClassicalFourthNat.DPay_1230
  · exact WuPaper.ClassicalFourthNat.DPay_1231
  · exact WuPaper.ClassicalFourthNat.DPay_1232
  · exact WuPaper.ClassicalFourthNat.DPay_1233
  · exact WuPaper.ClassicalFourthNat.DPay_1234
  · exact WuPaper.ClassicalFourthNat.DPay_1235
  · exact WuPaper.ClassicalFourthNat.DPay_1236
  · exact WuPaper.ClassicalFourthNat.DPay_1237
  · exact WuPaper.ClassicalFourthNat.DPay_1238
  · exact WuPaper.ClassicalFourthNat.DPay_1239
  · exact WuPaper.ClassicalFourthNat.DPay_1240
  · exact WuPaper.ClassicalFourthNat.DPay_1241
  · exact WuPaper.ClassicalFourthNat.DPay_1242
  · exact WuPaper.ClassicalFourthNat.DPay_1243
  · exact WuPaper.ClassicalFourthNat.DPay_1244
  · exact WuPaper.ClassicalFourthNat.DPay_1245
  · exact WuPaper.ClassicalFourthNat.DPay_1246
  · exact WuPaper.ClassicalFourthNat.DPay_1247
  · exact WuPaper.ClassicalFourthNat.DPay_1248
  · exact WuPaper.ClassicalFourthNat.DPay_1249
  · exact WuPaper.ClassicalFourthNat.DPay_1250
  · exact WuPaper.ClassicalFourthNat.DPay_1251
  · exact WuPaper.ClassicalFourthNat.DPay_1252
  · exact WuPaper.ClassicalFourthNat.DPay_1253
  · exact WuPaper.ClassicalFourthNat.DPay_1254
  · exact WuPaper.ClassicalFourthNat.DPay_1255
  · exact WuPaper.ClassicalFourthNat.DPay_1256
  · exact WuPaper.ClassicalFourthNat.DPay_1257
  · exact WuPaper.ClassicalFourthNat.DPay_1258
  · exact WuPaper.ClassicalFourthNat.DPay_1259
  · exact WuPaper.ClassicalFourthNat.DPay_1260
  · exact WuPaper.ClassicalFourthNat.DPay_1261
  · exact WuPaper.ClassicalFourthNat.DPay_1262
  · exact WuPaper.ClassicalFourthNat.DPay_1263
  · exact WuPaper.ClassicalFourthNat.DPay_1264
  · exact WuPaper.ClassicalFourthNat.DPay_1265
  · exact WuPaper.ClassicalFourthNat.DPay_1266
  · exact WuPaper.ClassicalFourthNat.DPay_1267
  · exact WuPaper.ClassicalFourthNat.DPay_1268
  · exact WuPaper.ClassicalFourthNat.DPay_1269
  · exact WuPaper.ClassicalFourthNat.DPay_1270
  · exact WuPaper.ClassicalFourthNat.DPay_1271
  · exact WuPaper.ClassicalFourthNat.DPay_1272
  · exact WuPaper.ClassicalFourthNat.DPay_1273
  · exact WuPaper.ClassicalFourthNat.DPay_1274
  · exact WuPaper.ClassicalFourthNat.DPay_1275
  · exact WuPaper.ClassicalFourthNat.DPay_1276
  · exact WuPaper.ClassicalFourthNat.DPay_1277
  · exact WuPaper.ClassicalFourthNat.DPay_1278
  · exact WuPaper.ClassicalFourthNat.DPay_1279
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_019
