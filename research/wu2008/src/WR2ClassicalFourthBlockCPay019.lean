import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay019
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_019 (j : Fin 64) (hj : 64*19+j.val < 2540) :
    CPay (64*19+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_1216
  · exact WuPaper.ClassicalFourthNat.CPay_1217
  · exact WuPaper.ClassicalFourthNat.CPay_1218
  · exact WuPaper.ClassicalFourthNat.CPay_1219
  · exact WuPaper.ClassicalFourthNat.CPay_1220
  · exact WuPaper.ClassicalFourthNat.CPay_1221
  · exact WuPaper.ClassicalFourthNat.CPay_1222
  · exact WuPaper.ClassicalFourthNat.CPay_1223
  · exact WuPaper.ClassicalFourthNat.CPay_1224
  · exact WuPaper.ClassicalFourthNat.CPay_1225
  · exact WuPaper.ClassicalFourthNat.CPay_1226
  · exact WuPaper.ClassicalFourthNat.CPay_1227
  · exact WuPaper.ClassicalFourthNat.CPay_1228
  · exact WuPaper.ClassicalFourthNat.CPay_1229
  · exact WuPaper.ClassicalFourthNat.CPay_1230
  · exact WuPaper.ClassicalFourthNat.CPay_1231
  · exact WuPaper.ClassicalFourthNat.CPay_1232
  · exact WuPaper.ClassicalFourthNat.CPay_1233
  · exact WuPaper.ClassicalFourthNat.CPay_1234
  · exact WuPaper.ClassicalFourthNat.CPay_1235
  · exact WuPaper.ClassicalFourthNat.CPay_1236
  · exact WuPaper.ClassicalFourthNat.CPay_1237
  · exact WuPaper.ClassicalFourthNat.CPay_1238
  · exact WuPaper.ClassicalFourthNat.CPay_1239
  · exact WuPaper.ClassicalFourthNat.CPay_1240
  · exact WuPaper.ClassicalFourthNat.CPay_1241
  · exact WuPaper.ClassicalFourthNat.CPay_1242
  · exact WuPaper.ClassicalFourthNat.CPay_1243
  · exact WuPaper.ClassicalFourthNat.CPay_1244
  · exact WuPaper.ClassicalFourthNat.CPay_1245
  · exact WuPaper.ClassicalFourthNat.CPay_1246
  · exact WuPaper.ClassicalFourthNat.CPay_1247
  · exact WuPaper.ClassicalFourthNat.CPay_1248
  · exact WuPaper.ClassicalFourthNat.CPay_1249
  · exact WuPaper.ClassicalFourthNat.CPay_1250
  · exact WuPaper.ClassicalFourthNat.CPay_1251
  · exact WuPaper.ClassicalFourthNat.CPay_1252
  · exact WuPaper.ClassicalFourthNat.CPay_1253
  · exact WuPaper.ClassicalFourthNat.CPay_1254
  · exact WuPaper.ClassicalFourthNat.CPay_1255
  · exact WuPaper.ClassicalFourthNat.CPay_1256
  · exact WuPaper.ClassicalFourthNat.CPay_1257
  · exact WuPaper.ClassicalFourthNat.CPay_1258
  · exact WuPaper.ClassicalFourthNat.CPay_1259
  · exact WuPaper.ClassicalFourthNat.CPay_1260
  · exact WuPaper.ClassicalFourthNat.CPay_1261
  · exact WuPaper.ClassicalFourthNat.CPay_1262
  · exact WuPaper.ClassicalFourthNat.CPay_1263
  · exact WuPaper.ClassicalFourthNat.CPay_1264
  · exact WuPaper.ClassicalFourthNat.CPay_1265
  · exact WuPaper.ClassicalFourthNat.CPay_1266
  · exact WuPaper.ClassicalFourthNat.CPay_1267
  · exact WuPaper.ClassicalFourthNat.CPay_1268
  · exact WuPaper.ClassicalFourthNat.CPay_1269
  · exact WuPaper.ClassicalFourthNat.CPay_1270
  · exact WuPaper.ClassicalFourthNat.CPay_1271
  · exact WuPaper.ClassicalFourthNat.CPay_1272
  · exact WuPaper.ClassicalFourthNat.CPay_1273
  · exact WuPaper.ClassicalFourthNat.CPay_1274
  · exact WuPaper.ClassicalFourthNat.CPay_1275
  · exact WuPaper.ClassicalFourthNat.CPay_1276
  · exact WuPaper.ClassicalFourthNat.CPay_1277
  · exact WuPaper.ClassicalFourthNat.CPay_1278
  · exact WuPaper.ClassicalFourthNat.CPay_1279
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_019
