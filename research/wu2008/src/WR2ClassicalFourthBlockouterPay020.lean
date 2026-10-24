import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay020
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_020 (j : Fin 64) (hj : 64*20+j.val < 10540) :
    OuterPay (64*20+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_1280
  · exact WuPaper.ClassicalFourthNat.outerPay_1281
  · exact WuPaper.ClassicalFourthNat.outerPay_1282
  · exact WuPaper.ClassicalFourthNat.outerPay_1283
  · exact WuPaper.ClassicalFourthNat.outerPay_1284
  · exact WuPaper.ClassicalFourthNat.outerPay_1285
  · exact WuPaper.ClassicalFourthNat.outerPay_1286
  · exact WuPaper.ClassicalFourthNat.outerPay_1287
  · exact WuPaper.ClassicalFourthNat.outerPay_1288
  · exact WuPaper.ClassicalFourthNat.outerPay_1289
  · exact WuPaper.ClassicalFourthNat.outerPay_1290
  · exact WuPaper.ClassicalFourthNat.outerPay_1291
  · exact WuPaper.ClassicalFourthNat.outerPay_1292
  · exact WuPaper.ClassicalFourthNat.outerPay_1293
  · exact WuPaper.ClassicalFourthNat.outerPay_1294
  · exact WuPaper.ClassicalFourthNat.outerPay_1295
  · exact WuPaper.ClassicalFourthNat.outerPay_1296
  · exact WuPaper.ClassicalFourthNat.outerPay_1297
  · exact WuPaper.ClassicalFourthNat.outerPay_1298
  · exact WuPaper.ClassicalFourthNat.outerPay_1299
  · exact WuPaper.ClassicalFourthNat.outerPay_1300
  · exact WuPaper.ClassicalFourthNat.outerPay_1301
  · exact WuPaper.ClassicalFourthNat.outerPay_1302
  · exact WuPaper.ClassicalFourthNat.outerPay_1303
  · exact WuPaper.ClassicalFourthNat.outerPay_1304
  · exact WuPaper.ClassicalFourthNat.outerPay_1305
  · exact WuPaper.ClassicalFourthNat.outerPay_1306
  · exact WuPaper.ClassicalFourthNat.outerPay_1307
  · exact WuPaper.ClassicalFourthNat.outerPay_1308
  · exact WuPaper.ClassicalFourthNat.outerPay_1309
  · exact WuPaper.ClassicalFourthNat.outerPay_1310
  · exact WuPaper.ClassicalFourthNat.outerPay_1311
  · exact WuPaper.ClassicalFourthNat.outerPay_1312
  · exact WuPaper.ClassicalFourthNat.outerPay_1313
  · exact WuPaper.ClassicalFourthNat.outerPay_1314
  · exact WuPaper.ClassicalFourthNat.outerPay_1315
  · exact WuPaper.ClassicalFourthNat.outerPay_1316
  · exact WuPaper.ClassicalFourthNat.outerPay_1317
  · exact WuPaper.ClassicalFourthNat.outerPay_1318
  · exact WuPaper.ClassicalFourthNat.outerPay_1319
  · exact WuPaper.ClassicalFourthNat.outerPay_1320
  · exact WuPaper.ClassicalFourthNat.outerPay_1321
  · exact WuPaper.ClassicalFourthNat.outerPay_1322
  · exact WuPaper.ClassicalFourthNat.outerPay_1323
  · exact WuPaper.ClassicalFourthNat.outerPay_1324
  · exact WuPaper.ClassicalFourthNat.outerPay_1325
  · exact WuPaper.ClassicalFourthNat.outerPay_1326
  · exact WuPaper.ClassicalFourthNat.outerPay_1327
  · exact WuPaper.ClassicalFourthNat.outerPay_1328
  · exact WuPaper.ClassicalFourthNat.outerPay_1329
  · exact WuPaper.ClassicalFourthNat.outerPay_1330
  · exact WuPaper.ClassicalFourthNat.outerPay_1331
  · exact WuPaper.ClassicalFourthNat.outerPay_1332
  · exact WuPaper.ClassicalFourthNat.outerPay_1333
  · exact WuPaper.ClassicalFourthNat.outerPay_1334
  · exact WuPaper.ClassicalFourthNat.outerPay_1335
  · exact WuPaper.ClassicalFourthNat.outerPay_1336
  · exact WuPaper.ClassicalFourthNat.outerPay_1337
  · exact WuPaper.ClassicalFourthNat.outerPay_1338
  · exact WuPaper.ClassicalFourthNat.outerPay_1339
  · exact WuPaper.ClassicalFourthNat.outerPay_1340
  · exact WuPaper.ClassicalFourthNat.outerPay_1341
  · exact WuPaper.ClassicalFourthNat.outerPay_1342
  · exact WuPaper.ClassicalFourthNat.outerPay_1343
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_020
