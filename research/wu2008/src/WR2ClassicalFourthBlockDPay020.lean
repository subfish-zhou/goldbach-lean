import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay020
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_020 (j : Fin 64) (hj : 64*20+j.val < 2540) :
    DPay (64*20+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_1280
  · exact WuPaper.ClassicalFourthNat.DPay_1281
  · exact WuPaper.ClassicalFourthNat.DPay_1282
  · exact WuPaper.ClassicalFourthNat.DPay_1283
  · exact WuPaper.ClassicalFourthNat.DPay_1284
  · exact WuPaper.ClassicalFourthNat.DPay_1285
  · exact WuPaper.ClassicalFourthNat.DPay_1286
  · exact WuPaper.ClassicalFourthNat.DPay_1287
  · exact WuPaper.ClassicalFourthNat.DPay_1288
  · exact WuPaper.ClassicalFourthNat.DPay_1289
  · exact WuPaper.ClassicalFourthNat.DPay_1290
  · exact WuPaper.ClassicalFourthNat.DPay_1291
  · exact WuPaper.ClassicalFourthNat.DPay_1292
  · exact WuPaper.ClassicalFourthNat.DPay_1293
  · exact WuPaper.ClassicalFourthNat.DPay_1294
  · exact WuPaper.ClassicalFourthNat.DPay_1295
  · exact WuPaper.ClassicalFourthNat.DPay_1296
  · exact WuPaper.ClassicalFourthNat.DPay_1297
  · exact WuPaper.ClassicalFourthNat.DPay_1298
  · exact WuPaper.ClassicalFourthNat.DPay_1299
  · exact WuPaper.ClassicalFourthNat.DPay_1300
  · exact WuPaper.ClassicalFourthNat.DPay_1301
  · exact WuPaper.ClassicalFourthNat.DPay_1302
  · exact WuPaper.ClassicalFourthNat.DPay_1303
  · exact WuPaper.ClassicalFourthNat.DPay_1304
  · exact WuPaper.ClassicalFourthNat.DPay_1305
  · exact WuPaper.ClassicalFourthNat.DPay_1306
  · exact WuPaper.ClassicalFourthNat.DPay_1307
  · exact WuPaper.ClassicalFourthNat.DPay_1308
  · exact WuPaper.ClassicalFourthNat.DPay_1309
  · exact WuPaper.ClassicalFourthNat.DPay_1310
  · exact WuPaper.ClassicalFourthNat.DPay_1311
  · exact WuPaper.ClassicalFourthNat.DPay_1312
  · exact WuPaper.ClassicalFourthNat.DPay_1313
  · exact WuPaper.ClassicalFourthNat.DPay_1314
  · exact WuPaper.ClassicalFourthNat.DPay_1315
  · exact WuPaper.ClassicalFourthNat.DPay_1316
  · exact WuPaper.ClassicalFourthNat.DPay_1317
  · exact WuPaper.ClassicalFourthNat.DPay_1318
  · exact WuPaper.ClassicalFourthNat.DPay_1319
  · exact WuPaper.ClassicalFourthNat.DPay_1320
  · exact WuPaper.ClassicalFourthNat.DPay_1321
  · exact WuPaper.ClassicalFourthNat.DPay_1322
  · exact WuPaper.ClassicalFourthNat.DPay_1323
  · exact WuPaper.ClassicalFourthNat.DPay_1324
  · exact WuPaper.ClassicalFourthNat.DPay_1325
  · exact WuPaper.ClassicalFourthNat.DPay_1326
  · exact WuPaper.ClassicalFourthNat.DPay_1327
  · exact WuPaper.ClassicalFourthNat.DPay_1328
  · exact WuPaper.ClassicalFourthNat.DPay_1329
  · exact WuPaper.ClassicalFourthNat.DPay_1330
  · exact WuPaper.ClassicalFourthNat.DPay_1331
  · exact WuPaper.ClassicalFourthNat.DPay_1332
  · exact WuPaper.ClassicalFourthNat.DPay_1333
  · exact WuPaper.ClassicalFourthNat.DPay_1334
  · exact WuPaper.ClassicalFourthNat.DPay_1335
  · exact WuPaper.ClassicalFourthNat.DPay_1336
  · exact WuPaper.ClassicalFourthNat.DPay_1337
  · exact WuPaper.ClassicalFourthNat.DPay_1338
  · exact WuPaper.ClassicalFourthNat.DPay_1339
  · exact WuPaper.ClassicalFourthNat.DPay_1340
  · exact WuPaper.ClassicalFourthNat.DPay_1341
  · exact WuPaper.ClassicalFourthNat.DPay_1342
  · exact WuPaper.ClassicalFourthNat.DPay_1343
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_020
