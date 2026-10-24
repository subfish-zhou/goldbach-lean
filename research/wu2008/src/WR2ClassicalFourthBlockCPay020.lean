import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay020
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_020 (j : Fin 64) (hj : 64*20+j.val < 2540) :
    CPay (64*20+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_1280
  · exact WuPaper.ClassicalFourthNat.CPay_1281
  · exact WuPaper.ClassicalFourthNat.CPay_1282
  · exact WuPaper.ClassicalFourthNat.CPay_1283
  · exact WuPaper.ClassicalFourthNat.CPay_1284
  · exact WuPaper.ClassicalFourthNat.CPay_1285
  · exact WuPaper.ClassicalFourthNat.CPay_1286
  · exact WuPaper.ClassicalFourthNat.CPay_1287
  · exact WuPaper.ClassicalFourthNat.CPay_1288
  · exact WuPaper.ClassicalFourthNat.CPay_1289
  · exact WuPaper.ClassicalFourthNat.CPay_1290
  · exact WuPaper.ClassicalFourthNat.CPay_1291
  · exact WuPaper.ClassicalFourthNat.CPay_1292
  · exact WuPaper.ClassicalFourthNat.CPay_1293
  · exact WuPaper.ClassicalFourthNat.CPay_1294
  · exact WuPaper.ClassicalFourthNat.CPay_1295
  · exact WuPaper.ClassicalFourthNat.CPay_1296
  · exact WuPaper.ClassicalFourthNat.CPay_1297
  · exact WuPaper.ClassicalFourthNat.CPay_1298
  · exact WuPaper.ClassicalFourthNat.CPay_1299
  · exact WuPaper.ClassicalFourthNat.CPay_1300
  · exact WuPaper.ClassicalFourthNat.CPay_1301
  · exact WuPaper.ClassicalFourthNat.CPay_1302
  · exact WuPaper.ClassicalFourthNat.CPay_1303
  · exact WuPaper.ClassicalFourthNat.CPay_1304
  · exact WuPaper.ClassicalFourthNat.CPay_1305
  · exact WuPaper.ClassicalFourthNat.CPay_1306
  · exact WuPaper.ClassicalFourthNat.CPay_1307
  · exact WuPaper.ClassicalFourthNat.CPay_1308
  · exact WuPaper.ClassicalFourthNat.CPay_1309
  · exact WuPaper.ClassicalFourthNat.CPay_1310
  · exact WuPaper.ClassicalFourthNat.CPay_1311
  · exact WuPaper.ClassicalFourthNat.CPay_1312
  · exact WuPaper.ClassicalFourthNat.CPay_1313
  · exact WuPaper.ClassicalFourthNat.CPay_1314
  · exact WuPaper.ClassicalFourthNat.CPay_1315
  · exact WuPaper.ClassicalFourthNat.CPay_1316
  · exact WuPaper.ClassicalFourthNat.CPay_1317
  · exact WuPaper.ClassicalFourthNat.CPay_1318
  · exact WuPaper.ClassicalFourthNat.CPay_1319
  · exact WuPaper.ClassicalFourthNat.CPay_1320
  · exact WuPaper.ClassicalFourthNat.CPay_1321
  · exact WuPaper.ClassicalFourthNat.CPay_1322
  · exact WuPaper.ClassicalFourthNat.CPay_1323
  · exact WuPaper.ClassicalFourthNat.CPay_1324
  · exact WuPaper.ClassicalFourthNat.CPay_1325
  · exact WuPaper.ClassicalFourthNat.CPay_1326
  · exact WuPaper.ClassicalFourthNat.CPay_1327
  · exact WuPaper.ClassicalFourthNat.CPay_1328
  · exact WuPaper.ClassicalFourthNat.CPay_1329
  · exact WuPaper.ClassicalFourthNat.CPay_1330
  · exact WuPaper.ClassicalFourthNat.CPay_1331
  · exact WuPaper.ClassicalFourthNat.CPay_1332
  · exact WuPaper.ClassicalFourthNat.CPay_1333
  · exact WuPaper.ClassicalFourthNat.CPay_1334
  · exact WuPaper.ClassicalFourthNat.CPay_1335
  · exact WuPaper.ClassicalFourthNat.CPay_1336
  · exact WuPaper.ClassicalFourthNat.CPay_1337
  · exact WuPaper.ClassicalFourthNat.CPay_1338
  · exact WuPaper.ClassicalFourthNat.CPay_1339
  · exact WuPaper.ClassicalFourthNat.CPay_1340
  · exact WuPaper.ClassicalFourthNat.CPay_1341
  · exact WuPaper.ClassicalFourthNat.CPay_1342
  · exact WuPaper.ClassicalFourthNat.CPay_1343
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_020
