import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay020
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_020 (j : Fin 64) (hj : 64*20+j.val < 10540) :
    BPay (64*20+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_1280
  · exact WuPaper.ClassicalFourthNat.BPay_1281
  · exact WuPaper.ClassicalFourthNat.BPay_1282
  · exact WuPaper.ClassicalFourthNat.BPay_1283
  · exact WuPaper.ClassicalFourthNat.BPay_1284
  · exact WuPaper.ClassicalFourthNat.BPay_1285
  · exact WuPaper.ClassicalFourthNat.BPay_1286
  · exact WuPaper.ClassicalFourthNat.BPay_1287
  · exact WuPaper.ClassicalFourthNat.BPay_1288
  · exact WuPaper.ClassicalFourthNat.BPay_1289
  · exact WuPaper.ClassicalFourthNat.BPay_1290
  · exact WuPaper.ClassicalFourthNat.BPay_1291
  · exact WuPaper.ClassicalFourthNat.BPay_1292
  · exact WuPaper.ClassicalFourthNat.BPay_1293
  · exact WuPaper.ClassicalFourthNat.BPay_1294
  · exact WuPaper.ClassicalFourthNat.BPay_1295
  · exact WuPaper.ClassicalFourthNat.BPay_1296
  · exact WuPaper.ClassicalFourthNat.BPay_1297
  · exact WuPaper.ClassicalFourthNat.BPay_1298
  · exact WuPaper.ClassicalFourthNat.BPay_1299
  · exact WuPaper.ClassicalFourthNat.BPay_1300
  · exact WuPaper.ClassicalFourthNat.BPay_1301
  · exact WuPaper.ClassicalFourthNat.BPay_1302
  · exact WuPaper.ClassicalFourthNat.BPay_1303
  · exact WuPaper.ClassicalFourthNat.BPay_1304
  · exact WuPaper.ClassicalFourthNat.BPay_1305
  · exact WuPaper.ClassicalFourthNat.BPay_1306
  · exact WuPaper.ClassicalFourthNat.BPay_1307
  · exact WuPaper.ClassicalFourthNat.BPay_1308
  · exact WuPaper.ClassicalFourthNat.BPay_1309
  · exact WuPaper.ClassicalFourthNat.BPay_1310
  · exact WuPaper.ClassicalFourthNat.BPay_1311
  · exact WuPaper.ClassicalFourthNat.BPay_1312
  · exact WuPaper.ClassicalFourthNat.BPay_1313
  · exact WuPaper.ClassicalFourthNat.BPay_1314
  · exact WuPaper.ClassicalFourthNat.BPay_1315
  · exact WuPaper.ClassicalFourthNat.BPay_1316
  · exact WuPaper.ClassicalFourthNat.BPay_1317
  · exact WuPaper.ClassicalFourthNat.BPay_1318
  · exact WuPaper.ClassicalFourthNat.BPay_1319
  · exact WuPaper.ClassicalFourthNat.BPay_1320
  · exact WuPaper.ClassicalFourthNat.BPay_1321
  · exact WuPaper.ClassicalFourthNat.BPay_1322
  · exact WuPaper.ClassicalFourthNat.BPay_1323
  · exact WuPaper.ClassicalFourthNat.BPay_1324
  · exact WuPaper.ClassicalFourthNat.BPay_1325
  · exact WuPaper.ClassicalFourthNat.BPay_1326
  · exact WuPaper.ClassicalFourthNat.BPay_1327
  · exact WuPaper.ClassicalFourthNat.BPay_1328
  · exact WuPaper.ClassicalFourthNat.BPay_1329
  · exact WuPaper.ClassicalFourthNat.BPay_1330
  · exact WuPaper.ClassicalFourthNat.BPay_1331
  · exact WuPaper.ClassicalFourthNat.BPay_1332
  · exact WuPaper.ClassicalFourthNat.BPay_1333
  · exact WuPaper.ClassicalFourthNat.BPay_1334
  · exact WuPaper.ClassicalFourthNat.BPay_1335
  · exact WuPaper.ClassicalFourthNat.BPay_1336
  · exact WuPaper.ClassicalFourthNat.BPay_1337
  · exact WuPaper.ClassicalFourthNat.BPay_1338
  · exact WuPaper.ClassicalFourthNat.BPay_1339
  · exact WuPaper.ClassicalFourthNat.BPay_1340
  · exact WuPaper.ClassicalFourthNat.BPay_1341
  · exact WuPaper.ClassicalFourthNat.BPay_1342
  · exact WuPaper.ClassicalFourthNat.BPay_1343
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_020
