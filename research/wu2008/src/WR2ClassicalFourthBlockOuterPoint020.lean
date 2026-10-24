import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint020
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_020 (j : Fin 64) (hj : 64*20+j.val < 10541) :
    OuterPoint (64*20+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1280
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1281
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1282
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1283
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1284
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1285
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1286
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1287
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1288
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1289
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1290
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1291
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1292
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1293
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1294
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1295
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1296
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1297
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1298
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1299
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1300
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1301
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1302
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1303
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1304
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1305
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1306
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1307
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1308
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1309
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1310
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1311
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1312
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1313
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1314
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1315
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1316
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1317
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1318
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1319
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1320
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1321
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1322
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1323
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1324
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1325
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1326
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1327
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1328
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1329
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1330
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1331
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1332
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1333
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1334
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1335
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1336
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1337
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1338
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1339
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1340
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1341
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1342
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1343
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_020
