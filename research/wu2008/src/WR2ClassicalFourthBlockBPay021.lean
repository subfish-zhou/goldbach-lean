import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay021
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_021 (j : Fin 64) (hj : 64*21+j.val < 10540) :
    BPay (64*21+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_1344
  · exact WuPaper.ClassicalFourthNat.BPay_1345
  · exact WuPaper.ClassicalFourthNat.BPay_1346
  · exact WuPaper.ClassicalFourthNat.BPay_1347
  · exact WuPaper.ClassicalFourthNat.BPay_1348
  · exact WuPaper.ClassicalFourthNat.BPay_1349
  · exact WuPaper.ClassicalFourthNat.BPay_1350
  · exact WuPaper.ClassicalFourthNat.BPay_1351
  · exact WuPaper.ClassicalFourthNat.BPay_1352
  · exact WuPaper.ClassicalFourthNat.BPay_1353
  · exact WuPaper.ClassicalFourthNat.BPay_1354
  · exact WuPaper.ClassicalFourthNat.BPay_1355
  · exact WuPaper.ClassicalFourthNat.BPay_1356
  · exact WuPaper.ClassicalFourthNat.BPay_1357
  · exact WuPaper.ClassicalFourthNat.BPay_1358
  · exact WuPaper.ClassicalFourthNat.BPay_1359
  · exact WuPaper.ClassicalFourthNat.BPay_1360
  · exact WuPaper.ClassicalFourthNat.BPay_1361
  · exact WuPaper.ClassicalFourthNat.BPay_1362
  · exact WuPaper.ClassicalFourthNat.BPay_1363
  · exact WuPaper.ClassicalFourthNat.BPay_1364
  · exact WuPaper.ClassicalFourthNat.BPay_1365
  · exact WuPaper.ClassicalFourthNat.BPay_1366
  · exact WuPaper.ClassicalFourthNat.BPay_1367
  · exact WuPaper.ClassicalFourthNat.BPay_1368
  · exact WuPaper.ClassicalFourthNat.BPay_1369
  · exact WuPaper.ClassicalFourthNat.BPay_1370
  · exact WuPaper.ClassicalFourthNat.BPay_1371
  · exact WuPaper.ClassicalFourthNat.BPay_1372
  · exact WuPaper.ClassicalFourthNat.BPay_1373
  · exact WuPaper.ClassicalFourthNat.BPay_1374
  · exact WuPaper.ClassicalFourthNat.BPay_1375
  · exact WuPaper.ClassicalFourthNat.BPay_1376
  · exact WuPaper.ClassicalFourthNat.BPay_1377
  · exact WuPaper.ClassicalFourthNat.BPay_1378
  · exact WuPaper.ClassicalFourthNat.BPay_1379
  · exact WuPaper.ClassicalFourthNat.BPay_1380
  · exact WuPaper.ClassicalFourthNat.BPay_1381
  · exact WuPaper.ClassicalFourthNat.BPay_1382
  · exact WuPaper.ClassicalFourthNat.BPay_1383
  · exact WuPaper.ClassicalFourthNat.BPay_1384
  · exact WuPaper.ClassicalFourthNat.BPay_1385
  · exact WuPaper.ClassicalFourthNat.BPay_1386
  · exact WuPaper.ClassicalFourthNat.BPay_1387
  · exact WuPaper.ClassicalFourthNat.BPay_1388
  · exact WuPaper.ClassicalFourthNat.BPay_1389
  · exact WuPaper.ClassicalFourthNat.BPay_1390
  · exact WuPaper.ClassicalFourthNat.BPay_1391
  · exact WuPaper.ClassicalFourthNat.BPay_1392
  · exact WuPaper.ClassicalFourthNat.BPay_1393
  · exact WuPaper.ClassicalFourthNat.BPay_1394
  · exact WuPaper.ClassicalFourthNat.BPay_1395
  · exact WuPaper.ClassicalFourthNat.BPay_1396
  · exact WuPaper.ClassicalFourthNat.BPay_1397
  · exact WuPaper.ClassicalFourthNat.BPay_1398
  · exact WuPaper.ClassicalFourthNat.BPay_1399
  · exact WuPaper.ClassicalFourthNat.BPay_1400
  · exact WuPaper.ClassicalFourthNat.BPay_1401
  · exact WuPaper.ClassicalFourthNat.BPay_1402
  · exact WuPaper.ClassicalFourthNat.BPay_1403
  · exact WuPaper.ClassicalFourthNat.BPay_1404
  · exact WuPaper.ClassicalFourthNat.BPay_1405
  · exact WuPaper.ClassicalFourthNat.BPay_1406
  · exact WuPaper.ClassicalFourthNat.BPay_1407
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_021
