import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay022
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_022 (j : Fin 64) (hj : 64*22+j.val < 10540) :
    BPay (64*22+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_1408
  · exact WuPaper.ClassicalFourthNat.BPay_1409
  · exact WuPaper.ClassicalFourthNat.BPay_1410
  · exact WuPaper.ClassicalFourthNat.BPay_1411
  · exact WuPaper.ClassicalFourthNat.BPay_1412
  · exact WuPaper.ClassicalFourthNat.BPay_1413
  · exact WuPaper.ClassicalFourthNat.BPay_1414
  · exact WuPaper.ClassicalFourthNat.BPay_1415
  · exact WuPaper.ClassicalFourthNat.BPay_1416
  · exact WuPaper.ClassicalFourthNat.BPay_1417
  · exact WuPaper.ClassicalFourthNat.BPay_1418
  · exact WuPaper.ClassicalFourthNat.BPay_1419
  · exact WuPaper.ClassicalFourthNat.BPay_1420
  · exact WuPaper.ClassicalFourthNat.BPay_1421
  · exact WuPaper.ClassicalFourthNat.BPay_1422
  · exact WuPaper.ClassicalFourthNat.BPay_1423
  · exact WuPaper.ClassicalFourthNat.BPay_1424
  · exact WuPaper.ClassicalFourthNat.BPay_1425
  · exact WuPaper.ClassicalFourthNat.BPay_1426
  · exact WuPaper.ClassicalFourthNat.BPay_1427
  · exact WuPaper.ClassicalFourthNat.BPay_1428
  · exact WuPaper.ClassicalFourthNat.BPay_1429
  · exact WuPaper.ClassicalFourthNat.BPay_1430
  · exact WuPaper.ClassicalFourthNat.BPay_1431
  · exact WuPaper.ClassicalFourthNat.BPay_1432
  · exact WuPaper.ClassicalFourthNat.BPay_1433
  · exact WuPaper.ClassicalFourthNat.BPay_1434
  · exact WuPaper.ClassicalFourthNat.BPay_1435
  · exact WuPaper.ClassicalFourthNat.BPay_1436
  · exact WuPaper.ClassicalFourthNat.BPay_1437
  · exact WuPaper.ClassicalFourthNat.BPay_1438
  · exact WuPaper.ClassicalFourthNat.BPay_1439
  · exact WuPaper.ClassicalFourthNat.BPay_1440
  · exact WuPaper.ClassicalFourthNat.BPay_1441
  · exact WuPaper.ClassicalFourthNat.BPay_1442
  · exact WuPaper.ClassicalFourthNat.BPay_1443
  · exact WuPaper.ClassicalFourthNat.BPay_1444
  · exact WuPaper.ClassicalFourthNat.BPay_1445
  · exact WuPaper.ClassicalFourthNat.BPay_1446
  · exact WuPaper.ClassicalFourthNat.BPay_1447
  · exact WuPaper.ClassicalFourthNat.BPay_1448
  · exact WuPaper.ClassicalFourthNat.BPay_1449
  · exact WuPaper.ClassicalFourthNat.BPay_1450
  · exact WuPaper.ClassicalFourthNat.BPay_1451
  · exact WuPaper.ClassicalFourthNat.BPay_1452
  · exact WuPaper.ClassicalFourthNat.BPay_1453
  · exact WuPaper.ClassicalFourthNat.BPay_1454
  · exact WuPaper.ClassicalFourthNat.BPay_1455
  · exact WuPaper.ClassicalFourthNat.BPay_1456
  · exact WuPaper.ClassicalFourthNat.BPay_1457
  · exact WuPaper.ClassicalFourthNat.BPay_1458
  · exact WuPaper.ClassicalFourthNat.BPay_1459
  · exact WuPaper.ClassicalFourthNat.BPay_1460
  · exact WuPaper.ClassicalFourthNat.BPay_1461
  · exact WuPaper.ClassicalFourthNat.BPay_1462
  · exact WuPaper.ClassicalFourthNat.BPay_1463
  · exact WuPaper.ClassicalFourthNat.BPay_1464
  · exact WuPaper.ClassicalFourthNat.BPay_1465
  · exact WuPaper.ClassicalFourthNat.BPay_1466
  · exact WuPaper.ClassicalFourthNat.BPay_1467
  · exact WuPaper.ClassicalFourthNat.BPay_1468
  · exact WuPaper.ClassicalFourthNat.BPay_1469
  · exact WuPaper.ClassicalFourthNat.BPay_1470
  · exact WuPaper.ClassicalFourthNat.BPay_1471
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_022
