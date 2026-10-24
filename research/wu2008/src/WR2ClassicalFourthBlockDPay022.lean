import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay022
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_022 (j : Fin 64) (hj : 64*22+j.val < 2540) :
    DPay (64*22+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_1408
  · exact WuPaper.ClassicalFourthNat.DPay_1409
  · exact WuPaper.ClassicalFourthNat.DPay_1410
  · exact WuPaper.ClassicalFourthNat.DPay_1411
  · exact WuPaper.ClassicalFourthNat.DPay_1412
  · exact WuPaper.ClassicalFourthNat.DPay_1413
  · exact WuPaper.ClassicalFourthNat.DPay_1414
  · exact WuPaper.ClassicalFourthNat.DPay_1415
  · exact WuPaper.ClassicalFourthNat.DPay_1416
  · exact WuPaper.ClassicalFourthNat.DPay_1417
  · exact WuPaper.ClassicalFourthNat.DPay_1418
  · exact WuPaper.ClassicalFourthNat.DPay_1419
  · exact WuPaper.ClassicalFourthNat.DPay_1420
  · exact WuPaper.ClassicalFourthNat.DPay_1421
  · exact WuPaper.ClassicalFourthNat.DPay_1422
  · exact WuPaper.ClassicalFourthNat.DPay_1423
  · exact WuPaper.ClassicalFourthNat.DPay_1424
  · exact WuPaper.ClassicalFourthNat.DPay_1425
  · exact WuPaper.ClassicalFourthNat.DPay_1426
  · exact WuPaper.ClassicalFourthNat.DPay_1427
  · exact WuPaper.ClassicalFourthNat.DPay_1428
  · exact WuPaper.ClassicalFourthNat.DPay_1429
  · exact WuPaper.ClassicalFourthNat.DPay_1430
  · exact WuPaper.ClassicalFourthNat.DPay_1431
  · exact WuPaper.ClassicalFourthNat.DPay_1432
  · exact WuPaper.ClassicalFourthNat.DPay_1433
  · exact WuPaper.ClassicalFourthNat.DPay_1434
  · exact WuPaper.ClassicalFourthNat.DPay_1435
  · exact WuPaper.ClassicalFourthNat.DPay_1436
  · exact WuPaper.ClassicalFourthNat.DPay_1437
  · exact WuPaper.ClassicalFourthNat.DPay_1438
  · exact WuPaper.ClassicalFourthNat.DPay_1439
  · exact WuPaper.ClassicalFourthNat.DPay_1440
  · exact WuPaper.ClassicalFourthNat.DPay_1441
  · exact WuPaper.ClassicalFourthNat.DPay_1442
  · exact WuPaper.ClassicalFourthNat.DPay_1443
  · exact WuPaper.ClassicalFourthNat.DPay_1444
  · exact WuPaper.ClassicalFourthNat.DPay_1445
  · exact WuPaper.ClassicalFourthNat.DPay_1446
  · exact WuPaper.ClassicalFourthNat.DPay_1447
  · exact WuPaper.ClassicalFourthNat.DPay_1448
  · exact WuPaper.ClassicalFourthNat.DPay_1449
  · exact WuPaper.ClassicalFourthNat.DPay_1450
  · exact WuPaper.ClassicalFourthNat.DPay_1451
  · exact WuPaper.ClassicalFourthNat.DPay_1452
  · exact WuPaper.ClassicalFourthNat.DPay_1453
  · exact WuPaper.ClassicalFourthNat.DPay_1454
  · exact WuPaper.ClassicalFourthNat.DPay_1455
  · exact WuPaper.ClassicalFourthNat.DPay_1456
  · exact WuPaper.ClassicalFourthNat.DPay_1457
  · exact WuPaper.ClassicalFourthNat.DPay_1458
  · exact WuPaper.ClassicalFourthNat.DPay_1459
  · exact WuPaper.ClassicalFourthNat.DPay_1460
  · exact WuPaper.ClassicalFourthNat.DPay_1461
  · exact WuPaper.ClassicalFourthNat.DPay_1462
  · exact WuPaper.ClassicalFourthNat.DPay_1463
  · exact WuPaper.ClassicalFourthNat.DPay_1464
  · exact WuPaper.ClassicalFourthNat.DPay_1465
  · exact WuPaper.ClassicalFourthNat.DPay_1466
  · exact WuPaper.ClassicalFourthNat.DPay_1467
  · exact WuPaper.ClassicalFourthNat.DPay_1468
  · exact WuPaper.ClassicalFourthNat.DPay_1469
  · exact WuPaper.ClassicalFourthNat.DPay_1470
  · exact WuPaper.ClassicalFourthNat.DPay_1471
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_022
