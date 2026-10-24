import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay022
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_022 (j : Fin 64) (hj : 64*22+j.val < 10540) :
    OuterPay (64*22+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_1408
  · exact WuPaper.ClassicalFourthNat.outerPay_1409
  · exact WuPaper.ClassicalFourthNat.outerPay_1410
  · exact WuPaper.ClassicalFourthNat.outerPay_1411
  · exact WuPaper.ClassicalFourthNat.outerPay_1412
  · exact WuPaper.ClassicalFourthNat.outerPay_1413
  · exact WuPaper.ClassicalFourthNat.outerPay_1414
  · exact WuPaper.ClassicalFourthNat.outerPay_1415
  · exact WuPaper.ClassicalFourthNat.outerPay_1416
  · exact WuPaper.ClassicalFourthNat.outerPay_1417
  · exact WuPaper.ClassicalFourthNat.outerPay_1418
  · exact WuPaper.ClassicalFourthNat.outerPay_1419
  · exact WuPaper.ClassicalFourthNat.outerPay_1420
  · exact WuPaper.ClassicalFourthNat.outerPay_1421
  · exact WuPaper.ClassicalFourthNat.outerPay_1422
  · exact WuPaper.ClassicalFourthNat.outerPay_1423
  · exact WuPaper.ClassicalFourthNat.outerPay_1424
  · exact WuPaper.ClassicalFourthNat.outerPay_1425
  · exact WuPaper.ClassicalFourthNat.outerPay_1426
  · exact WuPaper.ClassicalFourthNat.outerPay_1427
  · exact WuPaper.ClassicalFourthNat.outerPay_1428
  · exact WuPaper.ClassicalFourthNat.outerPay_1429
  · exact WuPaper.ClassicalFourthNat.outerPay_1430
  · exact WuPaper.ClassicalFourthNat.outerPay_1431
  · exact WuPaper.ClassicalFourthNat.outerPay_1432
  · exact WuPaper.ClassicalFourthNat.outerPay_1433
  · exact WuPaper.ClassicalFourthNat.outerPay_1434
  · exact WuPaper.ClassicalFourthNat.outerPay_1435
  · exact WuPaper.ClassicalFourthNat.outerPay_1436
  · exact WuPaper.ClassicalFourthNat.outerPay_1437
  · exact WuPaper.ClassicalFourthNat.outerPay_1438
  · exact WuPaper.ClassicalFourthNat.outerPay_1439
  · exact WuPaper.ClassicalFourthNat.outerPay_1440
  · exact WuPaper.ClassicalFourthNat.outerPay_1441
  · exact WuPaper.ClassicalFourthNat.outerPay_1442
  · exact WuPaper.ClassicalFourthNat.outerPay_1443
  · exact WuPaper.ClassicalFourthNat.outerPay_1444
  · exact WuPaper.ClassicalFourthNat.outerPay_1445
  · exact WuPaper.ClassicalFourthNat.outerPay_1446
  · exact WuPaper.ClassicalFourthNat.outerPay_1447
  · exact WuPaper.ClassicalFourthNat.outerPay_1448
  · exact WuPaper.ClassicalFourthNat.outerPay_1449
  · exact WuPaper.ClassicalFourthNat.outerPay_1450
  · exact WuPaper.ClassicalFourthNat.outerPay_1451
  · exact WuPaper.ClassicalFourthNat.outerPay_1452
  · exact WuPaper.ClassicalFourthNat.outerPay_1453
  · exact WuPaper.ClassicalFourthNat.outerPay_1454
  · exact WuPaper.ClassicalFourthNat.outerPay_1455
  · exact WuPaper.ClassicalFourthNat.outerPay_1456
  · exact WuPaper.ClassicalFourthNat.outerPay_1457
  · exact WuPaper.ClassicalFourthNat.outerPay_1458
  · exact WuPaper.ClassicalFourthNat.outerPay_1459
  · exact WuPaper.ClassicalFourthNat.outerPay_1460
  · exact WuPaper.ClassicalFourthNat.outerPay_1461
  · exact WuPaper.ClassicalFourthNat.outerPay_1462
  · exact WuPaper.ClassicalFourthNat.outerPay_1463
  · exact WuPaper.ClassicalFourthNat.outerPay_1464
  · exact WuPaper.ClassicalFourthNat.outerPay_1465
  · exact WuPaper.ClassicalFourthNat.outerPay_1466
  · exact WuPaper.ClassicalFourthNat.outerPay_1467
  · exact WuPaper.ClassicalFourthNat.outerPay_1468
  · exact WuPaper.ClassicalFourthNat.outerPay_1469
  · exact WuPaper.ClassicalFourthNat.outerPay_1470
  · exact WuPaper.ClassicalFourthNat.outerPay_1471
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_022
