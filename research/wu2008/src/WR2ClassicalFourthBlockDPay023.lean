import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay023
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_023 (j : Fin 64) (hj : 64*23+j.val < 2540) :
    DPay (64*23+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_1472
  · exact WuPaper.ClassicalFourthNat.DPay_1473
  · exact WuPaper.ClassicalFourthNat.DPay_1474
  · exact WuPaper.ClassicalFourthNat.DPay_1475
  · exact WuPaper.ClassicalFourthNat.DPay_1476
  · exact WuPaper.ClassicalFourthNat.DPay_1477
  · exact WuPaper.ClassicalFourthNat.DPay_1478
  · exact WuPaper.ClassicalFourthNat.DPay_1479
  · exact WuPaper.ClassicalFourthNat.DPay_1480
  · exact WuPaper.ClassicalFourthNat.DPay_1481
  · exact WuPaper.ClassicalFourthNat.DPay_1482
  · exact WuPaper.ClassicalFourthNat.DPay_1483
  · exact WuPaper.ClassicalFourthNat.DPay_1484
  · exact WuPaper.ClassicalFourthNat.DPay_1485
  · exact WuPaper.ClassicalFourthNat.DPay_1486
  · exact WuPaper.ClassicalFourthNat.DPay_1487
  · exact WuPaper.ClassicalFourthNat.DPay_1488
  · exact WuPaper.ClassicalFourthNat.DPay_1489
  · exact WuPaper.ClassicalFourthNat.DPay_1490
  · exact WuPaper.ClassicalFourthNat.DPay_1491
  · exact WuPaper.ClassicalFourthNat.DPay_1492
  · exact WuPaper.ClassicalFourthNat.DPay_1493
  · exact WuPaper.ClassicalFourthNat.DPay_1494
  · exact WuPaper.ClassicalFourthNat.DPay_1495
  · exact WuPaper.ClassicalFourthNat.DPay_1496
  · exact WuPaper.ClassicalFourthNat.DPay_1497
  · exact WuPaper.ClassicalFourthNat.DPay_1498
  · exact WuPaper.ClassicalFourthNat.DPay_1499
  · exact WuPaper.ClassicalFourthNat.DPay_1500
  · exact WuPaper.ClassicalFourthNat.DPay_1501
  · exact WuPaper.ClassicalFourthNat.DPay_1502
  · exact WuPaper.ClassicalFourthNat.DPay_1503
  · exact WuPaper.ClassicalFourthNat.DPay_1504
  · exact WuPaper.ClassicalFourthNat.DPay_1505
  · exact WuPaper.ClassicalFourthNat.DPay_1506
  · exact WuPaper.ClassicalFourthNat.DPay_1507
  · exact WuPaper.ClassicalFourthNat.DPay_1508
  · exact WuPaper.ClassicalFourthNat.DPay_1509
  · exact WuPaper.ClassicalFourthNat.DPay_1510
  · exact WuPaper.ClassicalFourthNat.DPay_1511
  · exact WuPaper.ClassicalFourthNat.DPay_1512
  · exact WuPaper.ClassicalFourthNat.DPay_1513
  · exact WuPaper.ClassicalFourthNat.DPay_1514
  · exact WuPaper.ClassicalFourthNat.DPay_1515
  · exact WuPaper.ClassicalFourthNat.DPay_1516
  · exact WuPaper.ClassicalFourthNat.DPay_1517
  · exact WuPaper.ClassicalFourthNat.DPay_1518
  · exact WuPaper.ClassicalFourthNat.DPay_1519
  · exact WuPaper.ClassicalFourthNat.DPay_1520
  · exact WuPaper.ClassicalFourthNat.DPay_1521
  · exact WuPaper.ClassicalFourthNat.DPay_1522
  · exact WuPaper.ClassicalFourthNat.DPay_1523
  · exact WuPaper.ClassicalFourthNat.DPay_1524
  · exact WuPaper.ClassicalFourthNat.DPay_1525
  · exact WuPaper.ClassicalFourthNat.DPay_1526
  · exact WuPaper.ClassicalFourthNat.DPay_1527
  · exact WuPaper.ClassicalFourthNat.DPay_1528
  · exact WuPaper.ClassicalFourthNat.DPay_1529
  · exact WuPaper.ClassicalFourthNat.DPay_1530
  · exact WuPaper.ClassicalFourthNat.DPay_1531
  · exact WuPaper.ClassicalFourthNat.DPay_1532
  · exact WuPaper.ClassicalFourthNat.DPay_1533
  · exact WuPaper.ClassicalFourthNat.DPay_1534
  · exact WuPaper.ClassicalFourthNat.DPay_1535
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_023
