import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay023
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_023 (j : Fin 64) (hj : 64*23+j.val < 10540) :
    BPay (64*23+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_1472
  · exact WuPaper.ClassicalFourthNat.BPay_1473
  · exact WuPaper.ClassicalFourthNat.BPay_1474
  · exact WuPaper.ClassicalFourthNat.BPay_1475
  · exact WuPaper.ClassicalFourthNat.BPay_1476
  · exact WuPaper.ClassicalFourthNat.BPay_1477
  · exact WuPaper.ClassicalFourthNat.BPay_1478
  · exact WuPaper.ClassicalFourthNat.BPay_1479
  · exact WuPaper.ClassicalFourthNat.BPay_1480
  · exact WuPaper.ClassicalFourthNat.BPay_1481
  · exact WuPaper.ClassicalFourthNat.BPay_1482
  · exact WuPaper.ClassicalFourthNat.BPay_1483
  · exact WuPaper.ClassicalFourthNat.BPay_1484
  · exact WuPaper.ClassicalFourthNat.BPay_1485
  · exact WuPaper.ClassicalFourthNat.BPay_1486
  · exact WuPaper.ClassicalFourthNat.BPay_1487
  · exact WuPaper.ClassicalFourthNat.BPay_1488
  · exact WuPaper.ClassicalFourthNat.BPay_1489
  · exact WuPaper.ClassicalFourthNat.BPay_1490
  · exact WuPaper.ClassicalFourthNat.BPay_1491
  · exact WuPaper.ClassicalFourthNat.BPay_1492
  · exact WuPaper.ClassicalFourthNat.BPay_1493
  · exact WuPaper.ClassicalFourthNat.BPay_1494
  · exact WuPaper.ClassicalFourthNat.BPay_1495
  · exact WuPaper.ClassicalFourthNat.BPay_1496
  · exact WuPaper.ClassicalFourthNat.BPay_1497
  · exact WuPaper.ClassicalFourthNat.BPay_1498
  · exact WuPaper.ClassicalFourthNat.BPay_1499
  · exact WuPaper.ClassicalFourthNat.BPay_1500
  · exact WuPaper.ClassicalFourthNat.BPay_1501
  · exact WuPaper.ClassicalFourthNat.BPay_1502
  · exact WuPaper.ClassicalFourthNat.BPay_1503
  · exact WuPaper.ClassicalFourthNat.BPay_1504
  · exact WuPaper.ClassicalFourthNat.BPay_1505
  · exact WuPaper.ClassicalFourthNat.BPay_1506
  · exact WuPaper.ClassicalFourthNat.BPay_1507
  · exact WuPaper.ClassicalFourthNat.BPay_1508
  · exact WuPaper.ClassicalFourthNat.BPay_1509
  · exact WuPaper.ClassicalFourthNat.BPay_1510
  · exact WuPaper.ClassicalFourthNat.BPay_1511
  · exact WuPaper.ClassicalFourthNat.BPay_1512
  · exact WuPaper.ClassicalFourthNat.BPay_1513
  · exact WuPaper.ClassicalFourthNat.BPay_1514
  · exact WuPaper.ClassicalFourthNat.BPay_1515
  · exact WuPaper.ClassicalFourthNat.BPay_1516
  · exact WuPaper.ClassicalFourthNat.BPay_1517
  · exact WuPaper.ClassicalFourthNat.BPay_1518
  · exact WuPaper.ClassicalFourthNat.BPay_1519
  · exact WuPaper.ClassicalFourthNat.BPay_1520
  · exact WuPaper.ClassicalFourthNat.BPay_1521
  · exact WuPaper.ClassicalFourthNat.BPay_1522
  · exact WuPaper.ClassicalFourthNat.BPay_1523
  · exact WuPaper.ClassicalFourthNat.BPay_1524
  · exact WuPaper.ClassicalFourthNat.BPay_1525
  · exact WuPaper.ClassicalFourthNat.BPay_1526
  · exact WuPaper.ClassicalFourthNat.BPay_1527
  · exact WuPaper.ClassicalFourthNat.BPay_1528
  · exact WuPaper.ClassicalFourthNat.BPay_1529
  · exact WuPaper.ClassicalFourthNat.BPay_1530
  · exact WuPaper.ClassicalFourthNat.BPay_1531
  · exact WuPaper.ClassicalFourthNat.BPay_1532
  · exact WuPaper.ClassicalFourthNat.BPay_1533
  · exact WuPaper.ClassicalFourthNat.BPay_1534
  · exact WuPaper.ClassicalFourthNat.BPay_1535
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_023
