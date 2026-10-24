import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay023
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_023 (j : Fin 64) (hj : 64*23+j.val < 2540) :
    CPay (64*23+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_1472
  · exact WuPaper.ClassicalFourthNat.CPay_1473
  · exact WuPaper.ClassicalFourthNat.CPay_1474
  · exact WuPaper.ClassicalFourthNat.CPay_1475
  · exact WuPaper.ClassicalFourthNat.CPay_1476
  · exact WuPaper.ClassicalFourthNat.CPay_1477
  · exact WuPaper.ClassicalFourthNat.CPay_1478
  · exact WuPaper.ClassicalFourthNat.CPay_1479
  · exact WuPaper.ClassicalFourthNat.CPay_1480
  · exact WuPaper.ClassicalFourthNat.CPay_1481
  · exact WuPaper.ClassicalFourthNat.CPay_1482
  · exact WuPaper.ClassicalFourthNat.CPay_1483
  · exact WuPaper.ClassicalFourthNat.CPay_1484
  · exact WuPaper.ClassicalFourthNat.CPay_1485
  · exact WuPaper.ClassicalFourthNat.CPay_1486
  · exact WuPaper.ClassicalFourthNat.CPay_1487
  · exact WuPaper.ClassicalFourthNat.CPay_1488
  · exact WuPaper.ClassicalFourthNat.CPay_1489
  · exact WuPaper.ClassicalFourthNat.CPay_1490
  · exact WuPaper.ClassicalFourthNat.CPay_1491
  · exact WuPaper.ClassicalFourthNat.CPay_1492
  · exact WuPaper.ClassicalFourthNat.CPay_1493
  · exact WuPaper.ClassicalFourthNat.CPay_1494
  · exact WuPaper.ClassicalFourthNat.CPay_1495
  · exact WuPaper.ClassicalFourthNat.CPay_1496
  · exact WuPaper.ClassicalFourthNat.CPay_1497
  · exact WuPaper.ClassicalFourthNat.CPay_1498
  · exact WuPaper.ClassicalFourthNat.CPay_1499
  · exact WuPaper.ClassicalFourthNat.CPay_1500
  · exact WuPaper.ClassicalFourthNat.CPay_1501
  · exact WuPaper.ClassicalFourthNat.CPay_1502
  · exact WuPaper.ClassicalFourthNat.CPay_1503
  · exact WuPaper.ClassicalFourthNat.CPay_1504
  · exact WuPaper.ClassicalFourthNat.CPay_1505
  · exact WuPaper.ClassicalFourthNat.CPay_1506
  · exact WuPaper.ClassicalFourthNat.CPay_1507
  · exact WuPaper.ClassicalFourthNat.CPay_1508
  · exact WuPaper.ClassicalFourthNat.CPay_1509
  · exact WuPaper.ClassicalFourthNat.CPay_1510
  · exact WuPaper.ClassicalFourthNat.CPay_1511
  · exact WuPaper.ClassicalFourthNat.CPay_1512
  · exact WuPaper.ClassicalFourthNat.CPay_1513
  · exact WuPaper.ClassicalFourthNat.CPay_1514
  · exact WuPaper.ClassicalFourthNat.CPay_1515
  · exact WuPaper.ClassicalFourthNat.CPay_1516
  · exact WuPaper.ClassicalFourthNat.CPay_1517
  · exact WuPaper.ClassicalFourthNat.CPay_1518
  · exact WuPaper.ClassicalFourthNat.CPay_1519
  · exact WuPaper.ClassicalFourthNat.CPay_1520
  · exact WuPaper.ClassicalFourthNat.CPay_1521
  · exact WuPaper.ClassicalFourthNat.CPay_1522
  · exact WuPaper.ClassicalFourthNat.CPay_1523
  · exact WuPaper.ClassicalFourthNat.CPay_1524
  · exact WuPaper.ClassicalFourthNat.CPay_1525
  · exact WuPaper.ClassicalFourthNat.CPay_1526
  · exact WuPaper.ClassicalFourthNat.CPay_1527
  · exact WuPaper.ClassicalFourthNat.CPay_1528
  · exact WuPaper.ClassicalFourthNat.CPay_1529
  · exact WuPaper.ClassicalFourthNat.CPay_1530
  · exact WuPaper.ClassicalFourthNat.CPay_1531
  · exact WuPaper.ClassicalFourthNat.CPay_1532
  · exact WuPaper.ClassicalFourthNat.CPay_1533
  · exact WuPaper.ClassicalFourthNat.CPay_1534
  · exact WuPaper.ClassicalFourthNat.CPay_1535
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_023
