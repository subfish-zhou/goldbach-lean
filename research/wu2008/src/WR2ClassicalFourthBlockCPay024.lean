import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay024
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_024 (j : Fin 64) (hj : 64*24+j.val < 2540) :
    CPay (64*24+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_1536
  · exact WuPaper.ClassicalFourthNat.CPay_1537
  · exact WuPaper.ClassicalFourthNat.CPay_1538
  · exact WuPaper.ClassicalFourthNat.CPay_1539
  · exact WuPaper.ClassicalFourthNat.CPay_1540
  · exact WuPaper.ClassicalFourthNat.CPay_1541
  · exact WuPaper.ClassicalFourthNat.CPay_1542
  · exact WuPaper.ClassicalFourthNat.CPay_1543
  · exact WuPaper.ClassicalFourthNat.CPay_1544
  · exact WuPaper.ClassicalFourthNat.CPay_1545
  · exact WuPaper.ClassicalFourthNat.CPay_1546
  · exact WuPaper.ClassicalFourthNat.CPay_1547
  · exact WuPaper.ClassicalFourthNat.CPay_1548
  · exact WuPaper.ClassicalFourthNat.CPay_1549
  · exact WuPaper.ClassicalFourthNat.CPay_1550
  · exact WuPaper.ClassicalFourthNat.CPay_1551
  · exact WuPaper.ClassicalFourthNat.CPay_1552
  · exact WuPaper.ClassicalFourthNat.CPay_1553
  · exact WuPaper.ClassicalFourthNat.CPay_1554
  · exact WuPaper.ClassicalFourthNat.CPay_1555
  · exact WuPaper.ClassicalFourthNat.CPay_1556
  · exact WuPaper.ClassicalFourthNat.CPay_1557
  · exact WuPaper.ClassicalFourthNat.CPay_1558
  · exact WuPaper.ClassicalFourthNat.CPay_1559
  · exact WuPaper.ClassicalFourthNat.CPay_1560
  · exact WuPaper.ClassicalFourthNat.CPay_1561
  · exact WuPaper.ClassicalFourthNat.CPay_1562
  · exact WuPaper.ClassicalFourthNat.CPay_1563
  · exact WuPaper.ClassicalFourthNat.CPay_1564
  · exact WuPaper.ClassicalFourthNat.CPay_1565
  · exact WuPaper.ClassicalFourthNat.CPay_1566
  · exact WuPaper.ClassicalFourthNat.CPay_1567
  · exact WuPaper.ClassicalFourthNat.CPay_1568
  · exact WuPaper.ClassicalFourthNat.CPay_1569
  · exact WuPaper.ClassicalFourthNat.CPay_1570
  · exact WuPaper.ClassicalFourthNat.CPay_1571
  · exact WuPaper.ClassicalFourthNat.CPay_1572
  · exact WuPaper.ClassicalFourthNat.CPay_1573
  · exact WuPaper.ClassicalFourthNat.CPay_1574
  · exact WuPaper.ClassicalFourthNat.CPay_1575
  · exact WuPaper.ClassicalFourthNat.CPay_1576
  · exact WuPaper.ClassicalFourthNat.CPay_1577
  · exact WuPaper.ClassicalFourthNat.CPay_1578
  · exact WuPaper.ClassicalFourthNat.CPay_1579
  · exact WuPaper.ClassicalFourthNat.CPay_1580
  · exact WuPaper.ClassicalFourthNat.CPay_1581
  · exact WuPaper.ClassicalFourthNat.CPay_1582
  · exact WuPaper.ClassicalFourthNat.CPay_1583
  · exact WuPaper.ClassicalFourthNat.CPay_1584
  · exact WuPaper.ClassicalFourthNat.CPay_1585
  · exact WuPaper.ClassicalFourthNat.CPay_1586
  · exact WuPaper.ClassicalFourthNat.CPay_1587
  · exact WuPaper.ClassicalFourthNat.CPay_1588
  · exact WuPaper.ClassicalFourthNat.CPay_1589
  · exact WuPaper.ClassicalFourthNat.CPay_1590
  · exact WuPaper.ClassicalFourthNat.CPay_1591
  · exact WuPaper.ClassicalFourthNat.CPay_1592
  · exact WuPaper.ClassicalFourthNat.CPay_1593
  · exact WuPaper.ClassicalFourthNat.CPay_1594
  · exact WuPaper.ClassicalFourthNat.CPay_1595
  · exact WuPaper.ClassicalFourthNat.CPay_1596
  · exact WuPaper.ClassicalFourthNat.CPay_1597
  · exact WuPaper.ClassicalFourthNat.CPay_1598
  · exact WuPaper.ClassicalFourthNat.CPay_1599
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_024
