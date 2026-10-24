import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay024
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_024 (j : Fin 64) (hj : 64*24+j.val < 10540) :
    OuterPay (64*24+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_1536
  · exact WuPaper.ClassicalFourthNat.outerPay_1537
  · exact WuPaper.ClassicalFourthNat.outerPay_1538
  · exact WuPaper.ClassicalFourthNat.outerPay_1539
  · exact WuPaper.ClassicalFourthNat.outerPay_1540
  · exact WuPaper.ClassicalFourthNat.outerPay_1541
  · exact WuPaper.ClassicalFourthNat.outerPay_1542
  · exact WuPaper.ClassicalFourthNat.outerPay_1543
  · exact WuPaper.ClassicalFourthNat.outerPay_1544
  · exact WuPaper.ClassicalFourthNat.outerPay_1545
  · exact WuPaper.ClassicalFourthNat.outerPay_1546
  · exact WuPaper.ClassicalFourthNat.outerPay_1547
  · exact WuPaper.ClassicalFourthNat.outerPay_1548
  · exact WuPaper.ClassicalFourthNat.outerPay_1549
  · exact WuPaper.ClassicalFourthNat.outerPay_1550
  · exact WuPaper.ClassicalFourthNat.outerPay_1551
  · exact WuPaper.ClassicalFourthNat.outerPay_1552
  · exact WuPaper.ClassicalFourthNat.outerPay_1553
  · exact WuPaper.ClassicalFourthNat.outerPay_1554
  · exact WuPaper.ClassicalFourthNat.outerPay_1555
  · exact WuPaper.ClassicalFourthNat.outerPay_1556
  · exact WuPaper.ClassicalFourthNat.outerPay_1557
  · exact WuPaper.ClassicalFourthNat.outerPay_1558
  · exact WuPaper.ClassicalFourthNat.outerPay_1559
  · exact WuPaper.ClassicalFourthNat.outerPay_1560
  · exact WuPaper.ClassicalFourthNat.outerPay_1561
  · exact WuPaper.ClassicalFourthNat.outerPay_1562
  · exact WuPaper.ClassicalFourthNat.outerPay_1563
  · exact WuPaper.ClassicalFourthNat.outerPay_1564
  · exact WuPaper.ClassicalFourthNat.outerPay_1565
  · exact WuPaper.ClassicalFourthNat.outerPay_1566
  · exact WuPaper.ClassicalFourthNat.outerPay_1567
  · exact WuPaper.ClassicalFourthNat.outerPay_1568
  · exact WuPaper.ClassicalFourthNat.outerPay_1569
  · exact WuPaper.ClassicalFourthNat.outerPay_1570
  · exact WuPaper.ClassicalFourthNat.outerPay_1571
  · exact WuPaper.ClassicalFourthNat.outerPay_1572
  · exact WuPaper.ClassicalFourthNat.outerPay_1573
  · exact WuPaper.ClassicalFourthNat.outerPay_1574
  · exact WuPaper.ClassicalFourthNat.outerPay_1575
  · exact WuPaper.ClassicalFourthNat.outerPay_1576
  · exact WuPaper.ClassicalFourthNat.outerPay_1577
  · exact WuPaper.ClassicalFourthNat.outerPay_1578
  · exact WuPaper.ClassicalFourthNat.outerPay_1579
  · exact WuPaper.ClassicalFourthNat.outerPay_1580
  · exact WuPaper.ClassicalFourthNat.outerPay_1581
  · exact WuPaper.ClassicalFourthNat.outerPay_1582
  · exact WuPaper.ClassicalFourthNat.outerPay_1583
  · exact WuPaper.ClassicalFourthNat.outerPay_1584
  · exact WuPaper.ClassicalFourthNat.outerPay_1585
  · exact WuPaper.ClassicalFourthNat.outerPay_1586
  · exact WuPaper.ClassicalFourthNat.outerPay_1587
  · exact WuPaper.ClassicalFourthNat.outerPay_1588
  · exact WuPaper.ClassicalFourthNat.outerPay_1589
  · exact WuPaper.ClassicalFourthNat.outerPay_1590
  · exact WuPaper.ClassicalFourthNat.outerPay_1591
  · exact WuPaper.ClassicalFourthNat.outerPay_1592
  · exact WuPaper.ClassicalFourthNat.outerPay_1593
  · exact WuPaper.ClassicalFourthNat.outerPay_1594
  · exact WuPaper.ClassicalFourthNat.outerPay_1595
  · exact WuPaper.ClassicalFourthNat.outerPay_1596
  · exact WuPaper.ClassicalFourthNat.outerPay_1597
  · exact WuPaper.ClassicalFourthNat.outerPay_1598
  · exact WuPaper.ClassicalFourthNat.outerPay_1599
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_024
