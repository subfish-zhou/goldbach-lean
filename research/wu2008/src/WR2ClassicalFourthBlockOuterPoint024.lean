import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint024
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_024 (j : Fin 64) (hj : 64*24+j.val < 10541) :
    OuterPoint (64*24+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1536
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1537
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1538
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1539
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1540
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1541
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1542
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1543
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1544
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1545
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1546
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1547
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1548
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1549
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1550
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1551
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1552
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1553
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1554
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1555
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1556
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1557
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1558
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1559
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1560
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1561
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1562
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1563
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1564
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1565
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1566
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1567
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1568
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1569
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1570
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1571
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1572
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1573
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1574
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1575
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1576
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1577
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1578
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1579
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1580
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1581
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1582
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1583
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1584
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1585
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1586
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1587
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1588
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1589
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1590
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1591
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1592
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1593
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1594
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1595
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1596
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1597
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1598
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1599
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_024
