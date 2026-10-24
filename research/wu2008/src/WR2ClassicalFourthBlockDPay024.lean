import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay024
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_024 (j : Fin 64) (hj : 64*24+j.val < 2540) :
    DPay (64*24+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_1536
  · exact WuPaper.ClassicalFourthNat.DPay_1537
  · exact WuPaper.ClassicalFourthNat.DPay_1538
  · exact WuPaper.ClassicalFourthNat.DPay_1539
  · exact WuPaper.ClassicalFourthNat.DPay_1540
  · exact WuPaper.ClassicalFourthNat.DPay_1541
  · exact WuPaper.ClassicalFourthNat.DPay_1542
  · exact WuPaper.ClassicalFourthNat.DPay_1543
  · exact WuPaper.ClassicalFourthNat.DPay_1544
  · exact WuPaper.ClassicalFourthNat.DPay_1545
  · exact WuPaper.ClassicalFourthNat.DPay_1546
  · exact WuPaper.ClassicalFourthNat.DPay_1547
  · exact WuPaper.ClassicalFourthNat.DPay_1548
  · exact WuPaper.ClassicalFourthNat.DPay_1549
  · exact WuPaper.ClassicalFourthNat.DPay_1550
  · exact WuPaper.ClassicalFourthNat.DPay_1551
  · exact WuPaper.ClassicalFourthNat.DPay_1552
  · exact WuPaper.ClassicalFourthNat.DPay_1553
  · exact WuPaper.ClassicalFourthNat.DPay_1554
  · exact WuPaper.ClassicalFourthNat.DPay_1555
  · exact WuPaper.ClassicalFourthNat.DPay_1556
  · exact WuPaper.ClassicalFourthNat.DPay_1557
  · exact WuPaper.ClassicalFourthNat.DPay_1558
  · exact WuPaper.ClassicalFourthNat.DPay_1559
  · exact WuPaper.ClassicalFourthNat.DPay_1560
  · exact WuPaper.ClassicalFourthNat.DPay_1561
  · exact WuPaper.ClassicalFourthNat.DPay_1562
  · exact WuPaper.ClassicalFourthNat.DPay_1563
  · exact WuPaper.ClassicalFourthNat.DPay_1564
  · exact WuPaper.ClassicalFourthNat.DPay_1565
  · exact WuPaper.ClassicalFourthNat.DPay_1566
  · exact WuPaper.ClassicalFourthNat.DPay_1567
  · exact WuPaper.ClassicalFourthNat.DPay_1568
  · exact WuPaper.ClassicalFourthNat.DPay_1569
  · exact WuPaper.ClassicalFourthNat.DPay_1570
  · exact WuPaper.ClassicalFourthNat.DPay_1571
  · exact WuPaper.ClassicalFourthNat.DPay_1572
  · exact WuPaper.ClassicalFourthNat.DPay_1573
  · exact WuPaper.ClassicalFourthNat.DPay_1574
  · exact WuPaper.ClassicalFourthNat.DPay_1575
  · exact WuPaper.ClassicalFourthNat.DPay_1576
  · exact WuPaper.ClassicalFourthNat.DPay_1577
  · exact WuPaper.ClassicalFourthNat.DPay_1578
  · exact WuPaper.ClassicalFourthNat.DPay_1579
  · exact WuPaper.ClassicalFourthNat.DPay_1580
  · exact WuPaper.ClassicalFourthNat.DPay_1581
  · exact WuPaper.ClassicalFourthNat.DPay_1582
  · exact WuPaper.ClassicalFourthNat.DPay_1583
  · exact WuPaper.ClassicalFourthNat.DPay_1584
  · exact WuPaper.ClassicalFourthNat.DPay_1585
  · exact WuPaper.ClassicalFourthNat.DPay_1586
  · exact WuPaper.ClassicalFourthNat.DPay_1587
  · exact WuPaper.ClassicalFourthNat.DPay_1588
  · exact WuPaper.ClassicalFourthNat.DPay_1589
  · exact WuPaper.ClassicalFourthNat.DPay_1590
  · exact WuPaper.ClassicalFourthNat.DPay_1591
  · exact WuPaper.ClassicalFourthNat.DPay_1592
  · exact WuPaper.ClassicalFourthNat.DPay_1593
  · exact WuPaper.ClassicalFourthNat.DPay_1594
  · exact WuPaper.ClassicalFourthNat.DPay_1595
  · exact WuPaper.ClassicalFourthNat.DPay_1596
  · exact WuPaper.ClassicalFourthNat.DPay_1597
  · exact WuPaper.ClassicalFourthNat.DPay_1598
  · exact WuPaper.ClassicalFourthNat.DPay_1599
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_024
