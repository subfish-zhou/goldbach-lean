import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay024
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_024 (j : Fin 64) (hj : 64*24+j.val < 10540) :
    BPay (64*24+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_1536
  · exact WuPaper.ClassicalFourthNat.BPay_1537
  · exact WuPaper.ClassicalFourthNat.BPay_1538
  · exact WuPaper.ClassicalFourthNat.BPay_1539
  · exact WuPaper.ClassicalFourthNat.BPay_1540
  · exact WuPaper.ClassicalFourthNat.BPay_1541
  · exact WuPaper.ClassicalFourthNat.BPay_1542
  · exact WuPaper.ClassicalFourthNat.BPay_1543
  · exact WuPaper.ClassicalFourthNat.BPay_1544
  · exact WuPaper.ClassicalFourthNat.BPay_1545
  · exact WuPaper.ClassicalFourthNat.BPay_1546
  · exact WuPaper.ClassicalFourthNat.BPay_1547
  · exact WuPaper.ClassicalFourthNat.BPay_1548
  · exact WuPaper.ClassicalFourthNat.BPay_1549
  · exact WuPaper.ClassicalFourthNat.BPay_1550
  · exact WuPaper.ClassicalFourthNat.BPay_1551
  · exact WuPaper.ClassicalFourthNat.BPay_1552
  · exact WuPaper.ClassicalFourthNat.BPay_1553
  · exact WuPaper.ClassicalFourthNat.BPay_1554
  · exact WuPaper.ClassicalFourthNat.BPay_1555
  · exact WuPaper.ClassicalFourthNat.BPay_1556
  · exact WuPaper.ClassicalFourthNat.BPay_1557
  · exact WuPaper.ClassicalFourthNat.BPay_1558
  · exact WuPaper.ClassicalFourthNat.BPay_1559
  · exact WuPaper.ClassicalFourthNat.BPay_1560
  · exact WuPaper.ClassicalFourthNat.BPay_1561
  · exact WuPaper.ClassicalFourthNat.BPay_1562
  · exact WuPaper.ClassicalFourthNat.BPay_1563
  · exact WuPaper.ClassicalFourthNat.BPay_1564
  · exact WuPaper.ClassicalFourthNat.BPay_1565
  · exact WuPaper.ClassicalFourthNat.BPay_1566
  · exact WuPaper.ClassicalFourthNat.BPay_1567
  · exact WuPaper.ClassicalFourthNat.BPay_1568
  · exact WuPaper.ClassicalFourthNat.BPay_1569
  · exact WuPaper.ClassicalFourthNat.BPay_1570
  · exact WuPaper.ClassicalFourthNat.BPay_1571
  · exact WuPaper.ClassicalFourthNat.BPay_1572
  · exact WuPaper.ClassicalFourthNat.BPay_1573
  · exact WuPaper.ClassicalFourthNat.BPay_1574
  · exact WuPaper.ClassicalFourthNat.BPay_1575
  · exact WuPaper.ClassicalFourthNat.BPay_1576
  · exact WuPaper.ClassicalFourthNat.BPay_1577
  · exact WuPaper.ClassicalFourthNat.BPay_1578
  · exact WuPaper.ClassicalFourthNat.BPay_1579
  · exact WuPaper.ClassicalFourthNat.BPay_1580
  · exact WuPaper.ClassicalFourthNat.BPay_1581
  · exact WuPaper.ClassicalFourthNat.BPay_1582
  · exact WuPaper.ClassicalFourthNat.BPay_1583
  · exact WuPaper.ClassicalFourthNat.BPay_1584
  · exact WuPaper.ClassicalFourthNat.BPay_1585
  · exact WuPaper.ClassicalFourthNat.BPay_1586
  · exact WuPaper.ClassicalFourthNat.BPay_1587
  · exact WuPaper.ClassicalFourthNat.BPay_1588
  · exact WuPaper.ClassicalFourthNat.BPay_1589
  · exact WuPaper.ClassicalFourthNat.BPay_1590
  · exact WuPaper.ClassicalFourthNat.BPay_1591
  · exact WuPaper.ClassicalFourthNat.BPay_1592
  · exact WuPaper.ClassicalFourthNat.BPay_1593
  · exact WuPaper.ClassicalFourthNat.BPay_1594
  · exact WuPaper.ClassicalFourthNat.BPay_1595
  · exact WuPaper.ClassicalFourthNat.BPay_1596
  · exact WuPaper.ClassicalFourthNat.BPay_1597
  · exact WuPaper.ClassicalFourthNat.BPay_1598
  · exact WuPaper.ClassicalFourthNat.BPay_1599
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_024
