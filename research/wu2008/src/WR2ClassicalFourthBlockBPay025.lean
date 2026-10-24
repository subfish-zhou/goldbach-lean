import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay025
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_025 (j : Fin 64) (hj : 64*25+j.val < 10540) :
    BPay (64*25+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_1600
  · exact WuPaper.ClassicalFourthNat.BPay_1601
  · exact WuPaper.ClassicalFourthNat.BPay_1602
  · exact WuPaper.ClassicalFourthNat.BPay_1603
  · exact WuPaper.ClassicalFourthNat.BPay_1604
  · exact WuPaper.ClassicalFourthNat.BPay_1605
  · exact WuPaper.ClassicalFourthNat.BPay_1606
  · exact WuPaper.ClassicalFourthNat.BPay_1607
  · exact WuPaper.ClassicalFourthNat.BPay_1608
  · exact WuPaper.ClassicalFourthNat.BPay_1609
  · exact WuPaper.ClassicalFourthNat.BPay_1610
  · exact WuPaper.ClassicalFourthNat.BPay_1611
  · exact WuPaper.ClassicalFourthNat.BPay_1612
  · exact WuPaper.ClassicalFourthNat.BPay_1613
  · exact WuPaper.ClassicalFourthNat.BPay_1614
  · exact WuPaper.ClassicalFourthNat.BPay_1615
  · exact WuPaper.ClassicalFourthNat.BPay_1616
  · exact WuPaper.ClassicalFourthNat.BPay_1617
  · exact WuPaper.ClassicalFourthNat.BPay_1618
  · exact WuPaper.ClassicalFourthNat.BPay_1619
  · exact WuPaper.ClassicalFourthNat.BPay_1620
  · exact WuPaper.ClassicalFourthNat.BPay_1621
  · exact WuPaper.ClassicalFourthNat.BPay_1622
  · exact WuPaper.ClassicalFourthNat.BPay_1623
  · exact WuPaper.ClassicalFourthNat.BPay_1624
  · exact WuPaper.ClassicalFourthNat.BPay_1625
  · exact WuPaper.ClassicalFourthNat.BPay_1626
  · exact WuPaper.ClassicalFourthNat.BPay_1627
  · exact WuPaper.ClassicalFourthNat.BPay_1628
  · exact WuPaper.ClassicalFourthNat.BPay_1629
  · exact WuPaper.ClassicalFourthNat.BPay_1630
  · exact WuPaper.ClassicalFourthNat.BPay_1631
  · exact WuPaper.ClassicalFourthNat.BPay_1632
  · exact WuPaper.ClassicalFourthNat.BPay_1633
  · exact WuPaper.ClassicalFourthNat.BPay_1634
  · exact WuPaper.ClassicalFourthNat.BPay_1635
  · exact WuPaper.ClassicalFourthNat.BPay_1636
  · exact WuPaper.ClassicalFourthNat.BPay_1637
  · exact WuPaper.ClassicalFourthNat.BPay_1638
  · exact WuPaper.ClassicalFourthNat.BPay_1639
  · exact WuPaper.ClassicalFourthNat.BPay_1640
  · exact WuPaper.ClassicalFourthNat.BPay_1641
  · exact WuPaper.ClassicalFourthNat.BPay_1642
  · exact WuPaper.ClassicalFourthNat.BPay_1643
  · exact WuPaper.ClassicalFourthNat.BPay_1644
  · exact WuPaper.ClassicalFourthNat.BPay_1645
  · exact WuPaper.ClassicalFourthNat.BPay_1646
  · exact WuPaper.ClassicalFourthNat.BPay_1647
  · exact WuPaper.ClassicalFourthNat.BPay_1648
  · exact WuPaper.ClassicalFourthNat.BPay_1649
  · exact WuPaper.ClassicalFourthNat.BPay_1650
  · exact WuPaper.ClassicalFourthNat.BPay_1651
  · exact WuPaper.ClassicalFourthNat.BPay_1652
  · exact WuPaper.ClassicalFourthNat.BPay_1653
  · exact WuPaper.ClassicalFourthNat.BPay_1654
  · exact WuPaper.ClassicalFourthNat.BPay_1655
  · exact WuPaper.ClassicalFourthNat.BPay_1656
  · exact WuPaper.ClassicalFourthNat.BPay_1657
  · exact WuPaper.ClassicalFourthNat.BPay_1658
  · exact WuPaper.ClassicalFourthNat.BPay_1659
  · exact WuPaper.ClassicalFourthNat.BPay_1660
  · exact WuPaper.ClassicalFourthNat.BPay_1661
  · exact WuPaper.ClassicalFourthNat.BPay_1662
  · exact WuPaper.ClassicalFourthNat.BPay_1663
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_025
