import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay025
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_025 (j : Fin 64) (hj : 64*25+j.val < 2540) :
    DPay (64*25+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_1600
  · exact WuPaper.ClassicalFourthNat.DPay_1601
  · exact WuPaper.ClassicalFourthNat.DPay_1602
  · exact WuPaper.ClassicalFourthNat.DPay_1603
  · exact WuPaper.ClassicalFourthNat.DPay_1604
  · exact WuPaper.ClassicalFourthNat.DPay_1605
  · exact WuPaper.ClassicalFourthNat.DPay_1606
  · exact WuPaper.ClassicalFourthNat.DPay_1607
  · exact WuPaper.ClassicalFourthNat.DPay_1608
  · exact WuPaper.ClassicalFourthNat.DPay_1609
  · exact WuPaper.ClassicalFourthNat.DPay_1610
  · exact WuPaper.ClassicalFourthNat.DPay_1611
  · exact WuPaper.ClassicalFourthNat.DPay_1612
  · exact WuPaper.ClassicalFourthNat.DPay_1613
  · exact WuPaper.ClassicalFourthNat.DPay_1614
  · exact WuPaper.ClassicalFourthNat.DPay_1615
  · exact WuPaper.ClassicalFourthNat.DPay_1616
  · exact WuPaper.ClassicalFourthNat.DPay_1617
  · exact WuPaper.ClassicalFourthNat.DPay_1618
  · exact WuPaper.ClassicalFourthNat.DPay_1619
  · exact WuPaper.ClassicalFourthNat.DPay_1620
  · exact WuPaper.ClassicalFourthNat.DPay_1621
  · exact WuPaper.ClassicalFourthNat.DPay_1622
  · exact WuPaper.ClassicalFourthNat.DPay_1623
  · exact WuPaper.ClassicalFourthNat.DPay_1624
  · exact WuPaper.ClassicalFourthNat.DPay_1625
  · exact WuPaper.ClassicalFourthNat.DPay_1626
  · exact WuPaper.ClassicalFourthNat.DPay_1627
  · exact WuPaper.ClassicalFourthNat.DPay_1628
  · exact WuPaper.ClassicalFourthNat.DPay_1629
  · exact WuPaper.ClassicalFourthNat.DPay_1630
  · exact WuPaper.ClassicalFourthNat.DPay_1631
  · exact WuPaper.ClassicalFourthNat.DPay_1632
  · exact WuPaper.ClassicalFourthNat.DPay_1633
  · exact WuPaper.ClassicalFourthNat.DPay_1634
  · exact WuPaper.ClassicalFourthNat.DPay_1635
  · exact WuPaper.ClassicalFourthNat.DPay_1636
  · exact WuPaper.ClassicalFourthNat.DPay_1637
  · exact WuPaper.ClassicalFourthNat.DPay_1638
  · exact WuPaper.ClassicalFourthNat.DPay_1639
  · exact WuPaper.ClassicalFourthNat.DPay_1640
  · exact WuPaper.ClassicalFourthNat.DPay_1641
  · exact WuPaper.ClassicalFourthNat.DPay_1642
  · exact WuPaper.ClassicalFourthNat.DPay_1643
  · exact WuPaper.ClassicalFourthNat.DPay_1644
  · exact WuPaper.ClassicalFourthNat.DPay_1645
  · exact WuPaper.ClassicalFourthNat.DPay_1646
  · exact WuPaper.ClassicalFourthNat.DPay_1647
  · exact WuPaper.ClassicalFourthNat.DPay_1648
  · exact WuPaper.ClassicalFourthNat.DPay_1649
  · exact WuPaper.ClassicalFourthNat.DPay_1650
  · exact WuPaper.ClassicalFourthNat.DPay_1651
  · exact WuPaper.ClassicalFourthNat.DPay_1652
  · exact WuPaper.ClassicalFourthNat.DPay_1653
  · exact WuPaper.ClassicalFourthNat.DPay_1654
  · exact WuPaper.ClassicalFourthNat.DPay_1655
  · exact WuPaper.ClassicalFourthNat.DPay_1656
  · exact WuPaper.ClassicalFourthNat.DPay_1657
  · exact WuPaper.ClassicalFourthNat.DPay_1658
  · exact WuPaper.ClassicalFourthNat.DPay_1659
  · exact WuPaper.ClassicalFourthNat.DPay_1660
  · exact WuPaper.ClassicalFourthNat.DPay_1661
  · exact WuPaper.ClassicalFourthNat.DPay_1662
  · exact WuPaper.ClassicalFourthNat.DPay_1663
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_025
