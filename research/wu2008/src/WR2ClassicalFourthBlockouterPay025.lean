import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay025
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_025 (j : Fin 64) (hj : 64*25+j.val < 10540) :
    OuterPay (64*25+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_1600
  · exact WuPaper.ClassicalFourthNat.outerPay_1601
  · exact WuPaper.ClassicalFourthNat.outerPay_1602
  · exact WuPaper.ClassicalFourthNat.outerPay_1603
  · exact WuPaper.ClassicalFourthNat.outerPay_1604
  · exact WuPaper.ClassicalFourthNat.outerPay_1605
  · exact WuPaper.ClassicalFourthNat.outerPay_1606
  · exact WuPaper.ClassicalFourthNat.outerPay_1607
  · exact WuPaper.ClassicalFourthNat.outerPay_1608
  · exact WuPaper.ClassicalFourthNat.outerPay_1609
  · exact WuPaper.ClassicalFourthNat.outerPay_1610
  · exact WuPaper.ClassicalFourthNat.outerPay_1611
  · exact WuPaper.ClassicalFourthNat.outerPay_1612
  · exact WuPaper.ClassicalFourthNat.outerPay_1613
  · exact WuPaper.ClassicalFourthNat.outerPay_1614
  · exact WuPaper.ClassicalFourthNat.outerPay_1615
  · exact WuPaper.ClassicalFourthNat.outerPay_1616
  · exact WuPaper.ClassicalFourthNat.outerPay_1617
  · exact WuPaper.ClassicalFourthNat.outerPay_1618
  · exact WuPaper.ClassicalFourthNat.outerPay_1619
  · exact WuPaper.ClassicalFourthNat.outerPay_1620
  · exact WuPaper.ClassicalFourthNat.outerPay_1621
  · exact WuPaper.ClassicalFourthNat.outerPay_1622
  · exact WuPaper.ClassicalFourthNat.outerPay_1623
  · exact WuPaper.ClassicalFourthNat.outerPay_1624
  · exact WuPaper.ClassicalFourthNat.outerPay_1625
  · exact WuPaper.ClassicalFourthNat.outerPay_1626
  · exact WuPaper.ClassicalFourthNat.outerPay_1627
  · exact WuPaper.ClassicalFourthNat.outerPay_1628
  · exact WuPaper.ClassicalFourthNat.outerPay_1629
  · exact WuPaper.ClassicalFourthNat.outerPay_1630
  · exact WuPaper.ClassicalFourthNat.outerPay_1631
  · exact WuPaper.ClassicalFourthNat.outerPay_1632
  · exact WuPaper.ClassicalFourthNat.outerPay_1633
  · exact WuPaper.ClassicalFourthNat.outerPay_1634
  · exact WuPaper.ClassicalFourthNat.outerPay_1635
  · exact WuPaper.ClassicalFourthNat.outerPay_1636
  · exact WuPaper.ClassicalFourthNat.outerPay_1637
  · exact WuPaper.ClassicalFourthNat.outerPay_1638
  · exact WuPaper.ClassicalFourthNat.outerPay_1639
  · exact WuPaper.ClassicalFourthNat.outerPay_1640
  · exact WuPaper.ClassicalFourthNat.outerPay_1641
  · exact WuPaper.ClassicalFourthNat.outerPay_1642
  · exact WuPaper.ClassicalFourthNat.outerPay_1643
  · exact WuPaper.ClassicalFourthNat.outerPay_1644
  · exact WuPaper.ClassicalFourthNat.outerPay_1645
  · exact WuPaper.ClassicalFourthNat.outerPay_1646
  · exact WuPaper.ClassicalFourthNat.outerPay_1647
  · exact WuPaper.ClassicalFourthNat.outerPay_1648
  · exact WuPaper.ClassicalFourthNat.outerPay_1649
  · exact WuPaper.ClassicalFourthNat.outerPay_1650
  · exact WuPaper.ClassicalFourthNat.outerPay_1651
  · exact WuPaper.ClassicalFourthNat.outerPay_1652
  · exact WuPaper.ClassicalFourthNat.outerPay_1653
  · exact WuPaper.ClassicalFourthNat.outerPay_1654
  · exact WuPaper.ClassicalFourthNat.outerPay_1655
  · exact WuPaper.ClassicalFourthNat.outerPay_1656
  · exact WuPaper.ClassicalFourthNat.outerPay_1657
  · exact WuPaper.ClassicalFourthNat.outerPay_1658
  · exact WuPaper.ClassicalFourthNat.outerPay_1659
  · exact WuPaper.ClassicalFourthNat.outerPay_1660
  · exact WuPaper.ClassicalFourthNat.outerPay_1661
  · exact WuPaper.ClassicalFourthNat.outerPay_1662
  · exact WuPaper.ClassicalFourthNat.outerPay_1663
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_025
