import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay025
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_025 (j : Fin 64) (hj : 64*25+j.val < 2540) :
    CPay (64*25+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_1600
  · exact WuPaper.ClassicalFourthNat.CPay_1601
  · exact WuPaper.ClassicalFourthNat.CPay_1602
  · exact WuPaper.ClassicalFourthNat.CPay_1603
  · exact WuPaper.ClassicalFourthNat.CPay_1604
  · exact WuPaper.ClassicalFourthNat.CPay_1605
  · exact WuPaper.ClassicalFourthNat.CPay_1606
  · exact WuPaper.ClassicalFourthNat.CPay_1607
  · exact WuPaper.ClassicalFourthNat.CPay_1608
  · exact WuPaper.ClassicalFourthNat.CPay_1609
  · exact WuPaper.ClassicalFourthNat.CPay_1610
  · exact WuPaper.ClassicalFourthNat.CPay_1611
  · exact WuPaper.ClassicalFourthNat.CPay_1612
  · exact WuPaper.ClassicalFourthNat.CPay_1613
  · exact WuPaper.ClassicalFourthNat.CPay_1614
  · exact WuPaper.ClassicalFourthNat.CPay_1615
  · exact WuPaper.ClassicalFourthNat.CPay_1616
  · exact WuPaper.ClassicalFourthNat.CPay_1617
  · exact WuPaper.ClassicalFourthNat.CPay_1618
  · exact WuPaper.ClassicalFourthNat.CPay_1619
  · exact WuPaper.ClassicalFourthNat.CPay_1620
  · exact WuPaper.ClassicalFourthNat.CPay_1621
  · exact WuPaper.ClassicalFourthNat.CPay_1622
  · exact WuPaper.ClassicalFourthNat.CPay_1623
  · exact WuPaper.ClassicalFourthNat.CPay_1624
  · exact WuPaper.ClassicalFourthNat.CPay_1625
  · exact WuPaper.ClassicalFourthNat.CPay_1626
  · exact WuPaper.ClassicalFourthNat.CPay_1627
  · exact WuPaper.ClassicalFourthNat.CPay_1628
  · exact WuPaper.ClassicalFourthNat.CPay_1629
  · exact WuPaper.ClassicalFourthNat.CPay_1630
  · exact WuPaper.ClassicalFourthNat.CPay_1631
  · exact WuPaper.ClassicalFourthNat.CPay_1632
  · exact WuPaper.ClassicalFourthNat.CPay_1633
  · exact WuPaper.ClassicalFourthNat.CPay_1634
  · exact WuPaper.ClassicalFourthNat.CPay_1635
  · exact WuPaper.ClassicalFourthNat.CPay_1636
  · exact WuPaper.ClassicalFourthNat.CPay_1637
  · exact WuPaper.ClassicalFourthNat.CPay_1638
  · exact WuPaper.ClassicalFourthNat.CPay_1639
  · exact WuPaper.ClassicalFourthNat.CPay_1640
  · exact WuPaper.ClassicalFourthNat.CPay_1641
  · exact WuPaper.ClassicalFourthNat.CPay_1642
  · exact WuPaper.ClassicalFourthNat.CPay_1643
  · exact WuPaper.ClassicalFourthNat.CPay_1644
  · exact WuPaper.ClassicalFourthNat.CPay_1645
  · exact WuPaper.ClassicalFourthNat.CPay_1646
  · exact WuPaper.ClassicalFourthNat.CPay_1647
  · exact WuPaper.ClassicalFourthNat.CPay_1648
  · exact WuPaper.ClassicalFourthNat.CPay_1649
  · exact WuPaper.ClassicalFourthNat.CPay_1650
  · exact WuPaper.ClassicalFourthNat.CPay_1651
  · exact WuPaper.ClassicalFourthNat.CPay_1652
  · exact WuPaper.ClassicalFourthNat.CPay_1653
  · exact WuPaper.ClassicalFourthNat.CPay_1654
  · exact WuPaper.ClassicalFourthNat.CPay_1655
  · exact WuPaper.ClassicalFourthNat.CPay_1656
  · exact WuPaper.ClassicalFourthNat.CPay_1657
  · exact WuPaper.ClassicalFourthNat.CPay_1658
  · exact WuPaper.ClassicalFourthNat.CPay_1659
  · exact WuPaper.ClassicalFourthNat.CPay_1660
  · exact WuPaper.ClassicalFourthNat.CPay_1661
  · exact WuPaper.ClassicalFourthNat.CPay_1662
  · exact WuPaper.ClassicalFourthNat.CPay_1663
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_025
