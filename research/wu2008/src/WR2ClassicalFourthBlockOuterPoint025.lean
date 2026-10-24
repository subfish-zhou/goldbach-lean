import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint025
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_025 (j : Fin 64) (hj : 64*25+j.val < 10541) :
    OuterPoint (64*25+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1600
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1601
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1602
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1603
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1604
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1605
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1606
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1607
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1608
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1609
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1610
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1611
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1612
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1613
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1614
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1615
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1616
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1617
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1618
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1619
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1620
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1621
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1622
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1623
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1624
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1625
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1626
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1627
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1628
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1629
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1630
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1631
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1632
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1633
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1634
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1635
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1636
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1637
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1638
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1639
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1640
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1641
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1642
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1643
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1644
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1645
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1646
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1647
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1648
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1649
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1650
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1651
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1652
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1653
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1654
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1655
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1656
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1657
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1658
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1659
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1660
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1661
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1662
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1663
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_025
