import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay026
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_026 (j : Fin 64) (hj : 64*26+j.val < 2540) :
    CPay (64*26+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_1664
  · exact WuPaper.ClassicalFourthNat.CPay_1665
  · exact WuPaper.ClassicalFourthNat.CPay_1666
  · exact WuPaper.ClassicalFourthNat.CPay_1667
  · exact WuPaper.ClassicalFourthNat.CPay_1668
  · exact WuPaper.ClassicalFourthNat.CPay_1669
  · exact WuPaper.ClassicalFourthNat.CPay_1670
  · exact WuPaper.ClassicalFourthNat.CPay_1671
  · exact WuPaper.ClassicalFourthNat.CPay_1672
  · exact WuPaper.ClassicalFourthNat.CPay_1673
  · exact WuPaper.ClassicalFourthNat.CPay_1674
  · exact WuPaper.ClassicalFourthNat.CPay_1675
  · exact WuPaper.ClassicalFourthNat.CPay_1676
  · exact WuPaper.ClassicalFourthNat.CPay_1677
  · exact WuPaper.ClassicalFourthNat.CPay_1678
  · exact WuPaper.ClassicalFourthNat.CPay_1679
  · exact WuPaper.ClassicalFourthNat.CPay_1680
  · exact WuPaper.ClassicalFourthNat.CPay_1681
  · exact WuPaper.ClassicalFourthNat.CPay_1682
  · exact WuPaper.ClassicalFourthNat.CPay_1683
  · exact WuPaper.ClassicalFourthNat.CPay_1684
  · exact WuPaper.ClassicalFourthNat.CPay_1685
  · exact WuPaper.ClassicalFourthNat.CPay_1686
  · exact WuPaper.ClassicalFourthNat.CPay_1687
  · exact WuPaper.ClassicalFourthNat.CPay_1688
  · exact WuPaper.ClassicalFourthNat.CPay_1689
  · exact WuPaper.ClassicalFourthNat.CPay_1690
  · exact WuPaper.ClassicalFourthNat.CPay_1691
  · exact WuPaper.ClassicalFourthNat.CPay_1692
  · exact WuPaper.ClassicalFourthNat.CPay_1693
  · exact WuPaper.ClassicalFourthNat.CPay_1694
  · exact WuPaper.ClassicalFourthNat.CPay_1695
  · exact WuPaper.ClassicalFourthNat.CPay_1696
  · exact WuPaper.ClassicalFourthNat.CPay_1697
  · exact WuPaper.ClassicalFourthNat.CPay_1698
  · exact WuPaper.ClassicalFourthNat.CPay_1699
  · exact WuPaper.ClassicalFourthNat.CPay_1700
  · exact WuPaper.ClassicalFourthNat.CPay_1701
  · exact WuPaper.ClassicalFourthNat.CPay_1702
  · exact WuPaper.ClassicalFourthNat.CPay_1703
  · exact WuPaper.ClassicalFourthNat.CPay_1704
  · exact WuPaper.ClassicalFourthNat.CPay_1705
  · exact WuPaper.ClassicalFourthNat.CPay_1706
  · exact WuPaper.ClassicalFourthNat.CPay_1707
  · exact WuPaper.ClassicalFourthNat.CPay_1708
  · exact WuPaper.ClassicalFourthNat.CPay_1709
  · exact WuPaper.ClassicalFourthNat.CPay_1710
  · exact WuPaper.ClassicalFourthNat.CPay_1711
  · exact WuPaper.ClassicalFourthNat.CPay_1712
  · exact WuPaper.ClassicalFourthNat.CPay_1713
  · exact WuPaper.ClassicalFourthNat.CPay_1714
  · exact WuPaper.ClassicalFourthNat.CPay_1715
  · exact WuPaper.ClassicalFourthNat.CPay_1716
  · exact WuPaper.ClassicalFourthNat.CPay_1717
  · exact WuPaper.ClassicalFourthNat.CPay_1718
  · exact WuPaper.ClassicalFourthNat.CPay_1719
  · exact WuPaper.ClassicalFourthNat.CPay_1720
  · exact WuPaper.ClassicalFourthNat.CPay_1721
  · exact WuPaper.ClassicalFourthNat.CPay_1722
  · exact WuPaper.ClassicalFourthNat.CPay_1723
  · exact WuPaper.ClassicalFourthNat.CPay_1724
  · exact WuPaper.ClassicalFourthNat.CPay_1725
  · exact WuPaper.ClassicalFourthNat.CPay_1726
  · exact WuPaper.ClassicalFourthNat.CPay_1727
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_026
