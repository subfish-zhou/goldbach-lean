import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay026
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_026 (j : Fin 64) (hj : 64*26+j.val < 2540) :
    DPay (64*26+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_1664
  · exact WuPaper.ClassicalFourthNat.DPay_1665
  · exact WuPaper.ClassicalFourthNat.DPay_1666
  · exact WuPaper.ClassicalFourthNat.DPay_1667
  · exact WuPaper.ClassicalFourthNat.DPay_1668
  · exact WuPaper.ClassicalFourthNat.DPay_1669
  · exact WuPaper.ClassicalFourthNat.DPay_1670
  · exact WuPaper.ClassicalFourthNat.DPay_1671
  · exact WuPaper.ClassicalFourthNat.DPay_1672
  · exact WuPaper.ClassicalFourthNat.DPay_1673
  · exact WuPaper.ClassicalFourthNat.DPay_1674
  · exact WuPaper.ClassicalFourthNat.DPay_1675
  · exact WuPaper.ClassicalFourthNat.DPay_1676
  · exact WuPaper.ClassicalFourthNat.DPay_1677
  · exact WuPaper.ClassicalFourthNat.DPay_1678
  · exact WuPaper.ClassicalFourthNat.DPay_1679
  · exact WuPaper.ClassicalFourthNat.DPay_1680
  · exact WuPaper.ClassicalFourthNat.DPay_1681
  · exact WuPaper.ClassicalFourthNat.DPay_1682
  · exact WuPaper.ClassicalFourthNat.DPay_1683
  · exact WuPaper.ClassicalFourthNat.DPay_1684
  · exact WuPaper.ClassicalFourthNat.DPay_1685
  · exact WuPaper.ClassicalFourthNat.DPay_1686
  · exact WuPaper.ClassicalFourthNat.DPay_1687
  · exact WuPaper.ClassicalFourthNat.DPay_1688
  · exact WuPaper.ClassicalFourthNat.DPay_1689
  · exact WuPaper.ClassicalFourthNat.DPay_1690
  · exact WuPaper.ClassicalFourthNat.DPay_1691
  · exact WuPaper.ClassicalFourthNat.DPay_1692
  · exact WuPaper.ClassicalFourthNat.DPay_1693
  · exact WuPaper.ClassicalFourthNat.DPay_1694
  · exact WuPaper.ClassicalFourthNat.DPay_1695
  · exact WuPaper.ClassicalFourthNat.DPay_1696
  · exact WuPaper.ClassicalFourthNat.DPay_1697
  · exact WuPaper.ClassicalFourthNat.DPay_1698
  · exact WuPaper.ClassicalFourthNat.DPay_1699
  · exact WuPaper.ClassicalFourthNat.DPay_1700
  · exact WuPaper.ClassicalFourthNat.DPay_1701
  · exact WuPaper.ClassicalFourthNat.DPay_1702
  · exact WuPaper.ClassicalFourthNat.DPay_1703
  · exact WuPaper.ClassicalFourthNat.DPay_1704
  · exact WuPaper.ClassicalFourthNat.DPay_1705
  · exact WuPaper.ClassicalFourthNat.DPay_1706
  · exact WuPaper.ClassicalFourthNat.DPay_1707
  · exact WuPaper.ClassicalFourthNat.DPay_1708
  · exact WuPaper.ClassicalFourthNat.DPay_1709
  · exact WuPaper.ClassicalFourthNat.DPay_1710
  · exact WuPaper.ClassicalFourthNat.DPay_1711
  · exact WuPaper.ClassicalFourthNat.DPay_1712
  · exact WuPaper.ClassicalFourthNat.DPay_1713
  · exact WuPaper.ClassicalFourthNat.DPay_1714
  · exact WuPaper.ClassicalFourthNat.DPay_1715
  · exact WuPaper.ClassicalFourthNat.DPay_1716
  · exact WuPaper.ClassicalFourthNat.DPay_1717
  · exact WuPaper.ClassicalFourthNat.DPay_1718
  · exact WuPaper.ClassicalFourthNat.DPay_1719
  · exact WuPaper.ClassicalFourthNat.DPay_1720
  · exact WuPaper.ClassicalFourthNat.DPay_1721
  · exact WuPaper.ClassicalFourthNat.DPay_1722
  · exact WuPaper.ClassicalFourthNat.DPay_1723
  · exact WuPaper.ClassicalFourthNat.DPay_1724
  · exact WuPaper.ClassicalFourthNat.DPay_1725
  · exact WuPaper.ClassicalFourthNat.DPay_1726
  · exact WuPaper.ClassicalFourthNat.DPay_1727
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_026
