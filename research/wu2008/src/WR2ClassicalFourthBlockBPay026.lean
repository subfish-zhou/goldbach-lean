import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay026
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_026 (j : Fin 64) (hj : 64*26+j.val < 10540) :
    BPay (64*26+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_1664
  · exact WuPaper.ClassicalFourthNat.BPay_1665
  · exact WuPaper.ClassicalFourthNat.BPay_1666
  · exact WuPaper.ClassicalFourthNat.BPay_1667
  · exact WuPaper.ClassicalFourthNat.BPay_1668
  · exact WuPaper.ClassicalFourthNat.BPay_1669
  · exact WuPaper.ClassicalFourthNat.BPay_1670
  · exact WuPaper.ClassicalFourthNat.BPay_1671
  · exact WuPaper.ClassicalFourthNat.BPay_1672
  · exact WuPaper.ClassicalFourthNat.BPay_1673
  · exact WuPaper.ClassicalFourthNat.BPay_1674
  · exact WuPaper.ClassicalFourthNat.BPay_1675
  · exact WuPaper.ClassicalFourthNat.BPay_1676
  · exact WuPaper.ClassicalFourthNat.BPay_1677
  · exact WuPaper.ClassicalFourthNat.BPay_1678
  · exact WuPaper.ClassicalFourthNat.BPay_1679
  · exact WuPaper.ClassicalFourthNat.BPay_1680
  · exact WuPaper.ClassicalFourthNat.BPay_1681
  · exact WuPaper.ClassicalFourthNat.BPay_1682
  · exact WuPaper.ClassicalFourthNat.BPay_1683
  · exact WuPaper.ClassicalFourthNat.BPay_1684
  · exact WuPaper.ClassicalFourthNat.BPay_1685
  · exact WuPaper.ClassicalFourthNat.BPay_1686
  · exact WuPaper.ClassicalFourthNat.BPay_1687
  · exact WuPaper.ClassicalFourthNat.BPay_1688
  · exact WuPaper.ClassicalFourthNat.BPay_1689
  · exact WuPaper.ClassicalFourthNat.BPay_1690
  · exact WuPaper.ClassicalFourthNat.BPay_1691
  · exact WuPaper.ClassicalFourthNat.BPay_1692
  · exact WuPaper.ClassicalFourthNat.BPay_1693
  · exact WuPaper.ClassicalFourthNat.BPay_1694
  · exact WuPaper.ClassicalFourthNat.BPay_1695
  · exact WuPaper.ClassicalFourthNat.BPay_1696
  · exact WuPaper.ClassicalFourthNat.BPay_1697
  · exact WuPaper.ClassicalFourthNat.BPay_1698
  · exact WuPaper.ClassicalFourthNat.BPay_1699
  · exact WuPaper.ClassicalFourthNat.BPay_1700
  · exact WuPaper.ClassicalFourthNat.BPay_1701
  · exact WuPaper.ClassicalFourthNat.BPay_1702
  · exact WuPaper.ClassicalFourthNat.BPay_1703
  · exact WuPaper.ClassicalFourthNat.BPay_1704
  · exact WuPaper.ClassicalFourthNat.BPay_1705
  · exact WuPaper.ClassicalFourthNat.BPay_1706
  · exact WuPaper.ClassicalFourthNat.BPay_1707
  · exact WuPaper.ClassicalFourthNat.BPay_1708
  · exact WuPaper.ClassicalFourthNat.BPay_1709
  · exact WuPaper.ClassicalFourthNat.BPay_1710
  · exact WuPaper.ClassicalFourthNat.BPay_1711
  · exact WuPaper.ClassicalFourthNat.BPay_1712
  · exact WuPaper.ClassicalFourthNat.BPay_1713
  · exact WuPaper.ClassicalFourthNat.BPay_1714
  · exact WuPaper.ClassicalFourthNat.BPay_1715
  · exact WuPaper.ClassicalFourthNat.BPay_1716
  · exact WuPaper.ClassicalFourthNat.BPay_1717
  · exact WuPaper.ClassicalFourthNat.BPay_1718
  · exact WuPaper.ClassicalFourthNat.BPay_1719
  · exact WuPaper.ClassicalFourthNat.BPay_1720
  · exact WuPaper.ClassicalFourthNat.BPay_1721
  · exact WuPaper.ClassicalFourthNat.BPay_1722
  · exact WuPaper.ClassicalFourthNat.BPay_1723
  · exact WuPaper.ClassicalFourthNat.BPay_1724
  · exact WuPaper.ClassicalFourthNat.BPay_1725
  · exact WuPaper.ClassicalFourthNat.BPay_1726
  · exact WuPaper.ClassicalFourthNat.BPay_1727
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_026
