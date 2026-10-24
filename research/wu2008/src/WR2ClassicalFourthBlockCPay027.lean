import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay027
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_027 (j : Fin 64) (hj : 64*27+j.val < 2540) :
    CPay (64*27+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_1728
  · exact WuPaper.ClassicalFourthNat.CPay_1729
  · exact WuPaper.ClassicalFourthNat.CPay_1730
  · exact WuPaper.ClassicalFourthNat.CPay_1731
  · exact WuPaper.ClassicalFourthNat.CPay_1732
  · exact WuPaper.ClassicalFourthNat.CPay_1733
  · exact WuPaper.ClassicalFourthNat.CPay_1734
  · exact WuPaper.ClassicalFourthNat.CPay_1735
  · exact WuPaper.ClassicalFourthNat.CPay_1736
  · exact WuPaper.ClassicalFourthNat.CPay_1737
  · exact WuPaper.ClassicalFourthNat.CPay_1738
  · exact WuPaper.ClassicalFourthNat.CPay_1739
  · exact WuPaper.ClassicalFourthNat.CPay_1740
  · exact WuPaper.ClassicalFourthNat.CPay_1741
  · exact WuPaper.ClassicalFourthNat.CPay_1742
  · exact WuPaper.ClassicalFourthNat.CPay_1743
  · exact WuPaper.ClassicalFourthNat.CPay_1744
  · exact WuPaper.ClassicalFourthNat.CPay_1745
  · exact WuPaper.ClassicalFourthNat.CPay_1746
  · exact WuPaper.ClassicalFourthNat.CPay_1747
  · exact WuPaper.ClassicalFourthNat.CPay_1748
  · exact WuPaper.ClassicalFourthNat.CPay_1749
  · exact WuPaper.ClassicalFourthNat.CPay_1750
  · exact WuPaper.ClassicalFourthNat.CPay_1751
  · exact WuPaper.ClassicalFourthNat.CPay_1752
  · exact WuPaper.ClassicalFourthNat.CPay_1753
  · exact WuPaper.ClassicalFourthNat.CPay_1754
  · exact WuPaper.ClassicalFourthNat.CPay_1755
  · exact WuPaper.ClassicalFourthNat.CPay_1756
  · exact WuPaper.ClassicalFourthNat.CPay_1757
  · exact WuPaper.ClassicalFourthNat.CPay_1758
  · exact WuPaper.ClassicalFourthNat.CPay_1759
  · exact WuPaper.ClassicalFourthNat.CPay_1760
  · exact WuPaper.ClassicalFourthNat.CPay_1761
  · exact WuPaper.ClassicalFourthNat.CPay_1762
  · exact WuPaper.ClassicalFourthNat.CPay_1763
  · exact WuPaper.ClassicalFourthNat.CPay_1764
  · exact WuPaper.ClassicalFourthNat.CPay_1765
  · exact WuPaper.ClassicalFourthNat.CPay_1766
  · exact WuPaper.ClassicalFourthNat.CPay_1767
  · exact WuPaper.ClassicalFourthNat.CPay_1768
  · exact WuPaper.ClassicalFourthNat.CPay_1769
  · exact WuPaper.ClassicalFourthNat.CPay_1770
  · exact WuPaper.ClassicalFourthNat.CPay_1771
  · exact WuPaper.ClassicalFourthNat.CPay_1772
  · exact WuPaper.ClassicalFourthNat.CPay_1773
  · exact WuPaper.ClassicalFourthNat.CPay_1774
  · exact WuPaper.ClassicalFourthNat.CPay_1775
  · exact WuPaper.ClassicalFourthNat.CPay_1776
  · exact WuPaper.ClassicalFourthNat.CPay_1777
  · exact WuPaper.ClassicalFourthNat.CPay_1778
  · exact WuPaper.ClassicalFourthNat.CPay_1779
  · exact WuPaper.ClassicalFourthNat.CPay_1780
  · exact WuPaper.ClassicalFourthNat.CPay_1781
  · exact WuPaper.ClassicalFourthNat.CPay_1782
  · exact WuPaper.ClassicalFourthNat.CPay_1783
  · exact WuPaper.ClassicalFourthNat.CPay_1784
  · exact WuPaper.ClassicalFourthNat.CPay_1785
  · exact WuPaper.ClassicalFourthNat.CPay_1786
  · exact WuPaper.ClassicalFourthNat.CPay_1787
  · exact WuPaper.ClassicalFourthNat.CPay_1788
  · exact WuPaper.ClassicalFourthNat.CPay_1789
  · exact WuPaper.ClassicalFourthNat.CPay_1790
  · exact WuPaper.ClassicalFourthNat.CPay_1791
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_027
