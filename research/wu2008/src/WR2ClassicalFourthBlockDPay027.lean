import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay027
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_027 (j : Fin 64) (hj : 64*27+j.val < 2540) :
    DPay (64*27+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_1728
  · exact WuPaper.ClassicalFourthNat.DPay_1729
  · exact WuPaper.ClassicalFourthNat.DPay_1730
  · exact WuPaper.ClassicalFourthNat.DPay_1731
  · exact WuPaper.ClassicalFourthNat.DPay_1732
  · exact WuPaper.ClassicalFourthNat.DPay_1733
  · exact WuPaper.ClassicalFourthNat.DPay_1734
  · exact WuPaper.ClassicalFourthNat.DPay_1735
  · exact WuPaper.ClassicalFourthNat.DPay_1736
  · exact WuPaper.ClassicalFourthNat.DPay_1737
  · exact WuPaper.ClassicalFourthNat.DPay_1738
  · exact WuPaper.ClassicalFourthNat.DPay_1739
  · exact WuPaper.ClassicalFourthNat.DPay_1740
  · exact WuPaper.ClassicalFourthNat.DPay_1741
  · exact WuPaper.ClassicalFourthNat.DPay_1742
  · exact WuPaper.ClassicalFourthNat.DPay_1743
  · exact WuPaper.ClassicalFourthNat.DPay_1744
  · exact WuPaper.ClassicalFourthNat.DPay_1745
  · exact WuPaper.ClassicalFourthNat.DPay_1746
  · exact WuPaper.ClassicalFourthNat.DPay_1747
  · exact WuPaper.ClassicalFourthNat.DPay_1748
  · exact WuPaper.ClassicalFourthNat.DPay_1749
  · exact WuPaper.ClassicalFourthNat.DPay_1750
  · exact WuPaper.ClassicalFourthNat.DPay_1751
  · exact WuPaper.ClassicalFourthNat.DPay_1752
  · exact WuPaper.ClassicalFourthNat.DPay_1753
  · exact WuPaper.ClassicalFourthNat.DPay_1754
  · exact WuPaper.ClassicalFourthNat.DPay_1755
  · exact WuPaper.ClassicalFourthNat.DPay_1756
  · exact WuPaper.ClassicalFourthNat.DPay_1757
  · exact WuPaper.ClassicalFourthNat.DPay_1758
  · exact WuPaper.ClassicalFourthNat.DPay_1759
  · exact WuPaper.ClassicalFourthNat.DPay_1760
  · exact WuPaper.ClassicalFourthNat.DPay_1761
  · exact WuPaper.ClassicalFourthNat.DPay_1762
  · exact WuPaper.ClassicalFourthNat.DPay_1763
  · exact WuPaper.ClassicalFourthNat.DPay_1764
  · exact WuPaper.ClassicalFourthNat.DPay_1765
  · exact WuPaper.ClassicalFourthNat.DPay_1766
  · exact WuPaper.ClassicalFourthNat.DPay_1767
  · exact WuPaper.ClassicalFourthNat.DPay_1768
  · exact WuPaper.ClassicalFourthNat.DPay_1769
  · exact WuPaper.ClassicalFourthNat.DPay_1770
  · exact WuPaper.ClassicalFourthNat.DPay_1771
  · exact WuPaper.ClassicalFourthNat.DPay_1772
  · exact WuPaper.ClassicalFourthNat.DPay_1773
  · exact WuPaper.ClassicalFourthNat.DPay_1774
  · exact WuPaper.ClassicalFourthNat.DPay_1775
  · exact WuPaper.ClassicalFourthNat.DPay_1776
  · exact WuPaper.ClassicalFourthNat.DPay_1777
  · exact WuPaper.ClassicalFourthNat.DPay_1778
  · exact WuPaper.ClassicalFourthNat.DPay_1779
  · exact WuPaper.ClassicalFourthNat.DPay_1780
  · exact WuPaper.ClassicalFourthNat.DPay_1781
  · exact WuPaper.ClassicalFourthNat.DPay_1782
  · exact WuPaper.ClassicalFourthNat.DPay_1783
  · exact WuPaper.ClassicalFourthNat.DPay_1784
  · exact WuPaper.ClassicalFourthNat.DPay_1785
  · exact WuPaper.ClassicalFourthNat.DPay_1786
  · exact WuPaper.ClassicalFourthNat.DPay_1787
  · exact WuPaper.ClassicalFourthNat.DPay_1788
  · exact WuPaper.ClassicalFourthNat.DPay_1789
  · exact WuPaper.ClassicalFourthNat.DPay_1790
  · exact WuPaper.ClassicalFourthNat.DPay_1791
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_027
