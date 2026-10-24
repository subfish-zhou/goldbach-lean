import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay027
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_027 (j : Fin 64) (hj : 64*27+j.val < 10540) :
    BPay (64*27+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_1728
  · exact WuPaper.ClassicalFourthNat.BPay_1729
  · exact WuPaper.ClassicalFourthNat.BPay_1730
  · exact WuPaper.ClassicalFourthNat.BPay_1731
  · exact WuPaper.ClassicalFourthNat.BPay_1732
  · exact WuPaper.ClassicalFourthNat.BPay_1733
  · exact WuPaper.ClassicalFourthNat.BPay_1734
  · exact WuPaper.ClassicalFourthNat.BPay_1735
  · exact WuPaper.ClassicalFourthNat.BPay_1736
  · exact WuPaper.ClassicalFourthNat.BPay_1737
  · exact WuPaper.ClassicalFourthNat.BPay_1738
  · exact WuPaper.ClassicalFourthNat.BPay_1739
  · exact WuPaper.ClassicalFourthNat.BPay_1740
  · exact WuPaper.ClassicalFourthNat.BPay_1741
  · exact WuPaper.ClassicalFourthNat.BPay_1742
  · exact WuPaper.ClassicalFourthNat.BPay_1743
  · exact WuPaper.ClassicalFourthNat.BPay_1744
  · exact WuPaper.ClassicalFourthNat.BPay_1745
  · exact WuPaper.ClassicalFourthNat.BPay_1746
  · exact WuPaper.ClassicalFourthNat.BPay_1747
  · exact WuPaper.ClassicalFourthNat.BPay_1748
  · exact WuPaper.ClassicalFourthNat.BPay_1749
  · exact WuPaper.ClassicalFourthNat.BPay_1750
  · exact WuPaper.ClassicalFourthNat.BPay_1751
  · exact WuPaper.ClassicalFourthNat.BPay_1752
  · exact WuPaper.ClassicalFourthNat.BPay_1753
  · exact WuPaper.ClassicalFourthNat.BPay_1754
  · exact WuPaper.ClassicalFourthNat.BPay_1755
  · exact WuPaper.ClassicalFourthNat.BPay_1756
  · exact WuPaper.ClassicalFourthNat.BPay_1757
  · exact WuPaper.ClassicalFourthNat.BPay_1758
  · exact WuPaper.ClassicalFourthNat.BPay_1759
  · exact WuPaper.ClassicalFourthNat.BPay_1760
  · exact WuPaper.ClassicalFourthNat.BPay_1761
  · exact WuPaper.ClassicalFourthNat.BPay_1762
  · exact WuPaper.ClassicalFourthNat.BPay_1763
  · exact WuPaper.ClassicalFourthNat.BPay_1764
  · exact WuPaper.ClassicalFourthNat.BPay_1765
  · exact WuPaper.ClassicalFourthNat.BPay_1766
  · exact WuPaper.ClassicalFourthNat.BPay_1767
  · exact WuPaper.ClassicalFourthNat.BPay_1768
  · exact WuPaper.ClassicalFourthNat.BPay_1769
  · exact WuPaper.ClassicalFourthNat.BPay_1770
  · exact WuPaper.ClassicalFourthNat.BPay_1771
  · exact WuPaper.ClassicalFourthNat.BPay_1772
  · exact WuPaper.ClassicalFourthNat.BPay_1773
  · exact WuPaper.ClassicalFourthNat.BPay_1774
  · exact WuPaper.ClassicalFourthNat.BPay_1775
  · exact WuPaper.ClassicalFourthNat.BPay_1776
  · exact WuPaper.ClassicalFourthNat.BPay_1777
  · exact WuPaper.ClassicalFourthNat.BPay_1778
  · exact WuPaper.ClassicalFourthNat.BPay_1779
  · exact WuPaper.ClassicalFourthNat.BPay_1780
  · exact WuPaper.ClassicalFourthNat.BPay_1781
  · exact WuPaper.ClassicalFourthNat.BPay_1782
  · exact WuPaper.ClassicalFourthNat.BPay_1783
  · exact WuPaper.ClassicalFourthNat.BPay_1784
  · exact WuPaper.ClassicalFourthNat.BPay_1785
  · exact WuPaper.ClassicalFourthNat.BPay_1786
  · exact WuPaper.ClassicalFourthNat.BPay_1787
  · exact WuPaper.ClassicalFourthNat.BPay_1788
  · exact WuPaper.ClassicalFourthNat.BPay_1789
  · exact WuPaper.ClassicalFourthNat.BPay_1790
  · exact WuPaper.ClassicalFourthNat.BPay_1791
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_027
