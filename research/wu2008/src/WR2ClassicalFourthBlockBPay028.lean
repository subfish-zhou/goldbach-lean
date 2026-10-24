import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay028
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_028 (j : Fin 64) (hj : 64*28+j.val < 10540) :
    BPay (64*28+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_1792
  · exact WuPaper.ClassicalFourthNat.BPay_1793
  · exact WuPaper.ClassicalFourthNat.BPay_1794
  · exact WuPaper.ClassicalFourthNat.BPay_1795
  · exact WuPaper.ClassicalFourthNat.BPay_1796
  · exact WuPaper.ClassicalFourthNat.BPay_1797
  · exact WuPaper.ClassicalFourthNat.BPay_1798
  · exact WuPaper.ClassicalFourthNat.BPay_1799
  · exact WuPaper.ClassicalFourthNat.BPay_1800
  · exact WuPaper.ClassicalFourthNat.BPay_1801
  · exact WuPaper.ClassicalFourthNat.BPay_1802
  · exact WuPaper.ClassicalFourthNat.BPay_1803
  · exact WuPaper.ClassicalFourthNat.BPay_1804
  · exact WuPaper.ClassicalFourthNat.BPay_1805
  · exact WuPaper.ClassicalFourthNat.BPay_1806
  · exact WuPaper.ClassicalFourthNat.BPay_1807
  · exact WuPaper.ClassicalFourthNat.BPay_1808
  · exact WuPaper.ClassicalFourthNat.BPay_1809
  · exact WuPaper.ClassicalFourthNat.BPay_1810
  · exact WuPaper.ClassicalFourthNat.BPay_1811
  · exact WuPaper.ClassicalFourthNat.BPay_1812
  · exact WuPaper.ClassicalFourthNat.BPay_1813
  · exact WuPaper.ClassicalFourthNat.BPay_1814
  · exact WuPaper.ClassicalFourthNat.BPay_1815
  · exact WuPaper.ClassicalFourthNat.BPay_1816
  · exact WuPaper.ClassicalFourthNat.BPay_1817
  · exact WuPaper.ClassicalFourthNat.BPay_1818
  · exact WuPaper.ClassicalFourthNat.BPay_1819
  · exact WuPaper.ClassicalFourthNat.BPay_1820
  · exact WuPaper.ClassicalFourthNat.BPay_1821
  · exact WuPaper.ClassicalFourthNat.BPay_1822
  · exact WuPaper.ClassicalFourthNat.BPay_1823
  · exact WuPaper.ClassicalFourthNat.BPay_1824
  · exact WuPaper.ClassicalFourthNat.BPay_1825
  · exact WuPaper.ClassicalFourthNat.BPay_1826
  · exact WuPaper.ClassicalFourthNat.BPay_1827
  · exact WuPaper.ClassicalFourthNat.BPay_1828
  · exact WuPaper.ClassicalFourthNat.BPay_1829
  · exact WuPaper.ClassicalFourthNat.BPay_1830
  · exact WuPaper.ClassicalFourthNat.BPay_1831
  · exact WuPaper.ClassicalFourthNat.BPay_1832
  · exact WuPaper.ClassicalFourthNat.BPay_1833
  · exact WuPaper.ClassicalFourthNat.BPay_1834
  · exact WuPaper.ClassicalFourthNat.BPay_1835
  · exact WuPaper.ClassicalFourthNat.BPay_1836
  · exact WuPaper.ClassicalFourthNat.BPay_1837
  · exact WuPaper.ClassicalFourthNat.BPay_1838
  · exact WuPaper.ClassicalFourthNat.BPay_1839
  · exact WuPaper.ClassicalFourthNat.BPay_1840
  · exact WuPaper.ClassicalFourthNat.BPay_1841
  · exact WuPaper.ClassicalFourthNat.BPay_1842
  · exact WuPaper.ClassicalFourthNat.BPay_1843
  · exact WuPaper.ClassicalFourthNat.BPay_1844
  · exact WuPaper.ClassicalFourthNat.BPay_1845
  · exact WuPaper.ClassicalFourthNat.BPay_1846
  · exact WuPaper.ClassicalFourthNat.BPay_1847
  · exact WuPaper.ClassicalFourthNat.BPay_1848
  · exact WuPaper.ClassicalFourthNat.BPay_1849
  · exact WuPaper.ClassicalFourthNat.BPay_1850
  · exact WuPaper.ClassicalFourthNat.BPay_1851
  · exact WuPaper.ClassicalFourthNat.BPay_1852
  · exact WuPaper.ClassicalFourthNat.BPay_1853
  · exact WuPaper.ClassicalFourthNat.BPay_1854
  · exact WuPaper.ClassicalFourthNat.BPay_1855
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_028
