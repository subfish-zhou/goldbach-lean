import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay028
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_028 (j : Fin 64) (hj : 64*28+j.val < 2540) :
    DPay (64*28+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_1792
  · exact WuPaper.ClassicalFourthNat.DPay_1793
  · exact WuPaper.ClassicalFourthNat.DPay_1794
  · exact WuPaper.ClassicalFourthNat.DPay_1795
  · exact WuPaper.ClassicalFourthNat.DPay_1796
  · exact WuPaper.ClassicalFourthNat.DPay_1797
  · exact WuPaper.ClassicalFourthNat.DPay_1798
  · exact WuPaper.ClassicalFourthNat.DPay_1799
  · exact WuPaper.ClassicalFourthNat.DPay_1800
  · exact WuPaper.ClassicalFourthNat.DPay_1801
  · exact WuPaper.ClassicalFourthNat.DPay_1802
  · exact WuPaper.ClassicalFourthNat.DPay_1803
  · exact WuPaper.ClassicalFourthNat.DPay_1804
  · exact WuPaper.ClassicalFourthNat.DPay_1805
  · exact WuPaper.ClassicalFourthNat.DPay_1806
  · exact WuPaper.ClassicalFourthNat.DPay_1807
  · exact WuPaper.ClassicalFourthNat.DPay_1808
  · exact WuPaper.ClassicalFourthNat.DPay_1809
  · exact WuPaper.ClassicalFourthNat.DPay_1810
  · exact WuPaper.ClassicalFourthNat.DPay_1811
  · exact WuPaper.ClassicalFourthNat.DPay_1812
  · exact WuPaper.ClassicalFourthNat.DPay_1813
  · exact WuPaper.ClassicalFourthNat.DPay_1814
  · exact WuPaper.ClassicalFourthNat.DPay_1815
  · exact WuPaper.ClassicalFourthNat.DPay_1816
  · exact WuPaper.ClassicalFourthNat.DPay_1817
  · exact WuPaper.ClassicalFourthNat.DPay_1818
  · exact WuPaper.ClassicalFourthNat.DPay_1819
  · exact WuPaper.ClassicalFourthNat.DPay_1820
  · exact WuPaper.ClassicalFourthNat.DPay_1821
  · exact WuPaper.ClassicalFourthNat.DPay_1822
  · exact WuPaper.ClassicalFourthNat.DPay_1823
  · exact WuPaper.ClassicalFourthNat.DPay_1824
  · exact WuPaper.ClassicalFourthNat.DPay_1825
  · exact WuPaper.ClassicalFourthNat.DPay_1826
  · exact WuPaper.ClassicalFourthNat.DPay_1827
  · exact WuPaper.ClassicalFourthNat.DPay_1828
  · exact WuPaper.ClassicalFourthNat.DPay_1829
  · exact WuPaper.ClassicalFourthNat.DPay_1830
  · exact WuPaper.ClassicalFourthNat.DPay_1831
  · exact WuPaper.ClassicalFourthNat.DPay_1832
  · exact WuPaper.ClassicalFourthNat.DPay_1833
  · exact WuPaper.ClassicalFourthNat.DPay_1834
  · exact WuPaper.ClassicalFourthNat.DPay_1835
  · exact WuPaper.ClassicalFourthNat.DPay_1836
  · exact WuPaper.ClassicalFourthNat.DPay_1837
  · exact WuPaper.ClassicalFourthNat.DPay_1838
  · exact WuPaper.ClassicalFourthNat.DPay_1839
  · exact WuPaper.ClassicalFourthNat.DPay_1840
  · exact WuPaper.ClassicalFourthNat.DPay_1841
  · exact WuPaper.ClassicalFourthNat.DPay_1842
  · exact WuPaper.ClassicalFourthNat.DPay_1843
  · exact WuPaper.ClassicalFourthNat.DPay_1844
  · exact WuPaper.ClassicalFourthNat.DPay_1845
  · exact WuPaper.ClassicalFourthNat.DPay_1846
  · exact WuPaper.ClassicalFourthNat.DPay_1847
  · exact WuPaper.ClassicalFourthNat.DPay_1848
  · exact WuPaper.ClassicalFourthNat.DPay_1849
  · exact WuPaper.ClassicalFourthNat.DPay_1850
  · exact WuPaper.ClassicalFourthNat.DPay_1851
  · exact WuPaper.ClassicalFourthNat.DPay_1852
  · exact WuPaper.ClassicalFourthNat.DPay_1853
  · exact WuPaper.ClassicalFourthNat.DPay_1854
  · exact WuPaper.ClassicalFourthNat.DPay_1855
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_028
