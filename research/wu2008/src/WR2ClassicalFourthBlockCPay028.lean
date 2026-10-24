import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay028
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_028 (j : Fin 64) (hj : 64*28+j.val < 2540) :
    CPay (64*28+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_1792
  · exact WuPaper.ClassicalFourthNat.CPay_1793
  · exact WuPaper.ClassicalFourthNat.CPay_1794
  · exact WuPaper.ClassicalFourthNat.CPay_1795
  · exact WuPaper.ClassicalFourthNat.CPay_1796
  · exact WuPaper.ClassicalFourthNat.CPay_1797
  · exact WuPaper.ClassicalFourthNat.CPay_1798
  · exact WuPaper.ClassicalFourthNat.CPay_1799
  · exact WuPaper.ClassicalFourthNat.CPay_1800
  · exact WuPaper.ClassicalFourthNat.CPay_1801
  · exact WuPaper.ClassicalFourthNat.CPay_1802
  · exact WuPaper.ClassicalFourthNat.CPay_1803
  · exact WuPaper.ClassicalFourthNat.CPay_1804
  · exact WuPaper.ClassicalFourthNat.CPay_1805
  · exact WuPaper.ClassicalFourthNat.CPay_1806
  · exact WuPaper.ClassicalFourthNat.CPay_1807
  · exact WuPaper.ClassicalFourthNat.CPay_1808
  · exact WuPaper.ClassicalFourthNat.CPay_1809
  · exact WuPaper.ClassicalFourthNat.CPay_1810
  · exact WuPaper.ClassicalFourthNat.CPay_1811
  · exact WuPaper.ClassicalFourthNat.CPay_1812
  · exact WuPaper.ClassicalFourthNat.CPay_1813
  · exact WuPaper.ClassicalFourthNat.CPay_1814
  · exact WuPaper.ClassicalFourthNat.CPay_1815
  · exact WuPaper.ClassicalFourthNat.CPay_1816
  · exact WuPaper.ClassicalFourthNat.CPay_1817
  · exact WuPaper.ClassicalFourthNat.CPay_1818
  · exact WuPaper.ClassicalFourthNat.CPay_1819
  · exact WuPaper.ClassicalFourthNat.CPay_1820
  · exact WuPaper.ClassicalFourthNat.CPay_1821
  · exact WuPaper.ClassicalFourthNat.CPay_1822
  · exact WuPaper.ClassicalFourthNat.CPay_1823
  · exact WuPaper.ClassicalFourthNat.CPay_1824
  · exact WuPaper.ClassicalFourthNat.CPay_1825
  · exact WuPaper.ClassicalFourthNat.CPay_1826
  · exact WuPaper.ClassicalFourthNat.CPay_1827
  · exact WuPaper.ClassicalFourthNat.CPay_1828
  · exact WuPaper.ClassicalFourthNat.CPay_1829
  · exact WuPaper.ClassicalFourthNat.CPay_1830
  · exact WuPaper.ClassicalFourthNat.CPay_1831
  · exact WuPaper.ClassicalFourthNat.CPay_1832
  · exact WuPaper.ClassicalFourthNat.CPay_1833
  · exact WuPaper.ClassicalFourthNat.CPay_1834
  · exact WuPaper.ClassicalFourthNat.CPay_1835
  · exact WuPaper.ClassicalFourthNat.CPay_1836
  · exact WuPaper.ClassicalFourthNat.CPay_1837
  · exact WuPaper.ClassicalFourthNat.CPay_1838
  · exact WuPaper.ClassicalFourthNat.CPay_1839
  · exact WuPaper.ClassicalFourthNat.CPay_1840
  · exact WuPaper.ClassicalFourthNat.CPay_1841
  · exact WuPaper.ClassicalFourthNat.CPay_1842
  · exact WuPaper.ClassicalFourthNat.CPay_1843
  · exact WuPaper.ClassicalFourthNat.CPay_1844
  · exact WuPaper.ClassicalFourthNat.CPay_1845
  · exact WuPaper.ClassicalFourthNat.CPay_1846
  · exact WuPaper.ClassicalFourthNat.CPay_1847
  · exact WuPaper.ClassicalFourthNat.CPay_1848
  · exact WuPaper.ClassicalFourthNat.CPay_1849
  · exact WuPaper.ClassicalFourthNat.CPay_1850
  · exact WuPaper.ClassicalFourthNat.CPay_1851
  · exact WuPaper.ClassicalFourthNat.CPay_1852
  · exact WuPaper.ClassicalFourthNat.CPay_1853
  · exact WuPaper.ClassicalFourthNat.CPay_1854
  · exact WuPaper.ClassicalFourthNat.CPay_1855
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_028
