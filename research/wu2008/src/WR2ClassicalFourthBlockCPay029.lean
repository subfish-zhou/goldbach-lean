import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay029
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_029 (j : Fin 64) (hj : 64*29+j.val < 2540) :
    CPay (64*29+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_1856
  · exact WuPaper.ClassicalFourthNat.CPay_1857
  · exact WuPaper.ClassicalFourthNat.CPay_1858
  · exact WuPaper.ClassicalFourthNat.CPay_1859
  · exact WuPaper.ClassicalFourthNat.CPay_1860
  · exact WuPaper.ClassicalFourthNat.CPay_1861
  · exact WuPaper.ClassicalFourthNat.CPay_1862
  · exact WuPaper.ClassicalFourthNat.CPay_1863
  · exact WuPaper.ClassicalFourthNat.CPay_1864
  · exact WuPaper.ClassicalFourthNat.CPay_1865
  · exact WuPaper.ClassicalFourthNat.CPay_1866
  · exact WuPaper.ClassicalFourthNat.CPay_1867
  · exact WuPaper.ClassicalFourthNat.CPay_1868
  · exact WuPaper.ClassicalFourthNat.CPay_1869
  · exact WuPaper.ClassicalFourthNat.CPay_1870
  · exact WuPaper.ClassicalFourthNat.CPay_1871
  · exact WuPaper.ClassicalFourthNat.CPay_1872
  · exact WuPaper.ClassicalFourthNat.CPay_1873
  · exact WuPaper.ClassicalFourthNat.CPay_1874
  · exact WuPaper.ClassicalFourthNat.CPay_1875
  · exact WuPaper.ClassicalFourthNat.CPay_1876
  · exact WuPaper.ClassicalFourthNat.CPay_1877
  · exact WuPaper.ClassicalFourthNat.CPay_1878
  · exact WuPaper.ClassicalFourthNat.CPay_1879
  · exact WuPaper.ClassicalFourthNat.CPay_1880
  · exact WuPaper.ClassicalFourthNat.CPay_1881
  · exact WuPaper.ClassicalFourthNat.CPay_1882
  · exact WuPaper.ClassicalFourthNat.CPay_1883
  · exact WuPaper.ClassicalFourthNat.CPay_1884
  · exact WuPaper.ClassicalFourthNat.CPay_1885
  · exact WuPaper.ClassicalFourthNat.CPay_1886
  · exact WuPaper.ClassicalFourthNat.CPay_1887
  · exact WuPaper.ClassicalFourthNat.CPay_1888
  · exact WuPaper.ClassicalFourthNat.CPay_1889
  · exact WuPaper.ClassicalFourthNat.CPay_1890
  · exact WuPaper.ClassicalFourthNat.CPay_1891
  · exact WuPaper.ClassicalFourthNat.CPay_1892
  · exact WuPaper.ClassicalFourthNat.CPay_1893
  · exact WuPaper.ClassicalFourthNat.CPay_1894
  · exact WuPaper.ClassicalFourthNat.CPay_1895
  · exact WuPaper.ClassicalFourthNat.CPay_1896
  · exact WuPaper.ClassicalFourthNat.CPay_1897
  · exact WuPaper.ClassicalFourthNat.CPay_1898
  · exact WuPaper.ClassicalFourthNat.CPay_1899
  · exact WuPaper.ClassicalFourthNat.CPay_1900
  · exact WuPaper.ClassicalFourthNat.CPay_1901
  · exact WuPaper.ClassicalFourthNat.CPay_1902
  · exact WuPaper.ClassicalFourthNat.CPay_1903
  · exact WuPaper.ClassicalFourthNat.CPay_1904
  · exact WuPaper.ClassicalFourthNat.CPay_1905
  · exact WuPaper.ClassicalFourthNat.CPay_1906
  · exact WuPaper.ClassicalFourthNat.CPay_1907
  · exact WuPaper.ClassicalFourthNat.CPay_1908
  · exact WuPaper.ClassicalFourthNat.CPay_1909
  · exact WuPaper.ClassicalFourthNat.CPay_1910
  · exact WuPaper.ClassicalFourthNat.CPay_1911
  · exact WuPaper.ClassicalFourthNat.CPay_1912
  · exact WuPaper.ClassicalFourthNat.CPay_1913
  · exact WuPaper.ClassicalFourthNat.CPay_1914
  · exact WuPaper.ClassicalFourthNat.CPay_1915
  · exact WuPaper.ClassicalFourthNat.CPay_1916
  · exact WuPaper.ClassicalFourthNat.CPay_1917
  · exact WuPaper.ClassicalFourthNat.CPay_1918
  · exact WuPaper.ClassicalFourthNat.CPay_1919
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_029
