import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay029
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_029 (j : Fin 64) (hj : 64*29+j.val < 2540) :
    DPay (64*29+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_1856
  · exact WuPaper.ClassicalFourthNat.DPay_1857
  · exact WuPaper.ClassicalFourthNat.DPay_1858
  · exact WuPaper.ClassicalFourthNat.DPay_1859
  · exact WuPaper.ClassicalFourthNat.DPay_1860
  · exact WuPaper.ClassicalFourthNat.DPay_1861
  · exact WuPaper.ClassicalFourthNat.DPay_1862
  · exact WuPaper.ClassicalFourthNat.DPay_1863
  · exact WuPaper.ClassicalFourthNat.DPay_1864
  · exact WuPaper.ClassicalFourthNat.DPay_1865
  · exact WuPaper.ClassicalFourthNat.DPay_1866
  · exact WuPaper.ClassicalFourthNat.DPay_1867
  · exact WuPaper.ClassicalFourthNat.DPay_1868
  · exact WuPaper.ClassicalFourthNat.DPay_1869
  · exact WuPaper.ClassicalFourthNat.DPay_1870
  · exact WuPaper.ClassicalFourthNat.DPay_1871
  · exact WuPaper.ClassicalFourthNat.DPay_1872
  · exact WuPaper.ClassicalFourthNat.DPay_1873
  · exact WuPaper.ClassicalFourthNat.DPay_1874
  · exact WuPaper.ClassicalFourthNat.DPay_1875
  · exact WuPaper.ClassicalFourthNat.DPay_1876
  · exact WuPaper.ClassicalFourthNat.DPay_1877
  · exact WuPaper.ClassicalFourthNat.DPay_1878
  · exact WuPaper.ClassicalFourthNat.DPay_1879
  · exact WuPaper.ClassicalFourthNat.DPay_1880
  · exact WuPaper.ClassicalFourthNat.DPay_1881
  · exact WuPaper.ClassicalFourthNat.DPay_1882
  · exact WuPaper.ClassicalFourthNat.DPay_1883
  · exact WuPaper.ClassicalFourthNat.DPay_1884
  · exact WuPaper.ClassicalFourthNat.DPay_1885
  · exact WuPaper.ClassicalFourthNat.DPay_1886
  · exact WuPaper.ClassicalFourthNat.DPay_1887
  · exact WuPaper.ClassicalFourthNat.DPay_1888
  · exact WuPaper.ClassicalFourthNat.DPay_1889
  · exact WuPaper.ClassicalFourthNat.DPay_1890
  · exact WuPaper.ClassicalFourthNat.DPay_1891
  · exact WuPaper.ClassicalFourthNat.DPay_1892
  · exact WuPaper.ClassicalFourthNat.DPay_1893
  · exact WuPaper.ClassicalFourthNat.DPay_1894
  · exact WuPaper.ClassicalFourthNat.DPay_1895
  · exact WuPaper.ClassicalFourthNat.DPay_1896
  · exact WuPaper.ClassicalFourthNat.DPay_1897
  · exact WuPaper.ClassicalFourthNat.DPay_1898
  · exact WuPaper.ClassicalFourthNat.DPay_1899
  · exact WuPaper.ClassicalFourthNat.DPay_1900
  · exact WuPaper.ClassicalFourthNat.DPay_1901
  · exact WuPaper.ClassicalFourthNat.DPay_1902
  · exact WuPaper.ClassicalFourthNat.DPay_1903
  · exact WuPaper.ClassicalFourthNat.DPay_1904
  · exact WuPaper.ClassicalFourthNat.DPay_1905
  · exact WuPaper.ClassicalFourthNat.DPay_1906
  · exact WuPaper.ClassicalFourthNat.DPay_1907
  · exact WuPaper.ClassicalFourthNat.DPay_1908
  · exact WuPaper.ClassicalFourthNat.DPay_1909
  · exact WuPaper.ClassicalFourthNat.DPay_1910
  · exact WuPaper.ClassicalFourthNat.DPay_1911
  · exact WuPaper.ClassicalFourthNat.DPay_1912
  · exact WuPaper.ClassicalFourthNat.DPay_1913
  · exact WuPaper.ClassicalFourthNat.DPay_1914
  · exact WuPaper.ClassicalFourthNat.DPay_1915
  · exact WuPaper.ClassicalFourthNat.DPay_1916
  · exact WuPaper.ClassicalFourthNat.DPay_1917
  · exact WuPaper.ClassicalFourthNat.DPay_1918
  · exact WuPaper.ClassicalFourthNat.DPay_1919
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_029
