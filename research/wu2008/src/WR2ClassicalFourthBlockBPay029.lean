import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay029
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_029 (j : Fin 64) (hj : 64*29+j.val < 10540) :
    BPay (64*29+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_1856
  · exact WuPaper.ClassicalFourthNat.BPay_1857
  · exact WuPaper.ClassicalFourthNat.BPay_1858
  · exact WuPaper.ClassicalFourthNat.BPay_1859
  · exact WuPaper.ClassicalFourthNat.BPay_1860
  · exact WuPaper.ClassicalFourthNat.BPay_1861
  · exact WuPaper.ClassicalFourthNat.BPay_1862
  · exact WuPaper.ClassicalFourthNat.BPay_1863
  · exact WuPaper.ClassicalFourthNat.BPay_1864
  · exact WuPaper.ClassicalFourthNat.BPay_1865
  · exact WuPaper.ClassicalFourthNat.BPay_1866
  · exact WuPaper.ClassicalFourthNat.BPay_1867
  · exact WuPaper.ClassicalFourthNat.BPay_1868
  · exact WuPaper.ClassicalFourthNat.BPay_1869
  · exact WuPaper.ClassicalFourthNat.BPay_1870
  · exact WuPaper.ClassicalFourthNat.BPay_1871
  · exact WuPaper.ClassicalFourthNat.BPay_1872
  · exact WuPaper.ClassicalFourthNat.BPay_1873
  · exact WuPaper.ClassicalFourthNat.BPay_1874
  · exact WuPaper.ClassicalFourthNat.BPay_1875
  · exact WuPaper.ClassicalFourthNat.BPay_1876
  · exact WuPaper.ClassicalFourthNat.BPay_1877
  · exact WuPaper.ClassicalFourthNat.BPay_1878
  · exact WuPaper.ClassicalFourthNat.BPay_1879
  · exact WuPaper.ClassicalFourthNat.BPay_1880
  · exact WuPaper.ClassicalFourthNat.BPay_1881
  · exact WuPaper.ClassicalFourthNat.BPay_1882
  · exact WuPaper.ClassicalFourthNat.BPay_1883
  · exact WuPaper.ClassicalFourthNat.BPay_1884
  · exact WuPaper.ClassicalFourthNat.BPay_1885
  · exact WuPaper.ClassicalFourthNat.BPay_1886
  · exact WuPaper.ClassicalFourthNat.BPay_1887
  · exact WuPaper.ClassicalFourthNat.BPay_1888
  · exact WuPaper.ClassicalFourthNat.BPay_1889
  · exact WuPaper.ClassicalFourthNat.BPay_1890
  · exact WuPaper.ClassicalFourthNat.BPay_1891
  · exact WuPaper.ClassicalFourthNat.BPay_1892
  · exact WuPaper.ClassicalFourthNat.BPay_1893
  · exact WuPaper.ClassicalFourthNat.BPay_1894
  · exact WuPaper.ClassicalFourthNat.BPay_1895
  · exact WuPaper.ClassicalFourthNat.BPay_1896
  · exact WuPaper.ClassicalFourthNat.BPay_1897
  · exact WuPaper.ClassicalFourthNat.BPay_1898
  · exact WuPaper.ClassicalFourthNat.BPay_1899
  · exact WuPaper.ClassicalFourthNat.BPay_1900
  · exact WuPaper.ClassicalFourthNat.BPay_1901
  · exact WuPaper.ClassicalFourthNat.BPay_1902
  · exact WuPaper.ClassicalFourthNat.BPay_1903
  · exact WuPaper.ClassicalFourthNat.BPay_1904
  · exact WuPaper.ClassicalFourthNat.BPay_1905
  · exact WuPaper.ClassicalFourthNat.BPay_1906
  · exact WuPaper.ClassicalFourthNat.BPay_1907
  · exact WuPaper.ClassicalFourthNat.BPay_1908
  · exact WuPaper.ClassicalFourthNat.BPay_1909
  · exact WuPaper.ClassicalFourthNat.BPay_1910
  · exact WuPaper.ClassicalFourthNat.BPay_1911
  · exact WuPaper.ClassicalFourthNat.BPay_1912
  · exact WuPaper.ClassicalFourthNat.BPay_1913
  · exact WuPaper.ClassicalFourthNat.BPay_1914
  · exact WuPaper.ClassicalFourthNat.BPay_1915
  · exact WuPaper.ClassicalFourthNat.BPay_1916
  · exact WuPaper.ClassicalFourthNat.BPay_1917
  · exact WuPaper.ClassicalFourthNat.BPay_1918
  · exact WuPaper.ClassicalFourthNat.BPay_1919
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_029
