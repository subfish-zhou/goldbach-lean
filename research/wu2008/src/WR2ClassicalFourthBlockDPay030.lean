import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay030
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_030 (j : Fin 64) (hj : 64*30+j.val < 2540) :
    DPay (64*30+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_1920
  · exact WuPaper.ClassicalFourthNat.DPay_1921
  · exact WuPaper.ClassicalFourthNat.DPay_1922
  · exact WuPaper.ClassicalFourthNat.DPay_1923
  · exact WuPaper.ClassicalFourthNat.DPay_1924
  · exact WuPaper.ClassicalFourthNat.DPay_1925
  · exact WuPaper.ClassicalFourthNat.DPay_1926
  · exact WuPaper.ClassicalFourthNat.DPay_1927
  · exact WuPaper.ClassicalFourthNat.DPay_1928
  · exact WuPaper.ClassicalFourthNat.DPay_1929
  · exact WuPaper.ClassicalFourthNat.DPay_1930
  · exact WuPaper.ClassicalFourthNat.DPay_1931
  · exact WuPaper.ClassicalFourthNat.DPay_1932
  · exact WuPaper.ClassicalFourthNat.DPay_1933
  · exact WuPaper.ClassicalFourthNat.DPay_1934
  · exact WuPaper.ClassicalFourthNat.DPay_1935
  · exact WuPaper.ClassicalFourthNat.DPay_1936
  · exact WuPaper.ClassicalFourthNat.DPay_1937
  · exact WuPaper.ClassicalFourthNat.DPay_1938
  · exact WuPaper.ClassicalFourthNat.DPay_1939
  · exact WuPaper.ClassicalFourthNat.DPay_1940
  · exact WuPaper.ClassicalFourthNat.DPay_1941
  · exact WuPaper.ClassicalFourthNat.DPay_1942
  · exact WuPaper.ClassicalFourthNat.DPay_1943
  · exact WuPaper.ClassicalFourthNat.DPay_1944
  · exact WuPaper.ClassicalFourthNat.DPay_1945
  · exact WuPaper.ClassicalFourthNat.DPay_1946
  · exact WuPaper.ClassicalFourthNat.DPay_1947
  · exact WuPaper.ClassicalFourthNat.DPay_1948
  · exact WuPaper.ClassicalFourthNat.DPay_1949
  · exact WuPaper.ClassicalFourthNat.DPay_1950
  · exact WuPaper.ClassicalFourthNat.DPay_1951
  · exact WuPaper.ClassicalFourthNat.DPay_1952
  · exact WuPaper.ClassicalFourthNat.DPay_1953
  · exact WuPaper.ClassicalFourthNat.DPay_1954
  · exact WuPaper.ClassicalFourthNat.DPay_1955
  · exact WuPaper.ClassicalFourthNat.DPay_1956
  · exact WuPaper.ClassicalFourthNat.DPay_1957
  · exact WuPaper.ClassicalFourthNat.DPay_1958
  · exact WuPaper.ClassicalFourthNat.DPay_1959
  · exact WuPaper.ClassicalFourthNat.DPay_1960
  · exact WuPaper.ClassicalFourthNat.DPay_1961
  · exact WuPaper.ClassicalFourthNat.DPay_1962
  · exact WuPaper.ClassicalFourthNat.DPay_1963
  · exact WuPaper.ClassicalFourthNat.DPay_1964
  · exact WuPaper.ClassicalFourthNat.DPay_1965
  · exact WuPaper.ClassicalFourthNat.DPay_1966
  · exact WuPaper.ClassicalFourthNat.DPay_1967
  · exact WuPaper.ClassicalFourthNat.DPay_1968
  · exact WuPaper.ClassicalFourthNat.DPay_1969
  · exact WuPaper.ClassicalFourthNat.DPay_1970
  · exact WuPaper.ClassicalFourthNat.DPay_1971
  · exact WuPaper.ClassicalFourthNat.DPay_1972
  · exact WuPaper.ClassicalFourthNat.DPay_1973
  · exact WuPaper.ClassicalFourthNat.DPay_1974
  · exact WuPaper.ClassicalFourthNat.DPay_1975
  · exact WuPaper.ClassicalFourthNat.DPay_1976
  · exact WuPaper.ClassicalFourthNat.DPay_1977
  · exact WuPaper.ClassicalFourthNat.DPay_1978
  · exact WuPaper.ClassicalFourthNat.DPay_1979
  · exact WuPaper.ClassicalFourthNat.DPay_1980
  · exact WuPaper.ClassicalFourthNat.DPay_1981
  · exact WuPaper.ClassicalFourthNat.DPay_1982
  · exact WuPaper.ClassicalFourthNat.DPay_1983
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_030
