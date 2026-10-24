import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay030
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_030 (j : Fin 64) (hj : 64*30+j.val < 10540) :
    BPay (64*30+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_1920
  · exact WuPaper.ClassicalFourthNat.BPay_1921
  · exact WuPaper.ClassicalFourthNat.BPay_1922
  · exact WuPaper.ClassicalFourthNat.BPay_1923
  · exact WuPaper.ClassicalFourthNat.BPay_1924
  · exact WuPaper.ClassicalFourthNat.BPay_1925
  · exact WuPaper.ClassicalFourthNat.BPay_1926
  · exact WuPaper.ClassicalFourthNat.BPay_1927
  · exact WuPaper.ClassicalFourthNat.BPay_1928
  · exact WuPaper.ClassicalFourthNat.BPay_1929
  · exact WuPaper.ClassicalFourthNat.BPay_1930
  · exact WuPaper.ClassicalFourthNat.BPay_1931
  · exact WuPaper.ClassicalFourthNat.BPay_1932
  · exact WuPaper.ClassicalFourthNat.BPay_1933
  · exact WuPaper.ClassicalFourthNat.BPay_1934
  · exact WuPaper.ClassicalFourthNat.BPay_1935
  · exact WuPaper.ClassicalFourthNat.BPay_1936
  · exact WuPaper.ClassicalFourthNat.BPay_1937
  · exact WuPaper.ClassicalFourthNat.BPay_1938
  · exact WuPaper.ClassicalFourthNat.BPay_1939
  · exact WuPaper.ClassicalFourthNat.BPay_1940
  · exact WuPaper.ClassicalFourthNat.BPay_1941
  · exact WuPaper.ClassicalFourthNat.BPay_1942
  · exact WuPaper.ClassicalFourthNat.BPay_1943
  · exact WuPaper.ClassicalFourthNat.BPay_1944
  · exact WuPaper.ClassicalFourthNat.BPay_1945
  · exact WuPaper.ClassicalFourthNat.BPay_1946
  · exact WuPaper.ClassicalFourthNat.BPay_1947
  · exact WuPaper.ClassicalFourthNat.BPay_1948
  · exact WuPaper.ClassicalFourthNat.BPay_1949
  · exact WuPaper.ClassicalFourthNat.BPay_1950
  · exact WuPaper.ClassicalFourthNat.BPay_1951
  · exact WuPaper.ClassicalFourthNat.BPay_1952
  · exact WuPaper.ClassicalFourthNat.BPay_1953
  · exact WuPaper.ClassicalFourthNat.BPay_1954
  · exact WuPaper.ClassicalFourthNat.BPay_1955
  · exact WuPaper.ClassicalFourthNat.BPay_1956
  · exact WuPaper.ClassicalFourthNat.BPay_1957
  · exact WuPaper.ClassicalFourthNat.BPay_1958
  · exact WuPaper.ClassicalFourthNat.BPay_1959
  · exact WuPaper.ClassicalFourthNat.BPay_1960
  · exact WuPaper.ClassicalFourthNat.BPay_1961
  · exact WuPaper.ClassicalFourthNat.BPay_1962
  · exact WuPaper.ClassicalFourthNat.BPay_1963
  · exact WuPaper.ClassicalFourthNat.BPay_1964
  · exact WuPaper.ClassicalFourthNat.BPay_1965
  · exact WuPaper.ClassicalFourthNat.BPay_1966
  · exact WuPaper.ClassicalFourthNat.BPay_1967
  · exact WuPaper.ClassicalFourthNat.BPay_1968
  · exact WuPaper.ClassicalFourthNat.BPay_1969
  · exact WuPaper.ClassicalFourthNat.BPay_1970
  · exact WuPaper.ClassicalFourthNat.BPay_1971
  · exact WuPaper.ClassicalFourthNat.BPay_1972
  · exact WuPaper.ClassicalFourthNat.BPay_1973
  · exact WuPaper.ClassicalFourthNat.BPay_1974
  · exact WuPaper.ClassicalFourthNat.BPay_1975
  · exact WuPaper.ClassicalFourthNat.BPay_1976
  · exact WuPaper.ClassicalFourthNat.BPay_1977
  · exact WuPaper.ClassicalFourthNat.BPay_1978
  · exact WuPaper.ClassicalFourthNat.BPay_1979
  · exact WuPaper.ClassicalFourthNat.BPay_1980
  · exact WuPaper.ClassicalFourthNat.BPay_1981
  · exact WuPaper.ClassicalFourthNat.BPay_1982
  · exact WuPaper.ClassicalFourthNat.BPay_1983
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_030
