import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay030
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_030 (j : Fin 64) (hj : 64*30+j.val < 10540) :
    OuterPay (64*30+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_1920
  · exact WuPaper.ClassicalFourthNat.outerPay_1921
  · exact WuPaper.ClassicalFourthNat.outerPay_1922
  · exact WuPaper.ClassicalFourthNat.outerPay_1923
  · exact WuPaper.ClassicalFourthNat.outerPay_1924
  · exact WuPaper.ClassicalFourthNat.outerPay_1925
  · exact WuPaper.ClassicalFourthNat.outerPay_1926
  · exact WuPaper.ClassicalFourthNat.outerPay_1927
  · exact WuPaper.ClassicalFourthNat.outerPay_1928
  · exact WuPaper.ClassicalFourthNat.outerPay_1929
  · exact WuPaper.ClassicalFourthNat.outerPay_1930
  · exact WuPaper.ClassicalFourthNat.outerPay_1931
  · exact WuPaper.ClassicalFourthNat.outerPay_1932
  · exact WuPaper.ClassicalFourthNat.outerPay_1933
  · exact WuPaper.ClassicalFourthNat.outerPay_1934
  · exact WuPaper.ClassicalFourthNat.outerPay_1935
  · exact WuPaper.ClassicalFourthNat.outerPay_1936
  · exact WuPaper.ClassicalFourthNat.outerPay_1937
  · exact WuPaper.ClassicalFourthNat.outerPay_1938
  · exact WuPaper.ClassicalFourthNat.outerPay_1939
  · exact WuPaper.ClassicalFourthNat.outerPay_1940
  · exact WuPaper.ClassicalFourthNat.outerPay_1941
  · exact WuPaper.ClassicalFourthNat.outerPay_1942
  · exact WuPaper.ClassicalFourthNat.outerPay_1943
  · exact WuPaper.ClassicalFourthNat.outerPay_1944
  · exact WuPaper.ClassicalFourthNat.outerPay_1945
  · exact WuPaper.ClassicalFourthNat.outerPay_1946
  · exact WuPaper.ClassicalFourthNat.outerPay_1947
  · exact WuPaper.ClassicalFourthNat.outerPay_1948
  · exact WuPaper.ClassicalFourthNat.outerPay_1949
  · exact WuPaper.ClassicalFourthNat.outerPay_1950
  · exact WuPaper.ClassicalFourthNat.outerPay_1951
  · exact WuPaper.ClassicalFourthNat.outerPay_1952
  · exact WuPaper.ClassicalFourthNat.outerPay_1953
  · exact WuPaper.ClassicalFourthNat.outerPay_1954
  · exact WuPaper.ClassicalFourthNat.outerPay_1955
  · exact WuPaper.ClassicalFourthNat.outerPay_1956
  · exact WuPaper.ClassicalFourthNat.outerPay_1957
  · exact WuPaper.ClassicalFourthNat.outerPay_1958
  · exact WuPaper.ClassicalFourthNat.outerPay_1959
  · exact WuPaper.ClassicalFourthNat.outerPay_1960
  · exact WuPaper.ClassicalFourthNat.outerPay_1961
  · exact WuPaper.ClassicalFourthNat.outerPay_1962
  · exact WuPaper.ClassicalFourthNat.outerPay_1963
  · exact WuPaper.ClassicalFourthNat.outerPay_1964
  · exact WuPaper.ClassicalFourthNat.outerPay_1965
  · exact WuPaper.ClassicalFourthNat.outerPay_1966
  · exact WuPaper.ClassicalFourthNat.outerPay_1967
  · exact WuPaper.ClassicalFourthNat.outerPay_1968
  · exact WuPaper.ClassicalFourthNat.outerPay_1969
  · exact WuPaper.ClassicalFourthNat.outerPay_1970
  · exact WuPaper.ClassicalFourthNat.outerPay_1971
  · exact WuPaper.ClassicalFourthNat.outerPay_1972
  · exact WuPaper.ClassicalFourthNat.outerPay_1973
  · exact WuPaper.ClassicalFourthNat.outerPay_1974
  · exact WuPaper.ClassicalFourthNat.outerPay_1975
  · exact WuPaper.ClassicalFourthNat.outerPay_1976
  · exact WuPaper.ClassicalFourthNat.outerPay_1977
  · exact WuPaper.ClassicalFourthNat.outerPay_1978
  · exact WuPaper.ClassicalFourthNat.outerPay_1979
  · exact WuPaper.ClassicalFourthNat.outerPay_1980
  · exact WuPaper.ClassicalFourthNat.outerPay_1981
  · exact WuPaper.ClassicalFourthNat.outerPay_1982
  · exact WuPaper.ClassicalFourthNat.outerPay_1983
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_030
