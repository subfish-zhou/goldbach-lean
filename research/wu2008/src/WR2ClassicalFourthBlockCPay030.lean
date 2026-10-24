import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay030
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_030 (j : Fin 64) (hj : 64*30+j.val < 2540) :
    CPay (64*30+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_1920
  · exact WuPaper.ClassicalFourthNat.CPay_1921
  · exact WuPaper.ClassicalFourthNat.CPay_1922
  · exact WuPaper.ClassicalFourthNat.CPay_1923
  · exact WuPaper.ClassicalFourthNat.CPay_1924
  · exact WuPaper.ClassicalFourthNat.CPay_1925
  · exact WuPaper.ClassicalFourthNat.CPay_1926
  · exact WuPaper.ClassicalFourthNat.CPay_1927
  · exact WuPaper.ClassicalFourthNat.CPay_1928
  · exact WuPaper.ClassicalFourthNat.CPay_1929
  · exact WuPaper.ClassicalFourthNat.CPay_1930
  · exact WuPaper.ClassicalFourthNat.CPay_1931
  · exact WuPaper.ClassicalFourthNat.CPay_1932
  · exact WuPaper.ClassicalFourthNat.CPay_1933
  · exact WuPaper.ClassicalFourthNat.CPay_1934
  · exact WuPaper.ClassicalFourthNat.CPay_1935
  · exact WuPaper.ClassicalFourthNat.CPay_1936
  · exact WuPaper.ClassicalFourthNat.CPay_1937
  · exact WuPaper.ClassicalFourthNat.CPay_1938
  · exact WuPaper.ClassicalFourthNat.CPay_1939
  · exact WuPaper.ClassicalFourthNat.CPay_1940
  · exact WuPaper.ClassicalFourthNat.CPay_1941
  · exact WuPaper.ClassicalFourthNat.CPay_1942
  · exact WuPaper.ClassicalFourthNat.CPay_1943
  · exact WuPaper.ClassicalFourthNat.CPay_1944
  · exact WuPaper.ClassicalFourthNat.CPay_1945
  · exact WuPaper.ClassicalFourthNat.CPay_1946
  · exact WuPaper.ClassicalFourthNat.CPay_1947
  · exact WuPaper.ClassicalFourthNat.CPay_1948
  · exact WuPaper.ClassicalFourthNat.CPay_1949
  · exact WuPaper.ClassicalFourthNat.CPay_1950
  · exact WuPaper.ClassicalFourthNat.CPay_1951
  · exact WuPaper.ClassicalFourthNat.CPay_1952
  · exact WuPaper.ClassicalFourthNat.CPay_1953
  · exact WuPaper.ClassicalFourthNat.CPay_1954
  · exact WuPaper.ClassicalFourthNat.CPay_1955
  · exact WuPaper.ClassicalFourthNat.CPay_1956
  · exact WuPaper.ClassicalFourthNat.CPay_1957
  · exact WuPaper.ClassicalFourthNat.CPay_1958
  · exact WuPaper.ClassicalFourthNat.CPay_1959
  · exact WuPaper.ClassicalFourthNat.CPay_1960
  · exact WuPaper.ClassicalFourthNat.CPay_1961
  · exact WuPaper.ClassicalFourthNat.CPay_1962
  · exact WuPaper.ClassicalFourthNat.CPay_1963
  · exact WuPaper.ClassicalFourthNat.CPay_1964
  · exact WuPaper.ClassicalFourthNat.CPay_1965
  · exact WuPaper.ClassicalFourthNat.CPay_1966
  · exact WuPaper.ClassicalFourthNat.CPay_1967
  · exact WuPaper.ClassicalFourthNat.CPay_1968
  · exact WuPaper.ClassicalFourthNat.CPay_1969
  · exact WuPaper.ClassicalFourthNat.CPay_1970
  · exact WuPaper.ClassicalFourthNat.CPay_1971
  · exact WuPaper.ClassicalFourthNat.CPay_1972
  · exact WuPaper.ClassicalFourthNat.CPay_1973
  · exact WuPaper.ClassicalFourthNat.CPay_1974
  · exact WuPaper.ClassicalFourthNat.CPay_1975
  · exact WuPaper.ClassicalFourthNat.CPay_1976
  · exact WuPaper.ClassicalFourthNat.CPay_1977
  · exact WuPaper.ClassicalFourthNat.CPay_1978
  · exact WuPaper.ClassicalFourthNat.CPay_1979
  · exact WuPaper.ClassicalFourthNat.CPay_1980
  · exact WuPaper.ClassicalFourthNat.CPay_1981
  · exact WuPaper.ClassicalFourthNat.CPay_1982
  · exact WuPaper.ClassicalFourthNat.CPay_1983
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_030
