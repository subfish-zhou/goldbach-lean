import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint030
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_030 (j : Fin 64) (hj : 64*30+j.val < 10541) :
    OuterPoint (64*30+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1920
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1921
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1922
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1923
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1924
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1925
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1926
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1927
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1928
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1929
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1930
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1931
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1932
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1933
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1934
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1935
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1936
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1937
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1938
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1939
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1940
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1941
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1942
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1943
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1944
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1945
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1946
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1947
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1948
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1949
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1950
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1951
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1952
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1953
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1954
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1955
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1956
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1957
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1958
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1959
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1960
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1961
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1962
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1963
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1964
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1965
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1966
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1967
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1968
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1969
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1970
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1971
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1972
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1973
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1974
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1975
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1976
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1977
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1978
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1979
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1980
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1981
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1982
  · exact WuPaper.ClassicalFourthNat.OuterPoint_1983
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_030
