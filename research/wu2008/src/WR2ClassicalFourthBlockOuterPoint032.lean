import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatOuterPoint032
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OuterPoint_block_032 (j : Fin 64) (hj : 64*32+j.val < 10541) :
    OuterPoint (64*32+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2048
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2049
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2050
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2051
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2052
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2053
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2054
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2055
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2056
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2057
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2058
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2059
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2060
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2061
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2062
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2063
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2064
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2065
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2066
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2067
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2068
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2069
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2070
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2071
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2072
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2073
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2074
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2075
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2076
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2077
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2078
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2079
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2080
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2081
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2082
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2083
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2084
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2085
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2086
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2087
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2088
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2089
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2090
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2091
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2092
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2093
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2094
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2095
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2096
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2097
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2098
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2099
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2100
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2101
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2102
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2103
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2104
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2105
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2106
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2107
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2108
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2109
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2110
  · exact WuPaper.ClassicalFourthNat.OuterPoint_2111
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.OuterPoint_block_032
