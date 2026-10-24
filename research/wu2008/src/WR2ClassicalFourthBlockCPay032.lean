import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay032
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_032 (j : Fin 64) (hj : 64*32+j.val < 2540) :
    CPay (64*32+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_2048
  · exact WuPaper.ClassicalFourthNat.CPay_2049
  · exact WuPaper.ClassicalFourthNat.CPay_2050
  · exact WuPaper.ClassicalFourthNat.CPay_2051
  · exact WuPaper.ClassicalFourthNat.CPay_2052
  · exact WuPaper.ClassicalFourthNat.CPay_2053
  · exact WuPaper.ClassicalFourthNat.CPay_2054
  · exact WuPaper.ClassicalFourthNat.CPay_2055
  · exact WuPaper.ClassicalFourthNat.CPay_2056
  · exact WuPaper.ClassicalFourthNat.CPay_2057
  · exact WuPaper.ClassicalFourthNat.CPay_2058
  · exact WuPaper.ClassicalFourthNat.CPay_2059
  · exact WuPaper.ClassicalFourthNat.CPay_2060
  · exact WuPaper.ClassicalFourthNat.CPay_2061
  · exact WuPaper.ClassicalFourthNat.CPay_2062
  · exact WuPaper.ClassicalFourthNat.CPay_2063
  · exact WuPaper.ClassicalFourthNat.CPay_2064
  · exact WuPaper.ClassicalFourthNat.CPay_2065
  · exact WuPaper.ClassicalFourthNat.CPay_2066
  · exact WuPaper.ClassicalFourthNat.CPay_2067
  · exact WuPaper.ClassicalFourthNat.CPay_2068
  · exact WuPaper.ClassicalFourthNat.CPay_2069
  · exact WuPaper.ClassicalFourthNat.CPay_2070
  · exact WuPaper.ClassicalFourthNat.CPay_2071
  · exact WuPaper.ClassicalFourthNat.CPay_2072
  · exact WuPaper.ClassicalFourthNat.CPay_2073
  · exact WuPaper.ClassicalFourthNat.CPay_2074
  · exact WuPaper.ClassicalFourthNat.CPay_2075
  · exact WuPaper.ClassicalFourthNat.CPay_2076
  · exact WuPaper.ClassicalFourthNat.CPay_2077
  · exact WuPaper.ClassicalFourthNat.CPay_2078
  · exact WuPaper.ClassicalFourthNat.CPay_2079
  · exact WuPaper.ClassicalFourthNat.CPay_2080
  · exact WuPaper.ClassicalFourthNat.CPay_2081
  · exact WuPaper.ClassicalFourthNat.CPay_2082
  · exact WuPaper.ClassicalFourthNat.CPay_2083
  · exact WuPaper.ClassicalFourthNat.CPay_2084
  · exact WuPaper.ClassicalFourthNat.CPay_2085
  · exact WuPaper.ClassicalFourthNat.CPay_2086
  · exact WuPaper.ClassicalFourthNat.CPay_2087
  · exact WuPaper.ClassicalFourthNat.CPay_2088
  · exact WuPaper.ClassicalFourthNat.CPay_2089
  · exact WuPaper.ClassicalFourthNat.CPay_2090
  · exact WuPaper.ClassicalFourthNat.CPay_2091
  · exact WuPaper.ClassicalFourthNat.CPay_2092
  · exact WuPaper.ClassicalFourthNat.CPay_2093
  · exact WuPaper.ClassicalFourthNat.CPay_2094
  · exact WuPaper.ClassicalFourthNat.CPay_2095
  · exact WuPaper.ClassicalFourthNat.CPay_2096
  · exact WuPaper.ClassicalFourthNat.CPay_2097
  · exact WuPaper.ClassicalFourthNat.CPay_2098
  · exact WuPaper.ClassicalFourthNat.CPay_2099
  · exact WuPaper.ClassicalFourthNat.CPay_2100
  · exact WuPaper.ClassicalFourthNat.CPay_2101
  · exact WuPaper.ClassicalFourthNat.CPay_2102
  · exact WuPaper.ClassicalFourthNat.CPay_2103
  · exact WuPaper.ClassicalFourthNat.CPay_2104
  · exact WuPaper.ClassicalFourthNat.CPay_2105
  · exact WuPaper.ClassicalFourthNat.CPay_2106
  · exact WuPaper.ClassicalFourthNat.CPay_2107
  · exact WuPaper.ClassicalFourthNat.CPay_2108
  · exact WuPaper.ClassicalFourthNat.CPay_2109
  · exact WuPaper.ClassicalFourthNat.CPay_2110
  · exact WuPaper.ClassicalFourthNat.CPay_2111
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_032
