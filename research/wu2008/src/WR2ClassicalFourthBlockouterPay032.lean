import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay032
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_032 (j : Fin 64) (hj : 64*32+j.val < 10540) :
    OuterPay (64*32+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_2048
  · exact WuPaper.ClassicalFourthNat.outerPay_2049
  · exact WuPaper.ClassicalFourthNat.outerPay_2050
  · exact WuPaper.ClassicalFourthNat.outerPay_2051
  · exact WuPaper.ClassicalFourthNat.outerPay_2052
  · exact WuPaper.ClassicalFourthNat.outerPay_2053
  · exact WuPaper.ClassicalFourthNat.outerPay_2054
  · exact WuPaper.ClassicalFourthNat.outerPay_2055
  · exact WuPaper.ClassicalFourthNat.outerPay_2056
  · exact WuPaper.ClassicalFourthNat.outerPay_2057
  · exact WuPaper.ClassicalFourthNat.outerPay_2058
  · exact WuPaper.ClassicalFourthNat.outerPay_2059
  · exact WuPaper.ClassicalFourthNat.outerPay_2060
  · exact WuPaper.ClassicalFourthNat.outerPay_2061
  · exact WuPaper.ClassicalFourthNat.outerPay_2062
  · exact WuPaper.ClassicalFourthNat.outerPay_2063
  · exact WuPaper.ClassicalFourthNat.outerPay_2064
  · exact WuPaper.ClassicalFourthNat.outerPay_2065
  · exact WuPaper.ClassicalFourthNat.outerPay_2066
  · exact WuPaper.ClassicalFourthNat.outerPay_2067
  · exact WuPaper.ClassicalFourthNat.outerPay_2068
  · exact WuPaper.ClassicalFourthNat.outerPay_2069
  · exact WuPaper.ClassicalFourthNat.outerPay_2070
  · exact WuPaper.ClassicalFourthNat.outerPay_2071
  · exact WuPaper.ClassicalFourthNat.outerPay_2072
  · exact WuPaper.ClassicalFourthNat.outerPay_2073
  · exact WuPaper.ClassicalFourthNat.outerPay_2074
  · exact WuPaper.ClassicalFourthNat.outerPay_2075
  · exact WuPaper.ClassicalFourthNat.outerPay_2076
  · exact WuPaper.ClassicalFourthNat.outerPay_2077
  · exact WuPaper.ClassicalFourthNat.outerPay_2078
  · exact WuPaper.ClassicalFourthNat.outerPay_2079
  · exact WuPaper.ClassicalFourthNat.outerPay_2080
  · exact WuPaper.ClassicalFourthNat.outerPay_2081
  · exact WuPaper.ClassicalFourthNat.outerPay_2082
  · exact WuPaper.ClassicalFourthNat.outerPay_2083
  · exact WuPaper.ClassicalFourthNat.outerPay_2084
  · exact WuPaper.ClassicalFourthNat.outerPay_2085
  · exact WuPaper.ClassicalFourthNat.outerPay_2086
  · exact WuPaper.ClassicalFourthNat.outerPay_2087
  · exact WuPaper.ClassicalFourthNat.outerPay_2088
  · exact WuPaper.ClassicalFourthNat.outerPay_2089
  · exact WuPaper.ClassicalFourthNat.outerPay_2090
  · exact WuPaper.ClassicalFourthNat.outerPay_2091
  · exact WuPaper.ClassicalFourthNat.outerPay_2092
  · exact WuPaper.ClassicalFourthNat.outerPay_2093
  · exact WuPaper.ClassicalFourthNat.outerPay_2094
  · exact WuPaper.ClassicalFourthNat.outerPay_2095
  · exact WuPaper.ClassicalFourthNat.outerPay_2096
  · exact WuPaper.ClassicalFourthNat.outerPay_2097
  · exact WuPaper.ClassicalFourthNat.outerPay_2098
  · exact WuPaper.ClassicalFourthNat.outerPay_2099
  · exact WuPaper.ClassicalFourthNat.outerPay_2100
  · exact WuPaper.ClassicalFourthNat.outerPay_2101
  · exact WuPaper.ClassicalFourthNat.outerPay_2102
  · exact WuPaper.ClassicalFourthNat.outerPay_2103
  · exact WuPaper.ClassicalFourthNat.outerPay_2104
  · exact WuPaper.ClassicalFourthNat.outerPay_2105
  · exact WuPaper.ClassicalFourthNat.outerPay_2106
  · exact WuPaper.ClassicalFourthNat.outerPay_2107
  · exact WuPaper.ClassicalFourthNat.outerPay_2108
  · exact WuPaper.ClassicalFourthNat.outerPay_2109
  · exact WuPaper.ClassicalFourthNat.outerPay_2110
  · exact WuPaper.ClassicalFourthNat.outerPay_2111
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_032
