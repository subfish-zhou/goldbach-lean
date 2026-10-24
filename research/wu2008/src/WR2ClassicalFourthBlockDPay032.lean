import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay032
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_032 (j : Fin 64) (hj : 64*32+j.val < 2540) :
    DPay (64*32+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_2048
  · exact WuPaper.ClassicalFourthNat.DPay_2049
  · exact WuPaper.ClassicalFourthNat.DPay_2050
  · exact WuPaper.ClassicalFourthNat.DPay_2051
  · exact WuPaper.ClassicalFourthNat.DPay_2052
  · exact WuPaper.ClassicalFourthNat.DPay_2053
  · exact WuPaper.ClassicalFourthNat.DPay_2054
  · exact WuPaper.ClassicalFourthNat.DPay_2055
  · exact WuPaper.ClassicalFourthNat.DPay_2056
  · exact WuPaper.ClassicalFourthNat.DPay_2057
  · exact WuPaper.ClassicalFourthNat.DPay_2058
  · exact WuPaper.ClassicalFourthNat.DPay_2059
  · exact WuPaper.ClassicalFourthNat.DPay_2060
  · exact WuPaper.ClassicalFourthNat.DPay_2061
  · exact WuPaper.ClassicalFourthNat.DPay_2062
  · exact WuPaper.ClassicalFourthNat.DPay_2063
  · exact WuPaper.ClassicalFourthNat.DPay_2064
  · exact WuPaper.ClassicalFourthNat.DPay_2065
  · exact WuPaper.ClassicalFourthNat.DPay_2066
  · exact WuPaper.ClassicalFourthNat.DPay_2067
  · exact WuPaper.ClassicalFourthNat.DPay_2068
  · exact WuPaper.ClassicalFourthNat.DPay_2069
  · exact WuPaper.ClassicalFourthNat.DPay_2070
  · exact WuPaper.ClassicalFourthNat.DPay_2071
  · exact WuPaper.ClassicalFourthNat.DPay_2072
  · exact WuPaper.ClassicalFourthNat.DPay_2073
  · exact WuPaper.ClassicalFourthNat.DPay_2074
  · exact WuPaper.ClassicalFourthNat.DPay_2075
  · exact WuPaper.ClassicalFourthNat.DPay_2076
  · exact WuPaper.ClassicalFourthNat.DPay_2077
  · exact WuPaper.ClassicalFourthNat.DPay_2078
  · exact WuPaper.ClassicalFourthNat.DPay_2079
  · exact WuPaper.ClassicalFourthNat.DPay_2080
  · exact WuPaper.ClassicalFourthNat.DPay_2081
  · exact WuPaper.ClassicalFourthNat.DPay_2082
  · exact WuPaper.ClassicalFourthNat.DPay_2083
  · exact WuPaper.ClassicalFourthNat.DPay_2084
  · exact WuPaper.ClassicalFourthNat.DPay_2085
  · exact WuPaper.ClassicalFourthNat.DPay_2086
  · exact WuPaper.ClassicalFourthNat.DPay_2087
  · exact WuPaper.ClassicalFourthNat.DPay_2088
  · exact WuPaper.ClassicalFourthNat.DPay_2089
  · exact WuPaper.ClassicalFourthNat.DPay_2090
  · exact WuPaper.ClassicalFourthNat.DPay_2091
  · exact WuPaper.ClassicalFourthNat.DPay_2092
  · exact WuPaper.ClassicalFourthNat.DPay_2093
  · exact WuPaper.ClassicalFourthNat.DPay_2094
  · exact WuPaper.ClassicalFourthNat.DPay_2095
  · exact WuPaper.ClassicalFourthNat.DPay_2096
  · exact WuPaper.ClassicalFourthNat.DPay_2097
  · exact WuPaper.ClassicalFourthNat.DPay_2098
  · exact WuPaper.ClassicalFourthNat.DPay_2099
  · exact WuPaper.ClassicalFourthNat.DPay_2100
  · exact WuPaper.ClassicalFourthNat.DPay_2101
  · exact WuPaper.ClassicalFourthNat.DPay_2102
  · exact WuPaper.ClassicalFourthNat.DPay_2103
  · exact WuPaper.ClassicalFourthNat.DPay_2104
  · exact WuPaper.ClassicalFourthNat.DPay_2105
  · exact WuPaper.ClassicalFourthNat.DPay_2106
  · exact WuPaper.ClassicalFourthNat.DPay_2107
  · exact WuPaper.ClassicalFourthNat.DPay_2108
  · exact WuPaper.ClassicalFourthNat.DPay_2109
  · exact WuPaper.ClassicalFourthNat.DPay_2110
  · exact WuPaper.ClassicalFourthNat.DPay_2111
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_032
