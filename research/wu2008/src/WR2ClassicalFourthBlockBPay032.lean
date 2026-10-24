import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay032
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_032 (j : Fin 64) (hj : 64*32+j.val < 10540) :
    BPay (64*32+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_2048
  · exact WuPaper.ClassicalFourthNat.BPay_2049
  · exact WuPaper.ClassicalFourthNat.BPay_2050
  · exact WuPaper.ClassicalFourthNat.BPay_2051
  · exact WuPaper.ClassicalFourthNat.BPay_2052
  · exact WuPaper.ClassicalFourthNat.BPay_2053
  · exact WuPaper.ClassicalFourthNat.BPay_2054
  · exact WuPaper.ClassicalFourthNat.BPay_2055
  · exact WuPaper.ClassicalFourthNat.BPay_2056
  · exact WuPaper.ClassicalFourthNat.BPay_2057
  · exact WuPaper.ClassicalFourthNat.BPay_2058
  · exact WuPaper.ClassicalFourthNat.BPay_2059
  · exact WuPaper.ClassicalFourthNat.BPay_2060
  · exact WuPaper.ClassicalFourthNat.BPay_2061
  · exact WuPaper.ClassicalFourthNat.BPay_2062
  · exact WuPaper.ClassicalFourthNat.BPay_2063
  · exact WuPaper.ClassicalFourthNat.BPay_2064
  · exact WuPaper.ClassicalFourthNat.BPay_2065
  · exact WuPaper.ClassicalFourthNat.BPay_2066
  · exact WuPaper.ClassicalFourthNat.BPay_2067
  · exact WuPaper.ClassicalFourthNat.BPay_2068
  · exact WuPaper.ClassicalFourthNat.BPay_2069
  · exact WuPaper.ClassicalFourthNat.BPay_2070
  · exact WuPaper.ClassicalFourthNat.BPay_2071
  · exact WuPaper.ClassicalFourthNat.BPay_2072
  · exact WuPaper.ClassicalFourthNat.BPay_2073
  · exact WuPaper.ClassicalFourthNat.BPay_2074
  · exact WuPaper.ClassicalFourthNat.BPay_2075
  · exact WuPaper.ClassicalFourthNat.BPay_2076
  · exact WuPaper.ClassicalFourthNat.BPay_2077
  · exact WuPaper.ClassicalFourthNat.BPay_2078
  · exact WuPaper.ClassicalFourthNat.BPay_2079
  · exact WuPaper.ClassicalFourthNat.BPay_2080
  · exact WuPaper.ClassicalFourthNat.BPay_2081
  · exact WuPaper.ClassicalFourthNat.BPay_2082
  · exact WuPaper.ClassicalFourthNat.BPay_2083
  · exact WuPaper.ClassicalFourthNat.BPay_2084
  · exact WuPaper.ClassicalFourthNat.BPay_2085
  · exact WuPaper.ClassicalFourthNat.BPay_2086
  · exact WuPaper.ClassicalFourthNat.BPay_2087
  · exact WuPaper.ClassicalFourthNat.BPay_2088
  · exact WuPaper.ClassicalFourthNat.BPay_2089
  · exact WuPaper.ClassicalFourthNat.BPay_2090
  · exact WuPaper.ClassicalFourthNat.BPay_2091
  · exact WuPaper.ClassicalFourthNat.BPay_2092
  · exact WuPaper.ClassicalFourthNat.BPay_2093
  · exact WuPaper.ClassicalFourthNat.BPay_2094
  · exact WuPaper.ClassicalFourthNat.BPay_2095
  · exact WuPaper.ClassicalFourthNat.BPay_2096
  · exact WuPaper.ClassicalFourthNat.BPay_2097
  · exact WuPaper.ClassicalFourthNat.BPay_2098
  · exact WuPaper.ClassicalFourthNat.BPay_2099
  · exact WuPaper.ClassicalFourthNat.BPay_2100
  · exact WuPaper.ClassicalFourthNat.BPay_2101
  · exact WuPaper.ClassicalFourthNat.BPay_2102
  · exact WuPaper.ClassicalFourthNat.BPay_2103
  · exact WuPaper.ClassicalFourthNat.BPay_2104
  · exact WuPaper.ClassicalFourthNat.BPay_2105
  · exact WuPaper.ClassicalFourthNat.BPay_2106
  · exact WuPaper.ClassicalFourthNat.BPay_2107
  · exact WuPaper.ClassicalFourthNat.BPay_2108
  · exact WuPaper.ClassicalFourthNat.BPay_2109
  · exact WuPaper.ClassicalFourthNat.BPay_2110
  · exact WuPaper.ClassicalFourthNat.BPay_2111
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_032
