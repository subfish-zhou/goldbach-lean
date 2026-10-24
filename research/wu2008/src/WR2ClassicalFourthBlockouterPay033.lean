import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay033
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_033 (j : Fin 64) (hj : 64*33+j.val < 10540) :
    OuterPay (64*33+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_2112
  · exact WuPaper.ClassicalFourthNat.outerPay_2113
  · exact WuPaper.ClassicalFourthNat.outerPay_2114
  · exact WuPaper.ClassicalFourthNat.outerPay_2115
  · exact WuPaper.ClassicalFourthNat.outerPay_2116
  · exact WuPaper.ClassicalFourthNat.outerPay_2117
  · exact WuPaper.ClassicalFourthNat.outerPay_2118
  · exact WuPaper.ClassicalFourthNat.outerPay_2119
  · exact WuPaper.ClassicalFourthNat.outerPay_2120
  · exact WuPaper.ClassicalFourthNat.outerPay_2121
  · exact WuPaper.ClassicalFourthNat.outerPay_2122
  · exact WuPaper.ClassicalFourthNat.outerPay_2123
  · exact WuPaper.ClassicalFourthNat.outerPay_2124
  · exact WuPaper.ClassicalFourthNat.outerPay_2125
  · exact WuPaper.ClassicalFourthNat.outerPay_2126
  · exact WuPaper.ClassicalFourthNat.outerPay_2127
  · exact WuPaper.ClassicalFourthNat.outerPay_2128
  · exact WuPaper.ClassicalFourthNat.outerPay_2129
  · exact WuPaper.ClassicalFourthNat.outerPay_2130
  · exact WuPaper.ClassicalFourthNat.outerPay_2131
  · exact WuPaper.ClassicalFourthNat.outerPay_2132
  · exact WuPaper.ClassicalFourthNat.outerPay_2133
  · exact WuPaper.ClassicalFourthNat.outerPay_2134
  · exact WuPaper.ClassicalFourthNat.outerPay_2135
  · exact WuPaper.ClassicalFourthNat.outerPay_2136
  · exact WuPaper.ClassicalFourthNat.outerPay_2137
  · exact WuPaper.ClassicalFourthNat.outerPay_2138
  · exact WuPaper.ClassicalFourthNat.outerPay_2139
  · exact WuPaper.ClassicalFourthNat.outerPay_2140
  · exact WuPaper.ClassicalFourthNat.outerPay_2141
  · exact WuPaper.ClassicalFourthNat.outerPay_2142
  · exact WuPaper.ClassicalFourthNat.outerPay_2143
  · exact WuPaper.ClassicalFourthNat.outerPay_2144
  · exact WuPaper.ClassicalFourthNat.outerPay_2145
  · exact WuPaper.ClassicalFourthNat.outerPay_2146
  · exact WuPaper.ClassicalFourthNat.outerPay_2147
  · exact WuPaper.ClassicalFourthNat.outerPay_2148
  · exact WuPaper.ClassicalFourthNat.outerPay_2149
  · exact WuPaper.ClassicalFourthNat.outerPay_2150
  · exact WuPaper.ClassicalFourthNat.outerPay_2151
  · exact WuPaper.ClassicalFourthNat.outerPay_2152
  · exact WuPaper.ClassicalFourthNat.outerPay_2153
  · exact WuPaper.ClassicalFourthNat.outerPay_2154
  · exact WuPaper.ClassicalFourthNat.outerPay_2155
  · exact WuPaper.ClassicalFourthNat.outerPay_2156
  · exact WuPaper.ClassicalFourthNat.outerPay_2157
  · exact WuPaper.ClassicalFourthNat.outerPay_2158
  · exact WuPaper.ClassicalFourthNat.outerPay_2159
  · exact WuPaper.ClassicalFourthNat.outerPay_2160
  · exact WuPaper.ClassicalFourthNat.outerPay_2161
  · exact WuPaper.ClassicalFourthNat.outerPay_2162
  · exact WuPaper.ClassicalFourthNat.outerPay_2163
  · exact WuPaper.ClassicalFourthNat.outerPay_2164
  · exact WuPaper.ClassicalFourthNat.outerPay_2165
  · exact WuPaper.ClassicalFourthNat.outerPay_2166
  · exact WuPaper.ClassicalFourthNat.outerPay_2167
  · exact WuPaper.ClassicalFourthNat.outerPay_2168
  · exact WuPaper.ClassicalFourthNat.outerPay_2169
  · exact WuPaper.ClassicalFourthNat.outerPay_2170
  · exact WuPaper.ClassicalFourthNat.outerPay_2171
  · exact WuPaper.ClassicalFourthNat.outerPay_2172
  · exact WuPaper.ClassicalFourthNat.outerPay_2173
  · exact WuPaper.ClassicalFourthNat.outerPay_2174
  · exact WuPaper.ClassicalFourthNat.outerPay_2175
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_033
