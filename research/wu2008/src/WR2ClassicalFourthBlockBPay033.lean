import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay033
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_033 (j : Fin 64) (hj : 64*33+j.val < 10540) :
    BPay (64*33+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_2112
  · exact WuPaper.ClassicalFourthNat.BPay_2113
  · exact WuPaper.ClassicalFourthNat.BPay_2114
  · exact WuPaper.ClassicalFourthNat.BPay_2115
  · exact WuPaper.ClassicalFourthNat.BPay_2116
  · exact WuPaper.ClassicalFourthNat.BPay_2117
  · exact WuPaper.ClassicalFourthNat.BPay_2118
  · exact WuPaper.ClassicalFourthNat.BPay_2119
  · exact WuPaper.ClassicalFourthNat.BPay_2120
  · exact WuPaper.ClassicalFourthNat.BPay_2121
  · exact WuPaper.ClassicalFourthNat.BPay_2122
  · exact WuPaper.ClassicalFourthNat.BPay_2123
  · exact WuPaper.ClassicalFourthNat.BPay_2124
  · exact WuPaper.ClassicalFourthNat.BPay_2125
  · exact WuPaper.ClassicalFourthNat.BPay_2126
  · exact WuPaper.ClassicalFourthNat.BPay_2127
  · exact WuPaper.ClassicalFourthNat.BPay_2128
  · exact WuPaper.ClassicalFourthNat.BPay_2129
  · exact WuPaper.ClassicalFourthNat.BPay_2130
  · exact WuPaper.ClassicalFourthNat.BPay_2131
  · exact WuPaper.ClassicalFourthNat.BPay_2132
  · exact WuPaper.ClassicalFourthNat.BPay_2133
  · exact WuPaper.ClassicalFourthNat.BPay_2134
  · exact WuPaper.ClassicalFourthNat.BPay_2135
  · exact WuPaper.ClassicalFourthNat.BPay_2136
  · exact WuPaper.ClassicalFourthNat.BPay_2137
  · exact WuPaper.ClassicalFourthNat.BPay_2138
  · exact WuPaper.ClassicalFourthNat.BPay_2139
  · exact WuPaper.ClassicalFourthNat.BPay_2140
  · exact WuPaper.ClassicalFourthNat.BPay_2141
  · exact WuPaper.ClassicalFourthNat.BPay_2142
  · exact WuPaper.ClassicalFourthNat.BPay_2143
  · exact WuPaper.ClassicalFourthNat.BPay_2144
  · exact WuPaper.ClassicalFourthNat.BPay_2145
  · exact WuPaper.ClassicalFourthNat.BPay_2146
  · exact WuPaper.ClassicalFourthNat.BPay_2147
  · exact WuPaper.ClassicalFourthNat.BPay_2148
  · exact WuPaper.ClassicalFourthNat.BPay_2149
  · exact WuPaper.ClassicalFourthNat.BPay_2150
  · exact WuPaper.ClassicalFourthNat.BPay_2151
  · exact WuPaper.ClassicalFourthNat.BPay_2152
  · exact WuPaper.ClassicalFourthNat.BPay_2153
  · exact WuPaper.ClassicalFourthNat.BPay_2154
  · exact WuPaper.ClassicalFourthNat.BPay_2155
  · exact WuPaper.ClassicalFourthNat.BPay_2156
  · exact WuPaper.ClassicalFourthNat.BPay_2157
  · exact WuPaper.ClassicalFourthNat.BPay_2158
  · exact WuPaper.ClassicalFourthNat.BPay_2159
  · exact WuPaper.ClassicalFourthNat.BPay_2160
  · exact WuPaper.ClassicalFourthNat.BPay_2161
  · exact WuPaper.ClassicalFourthNat.BPay_2162
  · exact WuPaper.ClassicalFourthNat.BPay_2163
  · exact WuPaper.ClassicalFourthNat.BPay_2164
  · exact WuPaper.ClassicalFourthNat.BPay_2165
  · exact WuPaper.ClassicalFourthNat.BPay_2166
  · exact WuPaper.ClassicalFourthNat.BPay_2167
  · exact WuPaper.ClassicalFourthNat.BPay_2168
  · exact WuPaper.ClassicalFourthNat.BPay_2169
  · exact WuPaper.ClassicalFourthNat.BPay_2170
  · exact WuPaper.ClassicalFourthNat.BPay_2171
  · exact WuPaper.ClassicalFourthNat.BPay_2172
  · exact WuPaper.ClassicalFourthNat.BPay_2173
  · exact WuPaper.ClassicalFourthNat.BPay_2174
  · exact WuPaper.ClassicalFourthNat.BPay_2175
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_033
