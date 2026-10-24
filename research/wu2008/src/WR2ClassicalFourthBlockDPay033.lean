import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay033
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_033 (j : Fin 64) (hj : 64*33+j.val < 2540) :
    DPay (64*33+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_2112
  · exact WuPaper.ClassicalFourthNat.DPay_2113
  · exact WuPaper.ClassicalFourthNat.DPay_2114
  · exact WuPaper.ClassicalFourthNat.DPay_2115
  · exact WuPaper.ClassicalFourthNat.DPay_2116
  · exact WuPaper.ClassicalFourthNat.DPay_2117
  · exact WuPaper.ClassicalFourthNat.DPay_2118
  · exact WuPaper.ClassicalFourthNat.DPay_2119
  · exact WuPaper.ClassicalFourthNat.DPay_2120
  · exact WuPaper.ClassicalFourthNat.DPay_2121
  · exact WuPaper.ClassicalFourthNat.DPay_2122
  · exact WuPaper.ClassicalFourthNat.DPay_2123
  · exact WuPaper.ClassicalFourthNat.DPay_2124
  · exact WuPaper.ClassicalFourthNat.DPay_2125
  · exact WuPaper.ClassicalFourthNat.DPay_2126
  · exact WuPaper.ClassicalFourthNat.DPay_2127
  · exact WuPaper.ClassicalFourthNat.DPay_2128
  · exact WuPaper.ClassicalFourthNat.DPay_2129
  · exact WuPaper.ClassicalFourthNat.DPay_2130
  · exact WuPaper.ClassicalFourthNat.DPay_2131
  · exact WuPaper.ClassicalFourthNat.DPay_2132
  · exact WuPaper.ClassicalFourthNat.DPay_2133
  · exact WuPaper.ClassicalFourthNat.DPay_2134
  · exact WuPaper.ClassicalFourthNat.DPay_2135
  · exact WuPaper.ClassicalFourthNat.DPay_2136
  · exact WuPaper.ClassicalFourthNat.DPay_2137
  · exact WuPaper.ClassicalFourthNat.DPay_2138
  · exact WuPaper.ClassicalFourthNat.DPay_2139
  · exact WuPaper.ClassicalFourthNat.DPay_2140
  · exact WuPaper.ClassicalFourthNat.DPay_2141
  · exact WuPaper.ClassicalFourthNat.DPay_2142
  · exact WuPaper.ClassicalFourthNat.DPay_2143
  · exact WuPaper.ClassicalFourthNat.DPay_2144
  · exact WuPaper.ClassicalFourthNat.DPay_2145
  · exact WuPaper.ClassicalFourthNat.DPay_2146
  · exact WuPaper.ClassicalFourthNat.DPay_2147
  · exact WuPaper.ClassicalFourthNat.DPay_2148
  · exact WuPaper.ClassicalFourthNat.DPay_2149
  · exact WuPaper.ClassicalFourthNat.DPay_2150
  · exact WuPaper.ClassicalFourthNat.DPay_2151
  · exact WuPaper.ClassicalFourthNat.DPay_2152
  · exact WuPaper.ClassicalFourthNat.DPay_2153
  · exact WuPaper.ClassicalFourthNat.DPay_2154
  · exact WuPaper.ClassicalFourthNat.DPay_2155
  · exact WuPaper.ClassicalFourthNat.DPay_2156
  · exact WuPaper.ClassicalFourthNat.DPay_2157
  · exact WuPaper.ClassicalFourthNat.DPay_2158
  · exact WuPaper.ClassicalFourthNat.DPay_2159
  · exact WuPaper.ClassicalFourthNat.DPay_2160
  · exact WuPaper.ClassicalFourthNat.DPay_2161
  · exact WuPaper.ClassicalFourthNat.DPay_2162
  · exact WuPaper.ClassicalFourthNat.DPay_2163
  · exact WuPaper.ClassicalFourthNat.DPay_2164
  · exact WuPaper.ClassicalFourthNat.DPay_2165
  · exact WuPaper.ClassicalFourthNat.DPay_2166
  · exact WuPaper.ClassicalFourthNat.DPay_2167
  · exact WuPaper.ClassicalFourthNat.DPay_2168
  · exact WuPaper.ClassicalFourthNat.DPay_2169
  · exact WuPaper.ClassicalFourthNat.DPay_2170
  · exact WuPaper.ClassicalFourthNat.DPay_2171
  · exact WuPaper.ClassicalFourthNat.DPay_2172
  · exact WuPaper.ClassicalFourthNat.DPay_2173
  · exact WuPaper.ClassicalFourthNat.DPay_2174
  · exact WuPaper.ClassicalFourthNat.DPay_2175
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_033
