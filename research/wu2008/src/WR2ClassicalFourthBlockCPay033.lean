import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay033
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_033 (j : Fin 64) (hj : 64*33+j.val < 2540) :
    CPay (64*33+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_2112
  · exact WuPaper.ClassicalFourthNat.CPay_2113
  · exact WuPaper.ClassicalFourthNat.CPay_2114
  · exact WuPaper.ClassicalFourthNat.CPay_2115
  · exact WuPaper.ClassicalFourthNat.CPay_2116
  · exact WuPaper.ClassicalFourthNat.CPay_2117
  · exact WuPaper.ClassicalFourthNat.CPay_2118
  · exact WuPaper.ClassicalFourthNat.CPay_2119
  · exact WuPaper.ClassicalFourthNat.CPay_2120
  · exact WuPaper.ClassicalFourthNat.CPay_2121
  · exact WuPaper.ClassicalFourthNat.CPay_2122
  · exact WuPaper.ClassicalFourthNat.CPay_2123
  · exact WuPaper.ClassicalFourthNat.CPay_2124
  · exact WuPaper.ClassicalFourthNat.CPay_2125
  · exact WuPaper.ClassicalFourthNat.CPay_2126
  · exact WuPaper.ClassicalFourthNat.CPay_2127
  · exact WuPaper.ClassicalFourthNat.CPay_2128
  · exact WuPaper.ClassicalFourthNat.CPay_2129
  · exact WuPaper.ClassicalFourthNat.CPay_2130
  · exact WuPaper.ClassicalFourthNat.CPay_2131
  · exact WuPaper.ClassicalFourthNat.CPay_2132
  · exact WuPaper.ClassicalFourthNat.CPay_2133
  · exact WuPaper.ClassicalFourthNat.CPay_2134
  · exact WuPaper.ClassicalFourthNat.CPay_2135
  · exact WuPaper.ClassicalFourthNat.CPay_2136
  · exact WuPaper.ClassicalFourthNat.CPay_2137
  · exact WuPaper.ClassicalFourthNat.CPay_2138
  · exact WuPaper.ClassicalFourthNat.CPay_2139
  · exact WuPaper.ClassicalFourthNat.CPay_2140
  · exact WuPaper.ClassicalFourthNat.CPay_2141
  · exact WuPaper.ClassicalFourthNat.CPay_2142
  · exact WuPaper.ClassicalFourthNat.CPay_2143
  · exact WuPaper.ClassicalFourthNat.CPay_2144
  · exact WuPaper.ClassicalFourthNat.CPay_2145
  · exact WuPaper.ClassicalFourthNat.CPay_2146
  · exact WuPaper.ClassicalFourthNat.CPay_2147
  · exact WuPaper.ClassicalFourthNat.CPay_2148
  · exact WuPaper.ClassicalFourthNat.CPay_2149
  · exact WuPaper.ClassicalFourthNat.CPay_2150
  · exact WuPaper.ClassicalFourthNat.CPay_2151
  · exact WuPaper.ClassicalFourthNat.CPay_2152
  · exact WuPaper.ClassicalFourthNat.CPay_2153
  · exact WuPaper.ClassicalFourthNat.CPay_2154
  · exact WuPaper.ClassicalFourthNat.CPay_2155
  · exact WuPaper.ClassicalFourthNat.CPay_2156
  · exact WuPaper.ClassicalFourthNat.CPay_2157
  · exact WuPaper.ClassicalFourthNat.CPay_2158
  · exact WuPaper.ClassicalFourthNat.CPay_2159
  · exact WuPaper.ClassicalFourthNat.CPay_2160
  · exact WuPaper.ClassicalFourthNat.CPay_2161
  · exact WuPaper.ClassicalFourthNat.CPay_2162
  · exact WuPaper.ClassicalFourthNat.CPay_2163
  · exact WuPaper.ClassicalFourthNat.CPay_2164
  · exact WuPaper.ClassicalFourthNat.CPay_2165
  · exact WuPaper.ClassicalFourthNat.CPay_2166
  · exact WuPaper.ClassicalFourthNat.CPay_2167
  · exact WuPaper.ClassicalFourthNat.CPay_2168
  · exact WuPaper.ClassicalFourthNat.CPay_2169
  · exact WuPaper.ClassicalFourthNat.CPay_2170
  · exact WuPaper.ClassicalFourthNat.CPay_2171
  · exact WuPaper.ClassicalFourthNat.CPay_2172
  · exact WuPaper.ClassicalFourthNat.CPay_2173
  · exact WuPaper.ClassicalFourthNat.CPay_2174
  · exact WuPaper.ClassicalFourthNat.CPay_2175
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_033
