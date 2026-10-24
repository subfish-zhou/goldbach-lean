import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay034
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_034 (j : Fin 64) (hj : 64*34+j.val < 2540) :
    CPay (64*34+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_2176
  · exact WuPaper.ClassicalFourthNat.CPay_2177
  · exact WuPaper.ClassicalFourthNat.CPay_2178
  · exact WuPaper.ClassicalFourthNat.CPay_2179
  · exact WuPaper.ClassicalFourthNat.CPay_2180
  · exact WuPaper.ClassicalFourthNat.CPay_2181
  · exact WuPaper.ClassicalFourthNat.CPay_2182
  · exact WuPaper.ClassicalFourthNat.CPay_2183
  · exact WuPaper.ClassicalFourthNat.CPay_2184
  · exact WuPaper.ClassicalFourthNat.CPay_2185
  · exact WuPaper.ClassicalFourthNat.CPay_2186
  · exact WuPaper.ClassicalFourthNat.CPay_2187
  · exact WuPaper.ClassicalFourthNat.CPay_2188
  · exact WuPaper.ClassicalFourthNat.CPay_2189
  · exact WuPaper.ClassicalFourthNat.CPay_2190
  · exact WuPaper.ClassicalFourthNat.CPay_2191
  · exact WuPaper.ClassicalFourthNat.CPay_2192
  · exact WuPaper.ClassicalFourthNat.CPay_2193
  · exact WuPaper.ClassicalFourthNat.CPay_2194
  · exact WuPaper.ClassicalFourthNat.CPay_2195
  · exact WuPaper.ClassicalFourthNat.CPay_2196
  · exact WuPaper.ClassicalFourthNat.CPay_2197
  · exact WuPaper.ClassicalFourthNat.CPay_2198
  · exact WuPaper.ClassicalFourthNat.CPay_2199
  · exact WuPaper.ClassicalFourthNat.CPay_2200
  · exact WuPaper.ClassicalFourthNat.CPay_2201
  · exact WuPaper.ClassicalFourthNat.CPay_2202
  · exact WuPaper.ClassicalFourthNat.CPay_2203
  · exact WuPaper.ClassicalFourthNat.CPay_2204
  · exact WuPaper.ClassicalFourthNat.CPay_2205
  · exact WuPaper.ClassicalFourthNat.CPay_2206
  · exact WuPaper.ClassicalFourthNat.CPay_2207
  · exact WuPaper.ClassicalFourthNat.CPay_2208
  · exact WuPaper.ClassicalFourthNat.CPay_2209
  · exact WuPaper.ClassicalFourthNat.CPay_2210
  · exact WuPaper.ClassicalFourthNat.CPay_2211
  · exact WuPaper.ClassicalFourthNat.CPay_2212
  · exact WuPaper.ClassicalFourthNat.CPay_2213
  · exact WuPaper.ClassicalFourthNat.CPay_2214
  · exact WuPaper.ClassicalFourthNat.CPay_2215
  · exact WuPaper.ClassicalFourthNat.CPay_2216
  · exact WuPaper.ClassicalFourthNat.CPay_2217
  · exact WuPaper.ClassicalFourthNat.CPay_2218
  · exact WuPaper.ClassicalFourthNat.CPay_2219
  · exact WuPaper.ClassicalFourthNat.CPay_2220
  · exact WuPaper.ClassicalFourthNat.CPay_2221
  · exact WuPaper.ClassicalFourthNat.CPay_2222
  · exact WuPaper.ClassicalFourthNat.CPay_2223
  · exact WuPaper.ClassicalFourthNat.CPay_2224
  · exact WuPaper.ClassicalFourthNat.CPay_2225
  · exact WuPaper.ClassicalFourthNat.CPay_2226
  · exact WuPaper.ClassicalFourthNat.CPay_2227
  · exact WuPaper.ClassicalFourthNat.CPay_2228
  · exact WuPaper.ClassicalFourthNat.CPay_2229
  · exact WuPaper.ClassicalFourthNat.CPay_2230
  · exact WuPaper.ClassicalFourthNat.CPay_2231
  · exact WuPaper.ClassicalFourthNat.CPay_2232
  · exact WuPaper.ClassicalFourthNat.CPay_2233
  · exact WuPaper.ClassicalFourthNat.CPay_2234
  · exact WuPaper.ClassicalFourthNat.CPay_2235
  · exact WuPaper.ClassicalFourthNat.CPay_2236
  · exact WuPaper.ClassicalFourthNat.CPay_2237
  · exact WuPaper.ClassicalFourthNat.CPay_2238
  · exact WuPaper.ClassicalFourthNat.CPay_2239
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_034
