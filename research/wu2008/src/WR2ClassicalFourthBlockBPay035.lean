import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay035
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_035 (j : Fin 64) (hj : 64*35+j.val < 10540) :
    BPay (64*35+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_2240
  · exact WuPaper.ClassicalFourthNat.BPay_2241
  · exact WuPaper.ClassicalFourthNat.BPay_2242
  · exact WuPaper.ClassicalFourthNat.BPay_2243
  · exact WuPaper.ClassicalFourthNat.BPay_2244
  · exact WuPaper.ClassicalFourthNat.BPay_2245
  · exact WuPaper.ClassicalFourthNat.BPay_2246
  · exact WuPaper.ClassicalFourthNat.BPay_2247
  · exact WuPaper.ClassicalFourthNat.BPay_2248
  · exact WuPaper.ClassicalFourthNat.BPay_2249
  · exact WuPaper.ClassicalFourthNat.BPay_2250
  · exact WuPaper.ClassicalFourthNat.BPay_2251
  · exact WuPaper.ClassicalFourthNat.BPay_2252
  · exact WuPaper.ClassicalFourthNat.BPay_2253
  · exact WuPaper.ClassicalFourthNat.BPay_2254
  · exact WuPaper.ClassicalFourthNat.BPay_2255
  · exact WuPaper.ClassicalFourthNat.BPay_2256
  · exact WuPaper.ClassicalFourthNat.BPay_2257
  · exact WuPaper.ClassicalFourthNat.BPay_2258
  · exact WuPaper.ClassicalFourthNat.BPay_2259
  · exact WuPaper.ClassicalFourthNat.BPay_2260
  · exact WuPaper.ClassicalFourthNat.BPay_2261
  · exact WuPaper.ClassicalFourthNat.BPay_2262
  · exact WuPaper.ClassicalFourthNat.BPay_2263
  · exact WuPaper.ClassicalFourthNat.BPay_2264
  · exact WuPaper.ClassicalFourthNat.BPay_2265
  · exact WuPaper.ClassicalFourthNat.BPay_2266
  · exact WuPaper.ClassicalFourthNat.BPay_2267
  · exact WuPaper.ClassicalFourthNat.BPay_2268
  · exact WuPaper.ClassicalFourthNat.BPay_2269
  · exact WuPaper.ClassicalFourthNat.BPay_2270
  · exact WuPaper.ClassicalFourthNat.BPay_2271
  · exact WuPaper.ClassicalFourthNat.BPay_2272
  · exact WuPaper.ClassicalFourthNat.BPay_2273
  · exact WuPaper.ClassicalFourthNat.BPay_2274
  · exact WuPaper.ClassicalFourthNat.BPay_2275
  · exact WuPaper.ClassicalFourthNat.BPay_2276
  · exact WuPaper.ClassicalFourthNat.BPay_2277
  · exact WuPaper.ClassicalFourthNat.BPay_2278
  · exact WuPaper.ClassicalFourthNat.BPay_2279
  · exact WuPaper.ClassicalFourthNat.BPay_2280
  · exact WuPaper.ClassicalFourthNat.BPay_2281
  · exact WuPaper.ClassicalFourthNat.BPay_2282
  · exact WuPaper.ClassicalFourthNat.BPay_2283
  · exact WuPaper.ClassicalFourthNat.BPay_2284
  · exact WuPaper.ClassicalFourthNat.BPay_2285
  · exact WuPaper.ClassicalFourthNat.BPay_2286
  · exact WuPaper.ClassicalFourthNat.BPay_2287
  · exact WuPaper.ClassicalFourthNat.BPay_2288
  · exact WuPaper.ClassicalFourthNat.BPay_2289
  · exact WuPaper.ClassicalFourthNat.BPay_2290
  · exact WuPaper.ClassicalFourthNat.BPay_2291
  · exact WuPaper.ClassicalFourthNat.BPay_2292
  · exact WuPaper.ClassicalFourthNat.BPay_2293
  · exact WuPaper.ClassicalFourthNat.BPay_2294
  · exact WuPaper.ClassicalFourthNat.BPay_2295
  · exact WuPaper.ClassicalFourthNat.BPay_2296
  · exact WuPaper.ClassicalFourthNat.BPay_2297
  · exact WuPaper.ClassicalFourthNat.BPay_2298
  · exact WuPaper.ClassicalFourthNat.BPay_2299
  · exact WuPaper.ClassicalFourthNat.BPay_2300
  · exact WuPaper.ClassicalFourthNat.BPay_2301
  · exact WuPaper.ClassicalFourthNat.BPay_2302
  · exact WuPaper.ClassicalFourthNat.BPay_2303
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_035
