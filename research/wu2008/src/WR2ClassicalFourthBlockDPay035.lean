import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay035
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_035 (j : Fin 64) (hj : 64*35+j.val < 2540) :
    DPay (64*35+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_2240
  · exact WuPaper.ClassicalFourthNat.DPay_2241
  · exact WuPaper.ClassicalFourthNat.DPay_2242
  · exact WuPaper.ClassicalFourthNat.DPay_2243
  · exact WuPaper.ClassicalFourthNat.DPay_2244
  · exact WuPaper.ClassicalFourthNat.DPay_2245
  · exact WuPaper.ClassicalFourthNat.DPay_2246
  · exact WuPaper.ClassicalFourthNat.DPay_2247
  · exact WuPaper.ClassicalFourthNat.DPay_2248
  · exact WuPaper.ClassicalFourthNat.DPay_2249
  · exact WuPaper.ClassicalFourthNat.DPay_2250
  · exact WuPaper.ClassicalFourthNat.DPay_2251
  · exact WuPaper.ClassicalFourthNat.DPay_2252
  · exact WuPaper.ClassicalFourthNat.DPay_2253
  · exact WuPaper.ClassicalFourthNat.DPay_2254
  · exact WuPaper.ClassicalFourthNat.DPay_2255
  · exact WuPaper.ClassicalFourthNat.DPay_2256
  · exact WuPaper.ClassicalFourthNat.DPay_2257
  · exact WuPaper.ClassicalFourthNat.DPay_2258
  · exact WuPaper.ClassicalFourthNat.DPay_2259
  · exact WuPaper.ClassicalFourthNat.DPay_2260
  · exact WuPaper.ClassicalFourthNat.DPay_2261
  · exact WuPaper.ClassicalFourthNat.DPay_2262
  · exact WuPaper.ClassicalFourthNat.DPay_2263
  · exact WuPaper.ClassicalFourthNat.DPay_2264
  · exact WuPaper.ClassicalFourthNat.DPay_2265
  · exact WuPaper.ClassicalFourthNat.DPay_2266
  · exact WuPaper.ClassicalFourthNat.DPay_2267
  · exact WuPaper.ClassicalFourthNat.DPay_2268
  · exact WuPaper.ClassicalFourthNat.DPay_2269
  · exact WuPaper.ClassicalFourthNat.DPay_2270
  · exact WuPaper.ClassicalFourthNat.DPay_2271
  · exact WuPaper.ClassicalFourthNat.DPay_2272
  · exact WuPaper.ClassicalFourthNat.DPay_2273
  · exact WuPaper.ClassicalFourthNat.DPay_2274
  · exact WuPaper.ClassicalFourthNat.DPay_2275
  · exact WuPaper.ClassicalFourthNat.DPay_2276
  · exact WuPaper.ClassicalFourthNat.DPay_2277
  · exact WuPaper.ClassicalFourthNat.DPay_2278
  · exact WuPaper.ClassicalFourthNat.DPay_2279
  · exact WuPaper.ClassicalFourthNat.DPay_2280
  · exact WuPaper.ClassicalFourthNat.DPay_2281
  · exact WuPaper.ClassicalFourthNat.DPay_2282
  · exact WuPaper.ClassicalFourthNat.DPay_2283
  · exact WuPaper.ClassicalFourthNat.DPay_2284
  · exact WuPaper.ClassicalFourthNat.DPay_2285
  · exact WuPaper.ClassicalFourthNat.DPay_2286
  · exact WuPaper.ClassicalFourthNat.DPay_2287
  · exact WuPaper.ClassicalFourthNat.DPay_2288
  · exact WuPaper.ClassicalFourthNat.DPay_2289
  · exact WuPaper.ClassicalFourthNat.DPay_2290
  · exact WuPaper.ClassicalFourthNat.DPay_2291
  · exact WuPaper.ClassicalFourthNat.DPay_2292
  · exact WuPaper.ClassicalFourthNat.DPay_2293
  · exact WuPaper.ClassicalFourthNat.DPay_2294
  · exact WuPaper.ClassicalFourthNat.DPay_2295
  · exact WuPaper.ClassicalFourthNat.DPay_2296
  · exact WuPaper.ClassicalFourthNat.DPay_2297
  · exact WuPaper.ClassicalFourthNat.DPay_2298
  · exact WuPaper.ClassicalFourthNat.DPay_2299
  · exact WuPaper.ClassicalFourthNat.DPay_2300
  · exact WuPaper.ClassicalFourthNat.DPay_2301
  · exact WuPaper.ClassicalFourthNat.DPay_2302
  · exact WuPaper.ClassicalFourthNat.DPay_2303
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_035
