import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatouterPay035
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem outerPay_block_035 (j : Fin 64) (hj : 64*35+j.val < 10540) :
    OuterPay (64*35+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.outerPay_2240
  · exact WuPaper.ClassicalFourthNat.outerPay_2241
  · exact WuPaper.ClassicalFourthNat.outerPay_2242
  · exact WuPaper.ClassicalFourthNat.outerPay_2243
  · exact WuPaper.ClassicalFourthNat.outerPay_2244
  · exact WuPaper.ClassicalFourthNat.outerPay_2245
  · exact WuPaper.ClassicalFourthNat.outerPay_2246
  · exact WuPaper.ClassicalFourthNat.outerPay_2247
  · exact WuPaper.ClassicalFourthNat.outerPay_2248
  · exact WuPaper.ClassicalFourthNat.outerPay_2249
  · exact WuPaper.ClassicalFourthNat.outerPay_2250
  · exact WuPaper.ClassicalFourthNat.outerPay_2251
  · exact WuPaper.ClassicalFourthNat.outerPay_2252
  · exact WuPaper.ClassicalFourthNat.outerPay_2253
  · exact WuPaper.ClassicalFourthNat.outerPay_2254
  · exact WuPaper.ClassicalFourthNat.outerPay_2255
  · exact WuPaper.ClassicalFourthNat.outerPay_2256
  · exact WuPaper.ClassicalFourthNat.outerPay_2257
  · exact WuPaper.ClassicalFourthNat.outerPay_2258
  · exact WuPaper.ClassicalFourthNat.outerPay_2259
  · exact WuPaper.ClassicalFourthNat.outerPay_2260
  · exact WuPaper.ClassicalFourthNat.outerPay_2261
  · exact WuPaper.ClassicalFourthNat.outerPay_2262
  · exact WuPaper.ClassicalFourthNat.outerPay_2263
  · exact WuPaper.ClassicalFourthNat.outerPay_2264
  · exact WuPaper.ClassicalFourthNat.outerPay_2265
  · exact WuPaper.ClassicalFourthNat.outerPay_2266
  · exact WuPaper.ClassicalFourthNat.outerPay_2267
  · exact WuPaper.ClassicalFourthNat.outerPay_2268
  · exact WuPaper.ClassicalFourthNat.outerPay_2269
  · exact WuPaper.ClassicalFourthNat.outerPay_2270
  · exact WuPaper.ClassicalFourthNat.outerPay_2271
  · exact WuPaper.ClassicalFourthNat.outerPay_2272
  · exact WuPaper.ClassicalFourthNat.outerPay_2273
  · exact WuPaper.ClassicalFourthNat.outerPay_2274
  · exact WuPaper.ClassicalFourthNat.outerPay_2275
  · exact WuPaper.ClassicalFourthNat.outerPay_2276
  · exact WuPaper.ClassicalFourthNat.outerPay_2277
  · exact WuPaper.ClassicalFourthNat.outerPay_2278
  · exact WuPaper.ClassicalFourthNat.outerPay_2279
  · exact WuPaper.ClassicalFourthNat.outerPay_2280
  · exact WuPaper.ClassicalFourthNat.outerPay_2281
  · exact WuPaper.ClassicalFourthNat.outerPay_2282
  · exact WuPaper.ClassicalFourthNat.outerPay_2283
  · exact WuPaper.ClassicalFourthNat.outerPay_2284
  · exact WuPaper.ClassicalFourthNat.outerPay_2285
  · exact WuPaper.ClassicalFourthNat.outerPay_2286
  · exact WuPaper.ClassicalFourthNat.outerPay_2287
  · exact WuPaper.ClassicalFourthNat.outerPay_2288
  · exact WuPaper.ClassicalFourthNat.outerPay_2289
  · exact WuPaper.ClassicalFourthNat.outerPay_2290
  · exact WuPaper.ClassicalFourthNat.outerPay_2291
  · exact WuPaper.ClassicalFourthNat.outerPay_2292
  · exact WuPaper.ClassicalFourthNat.outerPay_2293
  · exact WuPaper.ClassicalFourthNat.outerPay_2294
  · exact WuPaper.ClassicalFourthNat.outerPay_2295
  · exact WuPaper.ClassicalFourthNat.outerPay_2296
  · exact WuPaper.ClassicalFourthNat.outerPay_2297
  · exact WuPaper.ClassicalFourthNat.outerPay_2298
  · exact WuPaper.ClassicalFourthNat.outerPay_2299
  · exact WuPaper.ClassicalFourthNat.outerPay_2300
  · exact WuPaper.ClassicalFourthNat.outerPay_2301
  · exact WuPaper.ClassicalFourthNat.outerPay_2302
  · exact WuPaper.ClassicalFourthNat.outerPay_2303
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.outerPay_block_035
