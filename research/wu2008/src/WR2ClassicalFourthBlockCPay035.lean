import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatCPay035
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem CPay_block_035 (j : Fin 64) (hj : 64*35+j.val < 2540) :
    CPay (64*35+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.CPay_2240
  · exact WuPaper.ClassicalFourthNat.CPay_2241
  · exact WuPaper.ClassicalFourthNat.CPay_2242
  · exact WuPaper.ClassicalFourthNat.CPay_2243
  · exact WuPaper.ClassicalFourthNat.CPay_2244
  · exact WuPaper.ClassicalFourthNat.CPay_2245
  · exact WuPaper.ClassicalFourthNat.CPay_2246
  · exact WuPaper.ClassicalFourthNat.CPay_2247
  · exact WuPaper.ClassicalFourthNat.CPay_2248
  · exact WuPaper.ClassicalFourthNat.CPay_2249
  · exact WuPaper.ClassicalFourthNat.CPay_2250
  · exact WuPaper.ClassicalFourthNat.CPay_2251
  · exact WuPaper.ClassicalFourthNat.CPay_2252
  · exact WuPaper.ClassicalFourthNat.CPay_2253
  · exact WuPaper.ClassicalFourthNat.CPay_2254
  · exact WuPaper.ClassicalFourthNat.CPay_2255
  · exact WuPaper.ClassicalFourthNat.CPay_2256
  · exact WuPaper.ClassicalFourthNat.CPay_2257
  · exact WuPaper.ClassicalFourthNat.CPay_2258
  · exact WuPaper.ClassicalFourthNat.CPay_2259
  · exact WuPaper.ClassicalFourthNat.CPay_2260
  · exact WuPaper.ClassicalFourthNat.CPay_2261
  · exact WuPaper.ClassicalFourthNat.CPay_2262
  · exact WuPaper.ClassicalFourthNat.CPay_2263
  · exact WuPaper.ClassicalFourthNat.CPay_2264
  · exact WuPaper.ClassicalFourthNat.CPay_2265
  · exact WuPaper.ClassicalFourthNat.CPay_2266
  · exact WuPaper.ClassicalFourthNat.CPay_2267
  · exact WuPaper.ClassicalFourthNat.CPay_2268
  · exact WuPaper.ClassicalFourthNat.CPay_2269
  · exact WuPaper.ClassicalFourthNat.CPay_2270
  · exact WuPaper.ClassicalFourthNat.CPay_2271
  · exact WuPaper.ClassicalFourthNat.CPay_2272
  · exact WuPaper.ClassicalFourthNat.CPay_2273
  · exact WuPaper.ClassicalFourthNat.CPay_2274
  · exact WuPaper.ClassicalFourthNat.CPay_2275
  · exact WuPaper.ClassicalFourthNat.CPay_2276
  · exact WuPaper.ClassicalFourthNat.CPay_2277
  · exact WuPaper.ClassicalFourthNat.CPay_2278
  · exact WuPaper.ClassicalFourthNat.CPay_2279
  · exact WuPaper.ClassicalFourthNat.CPay_2280
  · exact WuPaper.ClassicalFourthNat.CPay_2281
  · exact WuPaper.ClassicalFourthNat.CPay_2282
  · exact WuPaper.ClassicalFourthNat.CPay_2283
  · exact WuPaper.ClassicalFourthNat.CPay_2284
  · exact WuPaper.ClassicalFourthNat.CPay_2285
  · exact WuPaper.ClassicalFourthNat.CPay_2286
  · exact WuPaper.ClassicalFourthNat.CPay_2287
  · exact WuPaper.ClassicalFourthNat.CPay_2288
  · exact WuPaper.ClassicalFourthNat.CPay_2289
  · exact WuPaper.ClassicalFourthNat.CPay_2290
  · exact WuPaper.ClassicalFourthNat.CPay_2291
  · exact WuPaper.ClassicalFourthNat.CPay_2292
  · exact WuPaper.ClassicalFourthNat.CPay_2293
  · exact WuPaper.ClassicalFourthNat.CPay_2294
  · exact WuPaper.ClassicalFourthNat.CPay_2295
  · exact WuPaper.ClassicalFourthNat.CPay_2296
  · exact WuPaper.ClassicalFourthNat.CPay_2297
  · exact WuPaper.ClassicalFourthNat.CPay_2298
  · exact WuPaper.ClassicalFourthNat.CPay_2299
  · exact WuPaper.ClassicalFourthNat.CPay_2300
  · exact WuPaper.ClassicalFourthNat.CPay_2301
  · exact WuPaper.ClassicalFourthNat.CPay_2302
  · exact WuPaper.ClassicalFourthNat.CPay_2303
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.CPay_block_035
