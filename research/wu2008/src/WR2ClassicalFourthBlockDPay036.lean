import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatDPay036
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem DPay_block_036 (j : Fin 64) (hj : 64*36+j.val < 2540) :
    DPay (64*36+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.DPay_2304
  · exact WuPaper.ClassicalFourthNat.DPay_2305
  · exact WuPaper.ClassicalFourthNat.DPay_2306
  · exact WuPaper.ClassicalFourthNat.DPay_2307
  · exact WuPaper.ClassicalFourthNat.DPay_2308
  · exact WuPaper.ClassicalFourthNat.DPay_2309
  · exact WuPaper.ClassicalFourthNat.DPay_2310
  · exact WuPaper.ClassicalFourthNat.DPay_2311
  · exact WuPaper.ClassicalFourthNat.DPay_2312
  · exact WuPaper.ClassicalFourthNat.DPay_2313
  · exact WuPaper.ClassicalFourthNat.DPay_2314
  · exact WuPaper.ClassicalFourthNat.DPay_2315
  · exact WuPaper.ClassicalFourthNat.DPay_2316
  · exact WuPaper.ClassicalFourthNat.DPay_2317
  · exact WuPaper.ClassicalFourthNat.DPay_2318
  · exact WuPaper.ClassicalFourthNat.DPay_2319
  · exact WuPaper.ClassicalFourthNat.DPay_2320
  · exact WuPaper.ClassicalFourthNat.DPay_2321
  · exact WuPaper.ClassicalFourthNat.DPay_2322
  · exact WuPaper.ClassicalFourthNat.DPay_2323
  · exact WuPaper.ClassicalFourthNat.DPay_2324
  · exact WuPaper.ClassicalFourthNat.DPay_2325
  · exact WuPaper.ClassicalFourthNat.DPay_2326
  · exact WuPaper.ClassicalFourthNat.DPay_2327
  · exact WuPaper.ClassicalFourthNat.DPay_2328
  · exact WuPaper.ClassicalFourthNat.DPay_2329
  · exact WuPaper.ClassicalFourthNat.DPay_2330
  · exact WuPaper.ClassicalFourthNat.DPay_2331
  · exact WuPaper.ClassicalFourthNat.DPay_2332
  · exact WuPaper.ClassicalFourthNat.DPay_2333
  · exact WuPaper.ClassicalFourthNat.DPay_2334
  · exact WuPaper.ClassicalFourthNat.DPay_2335
  · exact WuPaper.ClassicalFourthNat.DPay_2336
  · exact WuPaper.ClassicalFourthNat.DPay_2337
  · exact WuPaper.ClassicalFourthNat.DPay_2338
  · exact WuPaper.ClassicalFourthNat.DPay_2339
  · exact WuPaper.ClassicalFourthNat.DPay_2340
  · exact WuPaper.ClassicalFourthNat.DPay_2341
  · exact WuPaper.ClassicalFourthNat.DPay_2342
  · exact WuPaper.ClassicalFourthNat.DPay_2343
  · exact WuPaper.ClassicalFourthNat.DPay_2344
  · exact WuPaper.ClassicalFourthNat.DPay_2345
  · exact WuPaper.ClassicalFourthNat.DPay_2346
  · exact WuPaper.ClassicalFourthNat.DPay_2347
  · exact WuPaper.ClassicalFourthNat.DPay_2348
  · exact WuPaper.ClassicalFourthNat.DPay_2349
  · exact WuPaper.ClassicalFourthNat.DPay_2350
  · exact WuPaper.ClassicalFourthNat.DPay_2351
  · exact WuPaper.ClassicalFourthNat.DPay_2352
  · exact WuPaper.ClassicalFourthNat.DPay_2353
  · exact WuPaper.ClassicalFourthNat.DPay_2354
  · exact WuPaper.ClassicalFourthNat.DPay_2355
  · exact WuPaper.ClassicalFourthNat.DPay_2356
  · exact WuPaper.ClassicalFourthNat.DPay_2357
  · exact WuPaper.ClassicalFourthNat.DPay_2358
  · exact WuPaper.ClassicalFourthNat.DPay_2359
  · exact WuPaper.ClassicalFourthNat.DPay_2360
  · exact WuPaper.ClassicalFourthNat.DPay_2361
  · exact WuPaper.ClassicalFourthNat.DPay_2362
  · exact WuPaper.ClassicalFourthNat.DPay_2363
  · exact WuPaper.ClassicalFourthNat.DPay_2364
  · exact WuPaper.ClassicalFourthNat.DPay_2365
  · exact WuPaper.ClassicalFourthNat.DPay_2366
  · exact WuPaper.ClassicalFourthNat.DPay_2367
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.DPay_block_036
