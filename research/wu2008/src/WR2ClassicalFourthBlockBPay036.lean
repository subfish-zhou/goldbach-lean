import WR2ClassicalFourthConditions
import WR2ClassicalFourthNatBPay036
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem BPay_block_036 (j : Fin 64) (hj : 64*36+j.val < 10540) :
    BPay (64*36+j.val) := by
  fin_cases j
  · exact WuPaper.ClassicalFourthNat.BPay_2304
  · exact WuPaper.ClassicalFourthNat.BPay_2305
  · exact WuPaper.ClassicalFourthNat.BPay_2306
  · exact WuPaper.ClassicalFourthNat.BPay_2307
  · exact WuPaper.ClassicalFourthNat.BPay_2308
  · exact WuPaper.ClassicalFourthNat.BPay_2309
  · exact WuPaper.ClassicalFourthNat.BPay_2310
  · exact WuPaper.ClassicalFourthNat.BPay_2311
  · exact WuPaper.ClassicalFourthNat.BPay_2312
  · exact WuPaper.ClassicalFourthNat.BPay_2313
  · exact WuPaper.ClassicalFourthNat.BPay_2314
  · exact WuPaper.ClassicalFourthNat.BPay_2315
  · exact WuPaper.ClassicalFourthNat.BPay_2316
  · exact WuPaper.ClassicalFourthNat.BPay_2317
  · exact WuPaper.ClassicalFourthNat.BPay_2318
  · exact WuPaper.ClassicalFourthNat.BPay_2319
  · exact WuPaper.ClassicalFourthNat.BPay_2320
  · exact WuPaper.ClassicalFourthNat.BPay_2321
  · exact WuPaper.ClassicalFourthNat.BPay_2322
  · exact WuPaper.ClassicalFourthNat.BPay_2323
  · exact WuPaper.ClassicalFourthNat.BPay_2324
  · exact WuPaper.ClassicalFourthNat.BPay_2325
  · exact WuPaper.ClassicalFourthNat.BPay_2326
  · exact WuPaper.ClassicalFourthNat.BPay_2327
  · exact WuPaper.ClassicalFourthNat.BPay_2328
  · exact WuPaper.ClassicalFourthNat.BPay_2329
  · exact WuPaper.ClassicalFourthNat.BPay_2330
  · exact WuPaper.ClassicalFourthNat.BPay_2331
  · exact WuPaper.ClassicalFourthNat.BPay_2332
  · exact WuPaper.ClassicalFourthNat.BPay_2333
  · exact WuPaper.ClassicalFourthNat.BPay_2334
  · exact WuPaper.ClassicalFourthNat.BPay_2335
  · exact WuPaper.ClassicalFourthNat.BPay_2336
  · exact WuPaper.ClassicalFourthNat.BPay_2337
  · exact WuPaper.ClassicalFourthNat.BPay_2338
  · exact WuPaper.ClassicalFourthNat.BPay_2339
  · exact WuPaper.ClassicalFourthNat.BPay_2340
  · exact WuPaper.ClassicalFourthNat.BPay_2341
  · exact WuPaper.ClassicalFourthNat.BPay_2342
  · exact WuPaper.ClassicalFourthNat.BPay_2343
  · exact WuPaper.ClassicalFourthNat.BPay_2344
  · exact WuPaper.ClassicalFourthNat.BPay_2345
  · exact WuPaper.ClassicalFourthNat.BPay_2346
  · exact WuPaper.ClassicalFourthNat.BPay_2347
  · exact WuPaper.ClassicalFourthNat.BPay_2348
  · exact WuPaper.ClassicalFourthNat.BPay_2349
  · exact WuPaper.ClassicalFourthNat.BPay_2350
  · exact WuPaper.ClassicalFourthNat.BPay_2351
  · exact WuPaper.ClassicalFourthNat.BPay_2352
  · exact WuPaper.ClassicalFourthNat.BPay_2353
  · exact WuPaper.ClassicalFourthNat.BPay_2354
  · exact WuPaper.ClassicalFourthNat.BPay_2355
  · exact WuPaper.ClassicalFourthNat.BPay_2356
  · exact WuPaper.ClassicalFourthNat.BPay_2357
  · exact WuPaper.ClassicalFourthNat.BPay_2358
  · exact WuPaper.ClassicalFourthNat.BPay_2359
  · exact WuPaper.ClassicalFourthNat.BPay_2360
  · exact WuPaper.ClassicalFourthNat.BPay_2361
  · exact WuPaper.ClassicalFourthNat.BPay_2362
  · exact WuPaper.ClassicalFourthNat.BPay_2363
  · exact WuPaper.ClassicalFourthNat.BPay_2364
  · exact WuPaper.ClassicalFourthNat.BPay_2365
  · exact WuPaper.ClassicalFourthNat.BPay_2366
  · exact WuPaper.ClassicalFourthNat.BPay_2367
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.BPay_block_036
